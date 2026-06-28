// Lean compiler output
// Module: Lean.Meta.Constructions.CasesOn
// Imports: Init.Data.Range.Basic Lean.Meta.Basic Lean.AddDecl
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_range, l_List_reverse___redArg};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Range::Basic::{
    initialize_Init_Data_Range_Basic, runtime_initialize_Init_Data_Range_Basic,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_replaceRef, l_List_lengthTR___redArg,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Float::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate1;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_apply_7, lean_apply_8, lean_box, lean_box_float, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_float, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__2_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__3_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 114, 114, 111, 114, 32, 105, 110, 32, 39, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__5_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [39, 32, 103, 101, 110, 101, 114, 97, 116, 105, 111, 110, 44, 32, 39, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__7_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [39, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__3_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [76, 101, 97, 110, 46, 105, 115, 82, 101, 99, 63, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__3_value) as *mut LeanObject;
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__4_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__4_value) as *mut LeanObject;
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [80, 85, 110, 105, 116, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__0_value) as *mut LeanObject,11091137386503903511 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 110, 105, 116, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__2_value
) as *mut LeanObject;
static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__0_value) as *mut LeanObject,11091137386503903511 as *mut LeanObject] };
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__2_value) as *mut LeanObject,14036392901208071058 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__3_value
) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__2: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__3_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__5: f64 = 0.0;
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkCasesOn___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_mkCasesOn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOn___closed__0_value) as *mut LeanObject;
pub static l_Lean_mkCasesOn___closed__1_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_mkCasesOn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOn___closed__1_value) as *mut LeanObject;
static l_Lean_mkCasesOn___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_mkCasesOn___closed__0_value) as *mut LeanObject,
        142734480563613395 as *mut LeanObject,
    ],
};
pub static l_Lean_mkCasesOn___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_mkCasesOn___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_mkCasesOn___closed__1_value) as *mut LeanObject,
        14554705660503211730 as *mut LeanObject,
    ],
};
static mut l_Lean_mkCasesOn___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOn___closed__2_value) as *mut LeanObject;
pub static l_Lean_mkCasesOn___closed__3_value: LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_mkCasesOn___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOn___closed__3_value) as *mut LeanObject;
pub static l_Lean_mkCasesOn___closed__4_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_mkCasesOn___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOn___closed__4_value) as *mut LeanObject;
pub static l_Lean_mkCasesOn___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_mkCasesOn___closed__4_value) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l_Lean_mkCasesOn___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOn___closed__5_value) as *mut LeanObject;
static mut l_Lean_mkCasesOn___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkCasesOn___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkCasesOn___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkCasesOn___closed__7: f64 = 0.0;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_mkCasesOn___closed__0_value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [67, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,6298619751691480032 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 97, 115, 101, 115, 79, 110, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,13908150127721417385 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,14330104791255047660 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,16850664713141342957 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,5363805602364615876 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,6817493867345643597 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,6919186570005574456 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_mkCasesOn___closed__0_value) as *mut LeanObject,12403985358287198356 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,15944516466164890162 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,3279181264441860707 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,((( 989523109 as usize) << 1) | 1) as *mut LeanObject,13719880224209321761 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,15756402433763682466 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,15912005368295936558 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,10514961098779268799 as *mut LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg___lam__0(
    mut v_k_2935_: *mut LeanObject,
    mut v_b_2936_: *mut LeanObject,
    mut v___y_2937_: *mut LeanObject,
    mut v___y_2938_: *mut LeanObject,
    mut v___y_2939_: *mut LeanObject,
    mut v___y_2940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2940_);
    lean_inc_ref(v___y_2939_);
    lean_inc(v___y_2938_);
    lean_inc_ref(v___y_2937_);
    v___x_2942_ = lean_apply_6(
        v_k_2935_,
        v_b_2936_,
        v___y_2937_,
        v___y_2938_,
        v___y_2939_,
        v___y_2940_,
        lean_box(0),
    );
    return v___x_2942_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg___lam__0___boxed(
    mut v_k_2943_: *mut LeanObject,
    mut v_b_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
    mut v___y_2946_: *mut LeanObject,
    mut v___y_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2950_: *mut LeanObject = core::ptr::null_mut();
    v_res_2950_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg___lam__0(v_k_2943_, v_b_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
    lean_dec(v___y_2948_);
    lean_dec_ref(v___y_2947_);
    lean_dec(v___y_2946_);
    lean_dec_ref(v___y_2945_);
    return v_res_2950_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(
    mut v_name_2951_: *mut LeanObject,
    mut v_bi_2952_: u8,
    mut v_type_2953_: *mut LeanObject,
    mut v_k_2954_: *mut LeanObject,
    mut v_kind_2955_: u8,
    mut v___y_2956_: *mut LeanObject,
    mut v___y_2957_: *mut LeanObject,
    mut v___y_2958_: *mut LeanObject,
    mut v___y_2959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2970_: u8 = 0;
    let mut v_a_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2961_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_2961_, 0, v_k_2954_);
                v___x_2962_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_2962_) == 0 {
                    v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
                    v_isSharedCheck_2970_ = (!lean_is_exclusive(v___x_2962_)) as u8;
                    if v_isSharedCheck_2970_ == 0 {
                        v___x_2965_ = v___x_2962_;
                        v_isShared_2966_ = v_isSharedCheck_2970_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2963_);
                        lean_dec(v___x_2962_);
                        v___x_2965_ = lean_box(0);
                        v_isShared_2966_ = v_isSharedCheck_2970_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2971_ = lean_ctor_get(v___x_2962_, 0);
                    v_isSharedCheck_2978_ = (!lean_is_exclusive(v___x_2962_)) as u8;
                    if v_isSharedCheck_2978_ == 0 {
                        v___x_2973_ = v___x_2962_;
                        v_isShared_2974_ = v_isSharedCheck_2978_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2971_);
                        lean_dec(v___x_2962_);
                        v___x_2973_ = lean_box(0);
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
                    v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
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
                    v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
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
    mut v_name_2979_: *mut LeanObject,
    mut v_bi_2980_: *mut LeanObject,
    mut v_type_2981_: *mut LeanObject,
    mut v_k_2982_: *mut LeanObject,
    mut v_kind_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
    mut v___y_2985_: *mut LeanObject,
    mut v___y_2986_: *mut LeanObject,
    mut v___y_2987_: *mut LeanObject,
    mut v___y_2988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_2989_: u8 = 0;
    let mut v_kind_boxed_2990_: u8 = 0;
    let mut v_res_2991_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_2989_ = (lean_unbox(v_bi_2980_) as u8);
    v_kind_boxed_2990_ = (lean_unbox(v_kind_2983_) as u8);
    v_res_2991_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v_name_2979_, v_bi_boxed_2989_, v_type_2981_, v_k_2982_, v_kind_boxed_2990_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
    lean_dec(v___y_2987_);
    lean_dec_ref(v___y_2986_);
    lean_dec(v___y_2985_);
    lean_dec_ref(v___y_2984_);
    return v_res_2991_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0(
    mut v_00_u03b1_2992_: *mut LeanObject,
    mut v_name_2993_: *mut LeanObject,
    mut v_bi_2994_: u8,
    mut v_type_2995_: *mut LeanObject,
    mut v_k_2996_: *mut LeanObject,
    mut v_kind_2997_: u8,
    mut v___y_2998_: *mut LeanObject,
    mut v___y_2999_: *mut LeanObject,
    mut v___y_3000_: *mut LeanObject,
    mut v___y_3001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    v___x_3003_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v_name_2993_, v_bi_2994_, v_type_2995_, v_k_2996_, v_kind_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
    return v___x_3003_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___boxed(
    mut v_00_u03b1_3004_: *mut LeanObject,
    mut v_name_3005_: *mut LeanObject,
    mut v_bi_3006_: *mut LeanObject,
    mut v_type_3007_: *mut LeanObject,
    mut v_k_3008_: *mut LeanObject,
    mut v_kind_3009_: *mut LeanObject,
    mut v___y_3010_: *mut LeanObject,
    mut v___y_3011_: *mut LeanObject,
    mut v___y_3012_: *mut LeanObject,
    mut v___y_3013_: *mut LeanObject,
    mut v___y_3014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3015_: u8 = 0;
    let mut v_kind_boxed_3016_: u8 = 0;
    let mut v_res_3017_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3015_ = (lean_unbox(v_bi_3006_) as u8);
    v_kind_boxed_3016_ = (lean_unbox(v_kind_3009_) as u8);
    v_res_3017_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0(v_00_u03b1_3004_, v_name_3005_, v_bi_boxed_3015_, v_type_3007_, v_k_3008_, v_kind_boxed_3016_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
    lean_dec(v___y_3013_);
    lean_dec_ref(v___y_3012_);
    lean_dec(v___y_3011_);
    lean_dec_ref(v___y_3010_);
    return v_res_3017_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit___lam__0(
    mut v_body_3018_: *mut LeanObject,
    mut v_unit_3019_: *mut LeanObject,
    mut v_x_3020_: *mut LeanObject,
    mut v___y_3021_: *mut LeanObject,
    mut v___y_3022_: *mut LeanObject,
    mut v___y_3023_: *mut LeanObject,
    mut v___y_3024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    v___x_3026_ = lean_expr_instantiate1(v_body_3018_, v_x_3020_);
    v___x_3027_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit(
        v___x_3026_,
        v_unit_3019_,
        v___y_3021_,
        v___y_3022_,
        v___y_3023_,
        v___y_3024_,
    );
    if lean_obj_tag(v___x_3027_) == 0 {
        let mut v_a_3028_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3032_: u8 = 0;
        let mut v___x_3033_: u8 = 0;
        let mut v___x_3034_: u8 = 0;
        let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
        v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
        lean_inc(v_a_3028_);
        lean_dec_ref_known(v___x_3027_, 1);
        v___x_3029_ = lean_unsigned_to_nat(1);
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
        lean_dec_ref(v___x_3031_);
        return v___x_3035_;
    } else {
        lean_dec_ref(v_x_3020_);
        return v___x_3027_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit___lam__0___boxed(
    mut v_body_3036_: *mut LeanObject,
    mut v_unit_3037_: *mut LeanObject,
    mut v_x_3038_: *mut LeanObject,
    mut v___y_3039_: *mut LeanObject,
    mut v___y_3040_: *mut LeanObject,
    mut v___y_3041_: *mut LeanObject,
    mut v___y_3042_: *mut LeanObject,
    mut v___y_3043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3044_: *mut LeanObject = core::ptr::null_mut();
    v_res_3044_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit___lam__0(
        v_body_3036_,
        v_unit_3037_,
        v_x_3038_,
        v___y_3039_,
        v___y_3040_,
        v___y_3041_,
        v___y_3042_,
    );
    lean_dec(v___y_3042_);
    lean_dec_ref(v___y_3041_);
    lean_dec(v___y_3040_);
    lean_dec_ref(v___y_3039_);
    lean_dec_ref(v_body_3036_);
    return v_res_3044_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit(
    mut v_type_3045_: *mut LeanObject,
    mut v_unit_3046_: *mut LeanObject,
    mut v_a_3047_: *mut LeanObject,
    mut v_a_3048_: *mut LeanObject,
    mut v_a_3049_: *mut LeanObject,
    mut v_a_3050_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_type_3045_) == 7 {
        let mut v_binderName_3052_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_3053_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_3054_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_3055_: u8 = 0;
        let mut v___f_3056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3057_: u8 = 0;
        let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
        v_binderName_3052_ = lean_ctor_get(v_type_3045_, 0);
        lean_inc(v_binderName_3052_);
        v_binderType_3053_ = lean_ctor_get(v_type_3045_, 1);
        lean_inc_ref(v_binderType_3053_);
        v_body_3054_ = lean_ctor_get(v_type_3045_, 2);
        lean_inc_ref(v_body_3054_);
        v_binderInfo_3055_ = lean_ctor_get_uint8(
            v_type_3045_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        );
        lean_dec_ref_known(v_type_3045_, 3);
        v___f_3056_ = lean_alloc_closure(
            l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit___lam__0___boxed
                as *mut core::ffi::c_void,
            8,
            2,
        );
        lean_closure_set(v___f_3056_, 0, v_body_3054_);
        lean_closure_set(v___f_3056_, 1, v_unit_3046_);
        v___x_3057_ = 0;
        v___x_3058_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v_binderName_3052_, v_binderInfo_3055_, v_binderType_3053_, v___f_3056_, v___x_3057_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
        return v___x_3058_;
    } else {
        let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_type_3045_);
        v___x_3059_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3059_, 0, v_unit_3046_);
        return v___x_3059_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit___boxed(
    mut v_type_3060_: *mut LeanObject,
    mut v_unit_3061_: *mut LeanObject,
    mut v_a_3062_: *mut LeanObject,
    mut v_a_3063_: *mut LeanObject,
    mut v_a_3064_: *mut LeanObject,
    mut v_a_3065_: *mut LeanObject,
    mut v_a_3066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3067_: *mut LeanObject = core::ptr::null_mut();
    v_res_3067_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit(
        v_type_3060_,
        v_unit_3061_,
        v_a_3062_,
        v_a_3063_,
        v_a_3064_,
        v_a_3065_,
    );
    lean_dec(v_a_3065_);
    lean_dec_ref(v_a_3064_);
    lean_dec(v_a_3063_);
    lean_dec_ref(v_a_3062_);
    return v_res_3067_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit___lam__0(
    mut v_body_3068_: *mut LeanObject,
    mut v_unit_3069_: *mut LeanObject,
    mut v_x_3070_: *mut LeanObject,
    mut v___y_3071_: *mut LeanObject,
    mut v___y_3072_: *mut LeanObject,
    mut v___y_3073_: *mut LeanObject,
    mut v___y_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    v___x_3076_ = lean_expr_instantiate1(v_body_3068_, v_x_3070_);
    v___x_3077_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit(
        v___x_3076_,
        v_unit_3069_,
        v___y_3071_,
        v___y_3072_,
        v___y_3073_,
        v___y_3074_,
    );
    if lean_obj_tag(v___x_3077_) == 0 {
        let mut v_a_3078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3082_: u8 = 0;
        let mut v___x_3083_: u8 = 0;
        let mut v___x_3084_: u8 = 0;
        let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
        v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
        lean_inc(v_a_3078_);
        lean_dec_ref_known(v___x_3077_, 1);
        v___x_3079_ = lean_unsigned_to_nat(1);
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
        lean_dec_ref(v___x_3081_);
        return v___x_3085_;
    } else {
        lean_dec_ref(v_x_3070_);
        return v___x_3077_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit___lam__0___boxed(
    mut v_body_3086_: *mut LeanObject,
    mut v_unit_3087_: *mut LeanObject,
    mut v_x_3088_: *mut LeanObject,
    mut v___y_3089_: *mut LeanObject,
    mut v___y_3090_: *mut LeanObject,
    mut v___y_3091_: *mut LeanObject,
    mut v___y_3092_: *mut LeanObject,
    mut v___y_3093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3094_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3092_);
    lean_dec_ref(v___y_3091_);
    lean_dec(v___y_3090_);
    lean_dec_ref(v___y_3089_);
    lean_dec_ref(v_body_3086_);
    return v_res_3094_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit(
    mut v_type_3095_: *mut LeanObject,
    mut v_unit_3096_: *mut LeanObject,
    mut v_a_3097_: *mut LeanObject,
    mut v_a_3098_: *mut LeanObject,
    mut v_a_3099_: *mut LeanObject,
    mut v_a_3100_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_type_3095_) == 7 {
        let mut v_binderName_3102_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_3103_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_3104_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_3105_: u8 = 0;
        let mut v___f_3106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3107_: u8 = 0;
        let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
        v_binderName_3102_ = lean_ctor_get(v_type_3095_, 0);
        lean_inc(v_binderName_3102_);
        v_binderType_3103_ = lean_ctor_get(v_type_3095_, 1);
        lean_inc_ref(v_binderType_3103_);
        v_body_3104_ = lean_ctor_get(v_type_3095_, 2);
        lean_inc_ref(v_body_3104_);
        v_binderInfo_3105_ = lean_ctor_get_uint8(
            v_type_3095_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        );
        lean_dec_ref_known(v_type_3095_, 3);
        v___f_3106_ = lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
        lean_closure_set(v___f_3106_, 0, v_body_3104_);
        lean_closure_set(v___f_3106_, 1, v_unit_3096_);
        v___x_3107_ = 0;
        v___x_3108_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v_binderName_3102_, v_binderInfo_3105_, v_binderType_3103_, v___f_3106_, v___x_3107_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
        return v___x_3108_;
    } else {
        let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_type_3095_);
        v___x_3109_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3109_, 0, v_unit_3096_);
        return v___x_3109_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit___boxed(
    mut v_type_3110_: *mut LeanObject,
    mut v_unit_3111_: *mut LeanObject,
    mut v_a_3112_: *mut LeanObject,
    mut v_a_3113_: *mut LeanObject,
    mut v_a_3114_: *mut LeanObject,
    mut v_a_3115_: *mut LeanObject,
    mut v_a_3116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3117_: *mut LeanObject = core::ptr::null_mut();
    v_res_3117_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit(
        v_type_3110_,
        v_unit_3111_,
        v_a_3112_,
        v_a_3113_,
        v_a_3114_,
        v_a_3115_,
    );
    lean_dec(v_a_3115_);
    lean_dec_ref(v_a_3114_);
    lean_dec(v_a_3113_);
    lean_dec_ref(v_a_3112_);
    return v_res_3117_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_forallBody(
    mut v_type_3118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_body_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_type_3118_) == 7 {
                    v_body_3119_ = lean_ctor_get(v_type_3118_, 2);
                    v_type_3118_ = v_body_3119_;
                    state = 0;
                    continue;
                } else {
                    lean_inc_ref(v_type_3118_);
                    return v_type_3118_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_forallBody___boxed(
    mut v_type_3121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3122_: *mut LeanObject = core::ptr::null_mut();
    v_res_3122_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_forallBody(v_type_3121_);
    lean_dec_ref(v_type_3121_);
    return v_res_3122_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0_spec__0(
    mut v_a_3123_: *mut LeanObject,
    mut v_as_3124_: *mut LeanObject,
    mut v_i_3125_: usize,
    mut v_stop_3126_: usize,
) -> u8 {
    let mut v___x_3127_: u8 = 0;
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3134_: *mut LeanObject,
    mut v_as_3135_: *mut LeanObject,
    mut v_i_3136_: *mut LeanObject,
    mut v_stop_3137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3138_: usize = 0;
    let mut v_stop_boxed_3139_: usize = 0;
    let mut v_res_3140_: u8 = 0;
    let mut v_r_3141_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3138_ = lean_unbox_usize(v_i_3136_);
    lean_dec(v_i_3136_);
    v_stop_boxed_3139_ = lean_unbox_usize(v_stop_3137_);
    lean_dec(v_stop_3137_);
    v_res_3140_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0_spec__0(v_a_3134_, v_as_3135_, v_i_boxed_3138_, v_stop_boxed_3139_);
    lean_dec_ref(v_as_3135_);
    lean_dec(v_a_3134_);
    v_r_3141_ = lean_box((v_res_3140_) as usize);
    return v_r_3141_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0(
    mut v_as_3142_: *mut LeanObject,
    mut v_a_3143_: *mut LeanObject,
) -> u8 {
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: u8 = 0;
    v___x_3144_ = lean_unsigned_to_nat(0);
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
    mut v_as_3150_: *mut LeanObject,
    mut v_a_3151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3152_: u8 = 0;
    let mut v_r_3153_: *mut LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0(v_as_3150_, v_a_3151_);
    lean_dec(v_a_3151_);
    lean_dec_ref(v_as_3150_);
    v_r_3153_ = lean_box((v_res_3152_) as usize);
    return v_r_3153_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg(
    mut v_motiveIds_3154_: *mut LeanObject,
    mut v_arg_3155_: *mut LeanObject,
) -> u8 {
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    v___x_3156_ = l_Lean_Expr_getAppFn(v_arg_3155_);
    if lean_obj_tag(v___x_3156_) == 1 {
        let mut v_fvarId_3157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3158_: u8 = 0;
        v_fvarId_3157_ = lean_ctor_get(v___x_3156_, 0);
        lean_inc(v_fvarId_3157_);
        lean_dec_ref_known(v___x_3156_, 1);
        v___x_3158_ = l_Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0(v_motiveIds_3154_, v_fvarId_3157_);
        lean_dec(v_fvarId_3157_);
        return v___x_3158_;
    } else {
        let mut v___x_3159_: u8 = 0;
        lean_dec_ref(v___x_3156_);
        v___x_3159_ = 0;
        return v___x_3159_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg___boxed(
    mut v_motiveIds_3160_: *mut LeanObject,
    mut v_arg_3161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3162_: u8 = 0;
    let mut v_r_3163_: *mut LeanObject = core::ptr::null_mut();
    v_res_3162_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg(
        v_motiveIds_3160_,
        v_arg_3161_,
    );
    lean_dec_ref(v_arg_3161_);
    lean_dec_ref(v_motiveIds_3160_);
    v_r_3163_ = lean_box((v_res_3162_) as usize);
    return v_r_3163_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__0___boxed(
    mut v_minorParams_3164_: *mut LeanObject,
    mut v_motiveIds_3165_: *mut LeanObject,
    mut v_mainMotiveId_3166_: *mut LeanObject,
    mut v_unit_3167_: *mut LeanObject,
    mut v_body_3168_: *mut LeanObject,
    mut v_isMain_3169_: *mut LeanObject,
    mut v_minorNonRecParams_3170_: *mut LeanObject,
    mut v_k_3171_: *mut LeanObject,
    mut v_newLocal_3172_: *mut LeanObject,
    mut v___y_3173_: *mut LeanObject,
    mut v___y_3174_: *mut LeanObject,
    mut v___y_3175_: *mut LeanObject,
    mut v___y_3176_: *mut LeanObject,
    mut v___y_3177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMain_boxed_3178_: u8 = 0;
    let mut v_res_3179_: *mut LeanObject = core::ptr::null_mut();
    v_isMain_boxed_3178_ = (lean_unbox(v_isMain_3169_) as u8);
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
    lean_dec(v___y_3176_);
    lean_dec_ref(v___y_3175_);
    lean_dec(v___y_3174_);
    lean_dec_ref(v___y_3173_);
    return v_res_3179_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__1(
    mut v_body_3180_: *mut LeanObject,
    mut v_binderType_3181_: *mut LeanObject,
    mut v_motiveIds_3182_: *mut LeanObject,
    mut v_minorParams_3183_: *mut LeanObject,
    mut v_isMain_3184_: u8,
    mut v_mainMotiveId_3185_: *mut LeanObject,
    mut v_unit_3186_: *mut LeanObject,
    mut v_minorNonRecParams_3187_: *mut LeanObject,
    mut v_k_3188_: *mut LeanObject,
    mut v_binderName_3189_: *mut LeanObject,
    mut v_binderInfo_3190_: u8,
    mut v_x_3191_: *mut LeanObject,
    mut v___y_3192_: *mut LeanObject,
    mut v___y_3193_: *mut LeanObject,
    mut v___y_3194_: *mut LeanObject,
    mut v___y_3195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_body_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_argTarget_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: u8 = 0;
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: u8 = 0;
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3220_: u8 = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_dec_ref(v_argTarget_3198_);
                    lean_dec(v_binderName_3189_);
                    lean_dec_ref(v_binderType_3181_);
                    lean_inc_ref(v_x_3191_);
                    v___x_3200_ = lean_array_push(v_minorParams_3183_, v_x_3191_);
                    if v_isMain_3184_ == 0 {
                        lean_dec_ref(v_x_3191_);
                        v___x_3201_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg(v_motiveIds_3182_, v_mainMotiveId_3185_, v_unit_3186_, v_body_3197_, v_isMain_3184_, v___x_3200_, v_minorNonRecParams_3187_, v_k_3188_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
                        return v___x_3201_;
                    } else {
                        v___x_3202_ = lean_array_push(v_minorNonRecParams_3187_, v_x_3191_);
                        v___x_3203_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg(v_motiveIds_3182_, v_mainMotiveId_3185_, v_unit_3186_, v_body_3197_, v_isMain_3184_, v___x_3200_, v___x_3202_, v_k_3188_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
                        return v___x_3203_;
                    }
                } else {
                    v___x_3204_ = l_Lean_Expr_getAppFn(v_argTarget_3198_);
                    lean_dec_ref(v_argTarget_3198_);
                    v___x_3205_ = l_Lean_Expr_fvarId_x21(v___x_3204_);
                    lean_dec_ref(v___x_3204_);
                    v___x_3206_ = l_Lean_instBEqFVarId_beq(v___x_3205_, v_mainMotiveId_3185_);
                    lean_dec(v___x_3205_);
                    if v___x_3206_ == 0 {
                        lean_dec_ref(v_x_3191_);
                        lean_inc_ref(v_unit_3186_);
                        v___x_3207_ =
                            l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit(
                                v_binderType_3181_,
                                v_unit_3186_,
                                v___y_3192_,
                                v___y_3193_,
                                v___y_3194_,
                                v___y_3195_,
                            );
                        if lean_obj_tag(v___x_3207_) == 0 {
                            v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
                            lean_inc(v_a_3208_);
                            lean_dec_ref_known(v___x_3207_, 1);
                            v___x_3209_ = lean_box((v_isMain_3184_) as usize);
                            v___f_3210_ = lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 8);
                            lean_closure_set(v___f_3210_, 0, v_minorParams_3183_);
                            lean_closure_set(v___f_3210_, 1, v_motiveIds_3182_);
                            lean_closure_set(v___f_3210_, 2, v_mainMotiveId_3185_);
                            lean_closure_set(v___f_3210_, 3, v_unit_3186_);
                            lean_closure_set(v___f_3210_, 4, v_body_3197_);
                            lean_closure_set(v___f_3210_, 5, v___x_3209_);
                            lean_closure_set(v___f_3210_, 6, v_minorNonRecParams_3187_);
                            lean_closure_set(v___f_3210_, 7, v_k_3188_);
                            v___x_3211_ = 0;
                            v___x_3212_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v_binderName_3189_, v_binderInfo_3190_, v_a_3208_, v___f_3210_, v___x_3211_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
                            return v___x_3212_;
                        } else {
                            lean_dec_ref(v_body_3197_);
                            lean_dec(v_binderName_3189_);
                            lean_dec_ref(v_k_3188_);
                            lean_dec_ref(v_minorNonRecParams_3187_);
                            lean_dec_ref(v_unit_3186_);
                            lean_dec(v_mainMotiveId_3185_);
                            lean_dec_ref(v_minorParams_3183_);
                            lean_dec_ref(v_motiveIds_3182_);
                            v_a_3213_ = lean_ctor_get(v___x_3207_, 0);
                            v_isSharedCheck_3220_ = (!lean_is_exclusive(v___x_3207_)) as u8;
                            if v_isSharedCheck_3220_ == 0 {
                                v___x_3215_ = v___x_3207_;
                                v_isShared_3216_ = v_isSharedCheck_3220_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3213_);
                                lean_dec(v___x_3207_);
                                v___x_3215_ = lean_box(0);
                                v_isShared_3216_ = v_isSharedCheck_3220_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_binderName_3189_);
                        lean_dec_ref(v_binderType_3181_);
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
                    v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_body_3223_: *mut LeanObject = *_args.add(0);
    let mut v_binderType_3224_: *mut LeanObject = *_args.add(1);
    let mut v_motiveIds_3225_: *mut LeanObject = *_args.add(2);
    let mut v_minorParams_3226_: *mut LeanObject = *_args.add(3);
    let mut v_isMain_3227_: *mut LeanObject = *_args.add(4);
    let mut v_mainMotiveId_3228_: *mut LeanObject = *_args.add(5);
    let mut v_unit_3229_: *mut LeanObject = *_args.add(6);
    let mut v_minorNonRecParams_3230_: *mut LeanObject = *_args.add(7);
    let mut v_k_3231_: *mut LeanObject = *_args.add(8);
    let mut v_binderName_3232_: *mut LeanObject = *_args.add(9);
    let mut v_binderInfo_3233_: *mut LeanObject = *_args.add(10);
    let mut v_x_3234_: *mut LeanObject = *_args.add(11);
    let mut v___y_3235_: *mut LeanObject = *_args.add(12);
    let mut v___y_3236_: *mut LeanObject = *_args.add(13);
    let mut v___y_3237_: *mut LeanObject = *_args.add(14);
    let mut v___y_3238_: *mut LeanObject = *_args.add(15);
    let mut v___y_3239_: *mut LeanObject = *_args.add(16);
    let mut v_isMain_boxed_3240_: u8 = 0;
    let mut v_binderInfo_548__boxed_3241_: u8 = 0;
    let mut v_res_3242_: *mut LeanObject = core::ptr::null_mut();
    v_isMain_boxed_3240_ = (lean_unbox(v_isMain_3227_) as u8);
    v_binderInfo_548__boxed_3241_ = (lean_unbox(v_binderInfo_3233_) as u8);
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
    lean_dec(v___y_3238_);
    lean_dec_ref(v___y_3237_);
    lean_dec(v___y_3236_);
    lean_dec_ref(v___y_3235_);
    lean_dec_ref(v_body_3223_);
    return v_res_3242_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg(
    mut v_motiveIds_3243_: *mut LeanObject,
    mut v_mainMotiveId_3244_: *mut LeanObject,
    mut v_unit_3245_: *mut LeanObject,
    mut v_minorType_3246_: *mut LeanObject,
    mut v_isMain_3247_: u8,
    mut v_minorParams_3248_: *mut LeanObject,
    mut v_minorNonRecParams_3249_: *mut LeanObject,
    mut v_k_3250_: *mut LeanObject,
    mut v_a_3251_: *mut LeanObject,
    mut v_a_3252_: *mut LeanObject,
    mut v_a_3253_: *mut LeanObject,
    mut v_a_3254_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_minorType_3246_) == 7 {
        let mut v_binderName_3256_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_3257_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_3258_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_3259_: u8 = 0;
        let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3263_: u8 = 0;
        let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
        v_binderName_3256_ = lean_ctor_get(v_minorType_3246_, 0);
        lean_inc_n(v_binderName_3256_, 2);
        v_binderType_3257_ = lean_ctor_get(v_minorType_3246_, 1);
        lean_inc_ref_n(v_binderType_3257_, 2);
        v_body_3258_ = lean_ctor_get(v_minorType_3246_, 2);
        lean_inc_ref(v_body_3258_);
        v_binderInfo_3259_ = lean_ctor_get_uint8(
            v_minorType_3246_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        );
        lean_dec_ref_known(v_minorType_3246_, 3);
        v___x_3260_ = lean_box((v_isMain_3247_) as usize);
        v___x_3261_ = lean_box((v_binderInfo_3259_) as usize);
        v___f_3262_ = lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__1___boxed as *mut core::ffi::c_void, 17, 11);
        lean_closure_set(v___f_3262_, 0, v_body_3258_);
        lean_closure_set(v___f_3262_, 1, v_binderType_3257_);
        lean_closure_set(v___f_3262_, 2, v_motiveIds_3243_);
        lean_closure_set(v___f_3262_, 3, v_minorParams_3248_);
        lean_closure_set(v___f_3262_, 4, v___x_3260_);
        lean_closure_set(v___f_3262_, 5, v_mainMotiveId_3244_);
        lean_closure_set(v___f_3262_, 6, v_unit_3245_);
        lean_closure_set(v___f_3262_, 7, v_minorNonRecParams_3249_);
        lean_closure_set(v___f_3262_, 8, v_k_3250_);
        lean_closure_set(v___f_3262_, 9, v_binderName_3256_);
        lean_closure_set(v___f_3262_, 10, v___x_3261_);
        v___x_3263_ = 0;
        v___x_3264_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v_binderName_3256_, v_binderInfo_3259_, v_binderType_3257_, v___f_3262_, v___x_3263_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
        return v___x_3264_;
    } else {
        let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_unit_3245_);
        lean_dec(v_mainMotiveId_3244_);
        lean_dec_ref(v_motiveIds_3243_);
        lean_inc(v_a_3254_);
        lean_inc_ref(v_a_3253_);
        lean_inc(v_a_3252_);
        lean_inc_ref(v_a_3251_);
        v___x_3265_ = lean_apply_8(
            v_k_3250_,
            v_minorParams_3248_,
            v_minorNonRecParams_3249_,
            v_minorType_3246_,
            v_a_3251_,
            v_a_3252_,
            v_a_3253_,
            v_a_3254_,
            lean_box(0),
        );
        return v___x_3265_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__0(
    mut v_minorParams_3266_: *mut LeanObject,
    mut v_motiveIds_3267_: *mut LeanObject,
    mut v_mainMotiveId_3268_: *mut LeanObject,
    mut v_unit_3269_: *mut LeanObject,
    mut v_body_3270_: *mut LeanObject,
    mut v_isMain_3271_: u8,
    mut v_minorNonRecParams_3272_: *mut LeanObject,
    mut v_k_3273_: *mut LeanObject,
    mut v_newLocal_3274_: *mut LeanObject,
    mut v___y_3275_: *mut LeanObject,
    mut v___y_3276_: *mut LeanObject,
    mut v___y_3277_: *mut LeanObject,
    mut v___y_3278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_motiveIds_3282_: *mut LeanObject,
    mut v_mainMotiveId_3283_: *mut LeanObject,
    mut v_unit_3284_: *mut LeanObject,
    mut v_minorType_3285_: *mut LeanObject,
    mut v_isMain_3286_: *mut LeanObject,
    mut v_minorParams_3287_: *mut LeanObject,
    mut v_minorNonRecParams_3288_: *mut LeanObject,
    mut v_k_3289_: *mut LeanObject,
    mut v_a_3290_: *mut LeanObject,
    mut v_a_3291_: *mut LeanObject,
    mut v_a_3292_: *mut LeanObject,
    mut v_a_3293_: *mut LeanObject,
    mut v_a_3294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMain_boxed_3295_: u8 = 0;
    let mut v_res_3296_: *mut LeanObject = core::ptr::null_mut();
    v_isMain_boxed_3295_ = (lean_unbox(v_isMain_3286_) as u8);
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
    lean_dec(v_a_3293_);
    lean_dec_ref(v_a_3292_);
    lean_dec(v_a_3291_);
    lean_dec_ref(v_a_3290_);
    return v_res_3296_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams(
    mut v_00_u03b1_3297_: *mut LeanObject,
    mut v_motiveIds_3298_: *mut LeanObject,
    mut v_mainMotiveId_3299_: *mut LeanObject,
    mut v_unit_3300_: *mut LeanObject,
    mut v_minorType_3301_: *mut LeanObject,
    mut v_isMain_3302_: u8,
    mut v_minorParams_3303_: *mut LeanObject,
    mut v_minorNonRecParams_3304_: *mut LeanObject,
    mut v_k_3305_: *mut LeanObject,
    mut v_a_3306_: *mut LeanObject,
    mut v_a_3307_: *mut LeanObject,
    mut v_a_3308_: *mut LeanObject,
    mut v_a_3309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3312_: *mut LeanObject,
    mut v_motiveIds_3313_: *mut LeanObject,
    mut v_mainMotiveId_3314_: *mut LeanObject,
    mut v_unit_3315_: *mut LeanObject,
    mut v_minorType_3316_: *mut LeanObject,
    mut v_isMain_3317_: *mut LeanObject,
    mut v_minorParams_3318_: *mut LeanObject,
    mut v_minorNonRecParams_3319_: *mut LeanObject,
    mut v_k_3320_: *mut LeanObject,
    mut v_a_3321_: *mut LeanObject,
    mut v_a_3322_: *mut LeanObject,
    mut v_a_3323_: *mut LeanObject,
    mut v_a_3324_: *mut LeanObject,
    mut v_a_3325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMain_boxed_3326_: u8 = 0;
    let mut v_res_3327_: *mut LeanObject = core::ptr::null_mut();
    v_isMain_boxed_3326_ = (lean_unbox(v_isMain_3317_) as u8);
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
    lean_dec(v_a_3324_);
    lean_dec_ref(v_a_3323_);
    lean_dec(v_a_3322_);
    lean_dec_ref(v_a_3321_);
    return v_res_3327_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minorNonRecParams_3328_: *mut LeanObject = *_args.add(0);
    let mut v_minorParams_3329_: *mut LeanObject = *_args.add(1);
    let mut v___x_3330_: *mut LeanObject = *_args.add(2);
    let mut v___x_3331_: *mut LeanObject = *_args.add(3);
    let mut v___x_3332_: *mut LeanObject = *_args.add(4);
    let mut v_minorIdx_3333_: *mut LeanObject = *_args.add(5);
    let mut v_casesOnParams_3334_: *mut LeanObject = *_args.add(6);
    let mut v_recArgs_3335_: *mut LeanObject = *_args.add(7);
    let mut v_motiveIds_3336_: *mut LeanObject = *_args.add(8);
    let mut v_mainMotiveId_3337_: *mut LeanObject = *_args.add(9);
    let mut v_unit_3338_: *mut LeanObject = *_args.add(10);
    let mut v_star_3339_: *mut LeanObject = *_args.add(11);
    let mut v_minorEntries_3340_: *mut LeanObject = *_args.add(12);
    let mut v_k_3341_: *mut LeanObject = *_args.add(13);
    let mut v_newC_3342_: *mut LeanObject = *_args.add(14);
    let mut v___y_3343_: *mut LeanObject = *_args.add(15);
    let mut v___y_3344_: *mut LeanObject = *_args.add(16);
    let mut v___y_3345_: *mut LeanObject = *_args.add(17);
    let mut v___y_3346_: *mut LeanObject = *_args.add(18);
    let mut v___y_3347_: *mut LeanObject = *_args.add(19);
    let mut v___x_799__boxed_3348_: u8 = 0;
    let mut v___x_800__boxed_3349_: u8 = 0;
    let mut v___x_801__boxed_3350_: u8 = 0;
    let mut v_res_3351_: *mut LeanObject = core::ptr::null_mut();
    v___x_799__boxed_3348_ = (lean_unbox(v___x_3330_) as u8);
    v___x_800__boxed_3349_ = (lean_unbox(v___x_3331_) as u8);
    v___x_801__boxed_3350_ = (lean_unbox(v___x_3332_) as u8);
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
    lean_dec(v___y_3346_);
    lean_dec_ref(v___y_3345_);
    lean_dec(v___y_3344_);
    lean_dec_ref(v___y_3343_);
    lean_dec(v_minorIdx_3333_);
    lean_dec_ref(v_minorParams_3329_);
    lean_dec_ref(v_minorNonRecParams_3328_);
    return v_res_3351_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___lam__1(
    mut v_snd_3352_: u8,
    mut v_star_3353_: *mut LeanObject,
    mut v___x_3354_: u8,
    mut v_minorIdx_3355_: *mut LeanObject,
    mut v_recArgs_3356_: *mut LeanObject,
    mut v_motiveIds_3357_: *mut LeanObject,
    mut v_mainMotiveId_3358_: *mut LeanObject,
    mut v_unit_3359_: *mut LeanObject,
    mut v_minorEntries_3360_: *mut LeanObject,
    mut v_casesOnParams_3361_: *mut LeanObject,
    mut v_k_3362_: *mut LeanObject,
    mut v_a_3363_: *mut LeanObject,
    mut v_minorParams_3364_: *mut LeanObject,
    mut v_minorNonRecParams_3365_: *mut LeanObject,
    mut v_minorType_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
    mut v___y_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3372_: u8 = 0;
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3382_: u8 = 0;
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3386_: u8 = 0;
    let mut v___x_3387_: u8 = 0;
    let mut v___x_3388_: u8 = 0;
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: u8 = 0;
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3402_: u8 = 0;
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_snd_3352_ == 0 {
                    lean_dec_ref(v_minorType_3366_);
                    lean_dec_ref(v_minorNonRecParams_3365_);
                    v___x_3372_ = 1;
                    lean_inc_ref(v_star_3353_);
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
                    lean_dec_ref(v_minorParams_3364_);
                    if lean_obj_tag(v___x_3373_) == 0 {
                        v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
                        lean_inc(v_a_3374_);
                        lean_dec_ref_known(v___x_3373_, 1);
                        v___x_3375_ = lean_unsigned_to_nat(1);
                        v___x_3376_ = lean_nat_add(v_minorIdx_3355_, v___x_3375_);
                        lean_dec(v_minorIdx_3355_);
                        v___x_3377_ = lean_array_push(v_recArgs_3356_, v_a_3374_);
                        v___x_3378_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg(v_motiveIds_3357_, v_mainMotiveId_3358_, v_unit_3359_, v_star_3353_, v_minorEntries_3360_, v___x_3376_, v_casesOnParams_3361_, v___x_3377_, v_k_3362_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
                        return v___x_3378_;
                    } else {
                        lean_dec_ref(v_k_3362_);
                        lean_dec_ref(v_casesOnParams_3361_);
                        lean_dec_ref(v_minorEntries_3360_);
                        lean_dec_ref(v_unit_3359_);
                        lean_dec(v_mainMotiveId_3358_);
                        lean_dec_ref(v_motiveIds_3357_);
                        lean_dec_ref(v_recArgs_3356_);
                        lean_dec(v_minorIdx_3355_);
                        lean_dec_ref(v_star_3353_);
                        v_a_3379_ = lean_ctor_get(v___x_3373_, 0);
                        v_isSharedCheck_3386_ = (!lean_is_exclusive(v___x_3373_)) as u8;
                        if v_isSharedCheck_3386_ == 0 {
                            v___x_3381_ = v___x_3373_;
                            v_isShared_3382_ = v_isSharedCheck_3386_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3379_);
                            lean_dec(v___x_3373_);
                            v___x_3381_ = lean_box(0);
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
                    if lean_obj_tag(v___x_3389_) == 0 {
                        v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
                        lean_inc(v_a_3390_);
                        lean_dec_ref_known(v___x_3389_, 1);
                        v___x_3391_ = lean_box((v___x_3387_) as usize);
                        v___x_3392_ = lean_box((v___x_3354_) as usize);
                        v___x_3393_ = lean_box((v___x_3388_) as usize);
                        v___f_3394_ = lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___lam__0___boxed as *mut core::ffi::c_void, 20, 14);
                        lean_closure_set(v___f_3394_, 0, v_minorNonRecParams_3365_);
                        lean_closure_set(v___f_3394_, 1, v_minorParams_3364_);
                        lean_closure_set(v___f_3394_, 2, v___x_3391_);
                        lean_closure_set(v___f_3394_, 3, v___x_3392_);
                        lean_closure_set(v___f_3394_, 4, v___x_3393_);
                        lean_closure_set(v___f_3394_, 5, v_minorIdx_3355_);
                        lean_closure_set(v___f_3394_, 6, v_casesOnParams_3361_);
                        lean_closure_set(v___f_3394_, 7, v_recArgs_3356_);
                        lean_closure_set(v___f_3394_, 8, v_motiveIds_3357_);
                        lean_closure_set(v___f_3394_, 9, v_mainMotiveId_3358_);
                        lean_closure_set(v___f_3394_, 10, v_unit_3359_);
                        lean_closure_set(v___f_3394_, 11, v_star_3353_);
                        lean_closure_set(v___f_3394_, 12, v_minorEntries_3360_);
                        lean_closure_set(v___f_3394_, 13, v_k_3362_);
                        v___x_3395_ = l_Lean_LocalDecl_userName(v_a_3363_);
                        v___x_3396_ = l_Lean_LocalDecl_binderInfo(v_a_3363_);
                        v___x_3397_ = 0;
                        v___x_3398_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v___x_3395_, v___x_3396_, v_a_3390_, v___f_3394_, v___x_3397_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
                        return v___x_3398_;
                    } else {
                        lean_dec_ref(v_minorNonRecParams_3365_);
                        lean_dec_ref(v_minorParams_3364_);
                        lean_dec_ref(v_k_3362_);
                        lean_dec_ref(v_casesOnParams_3361_);
                        lean_dec_ref(v_minorEntries_3360_);
                        lean_dec_ref(v_unit_3359_);
                        lean_dec(v_mainMotiveId_3358_);
                        lean_dec_ref(v_motiveIds_3357_);
                        lean_dec_ref(v_recArgs_3356_);
                        lean_dec(v_minorIdx_3355_);
                        lean_dec_ref(v_star_3353_);
                        v_a_3399_ = lean_ctor_get(v___x_3389_, 0);
                        v_isSharedCheck_3406_ = (!lean_is_exclusive(v___x_3389_)) as u8;
                        if v_isSharedCheck_3406_ == 0 {
                            v___x_3401_ = v___x_3389_;
                            v_isShared_3402_ = v_isSharedCheck_3406_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3399_);
                            lean_dec(v___x_3389_);
                            v___x_3401_ = lean_box(0);
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
                    v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
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
                    v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3407_: *mut LeanObject = *_args.add(0);
    let mut v_star_3408_: *mut LeanObject = *_args.add(1);
    let mut v___x_3409_: *mut LeanObject = *_args.add(2);
    let mut v_minorIdx_3410_: *mut LeanObject = *_args.add(3);
    let mut v_recArgs_3411_: *mut LeanObject = *_args.add(4);
    let mut v_motiveIds_3412_: *mut LeanObject = *_args.add(5);
    let mut v_mainMotiveId_3413_: *mut LeanObject = *_args.add(6);
    let mut v_unit_3414_: *mut LeanObject = *_args.add(7);
    let mut v_minorEntries_3415_: *mut LeanObject = *_args.add(8);
    let mut v_casesOnParams_3416_: *mut LeanObject = *_args.add(9);
    let mut v_k_3417_: *mut LeanObject = *_args.add(10);
    let mut v_a_3418_: *mut LeanObject = *_args.add(11);
    let mut v_minorParams_3419_: *mut LeanObject = *_args.add(12);
    let mut v_minorNonRecParams_3420_: *mut LeanObject = *_args.add(13);
    let mut v_minorType_3421_: *mut LeanObject = *_args.add(14);
    let mut v___y_3422_: *mut LeanObject = *_args.add(15);
    let mut v___y_3423_: *mut LeanObject = *_args.add(16);
    let mut v___y_3424_: *mut LeanObject = *_args.add(17);
    let mut v___y_3425_: *mut LeanObject = *_args.add(18);
    let mut v___y_3426_: *mut LeanObject = *_args.add(19);
    let mut v_snd_835__boxed_3427_: u8 = 0;
    let mut v___x_836__boxed_3428_: u8 = 0;
    let mut v_res_3429_: *mut LeanObject = core::ptr::null_mut();
    v_snd_835__boxed_3427_ = (lean_unbox(v_snd_3407_) as u8);
    v___x_836__boxed_3428_ = (lean_unbox(v___x_3409_) as u8);
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
    lean_dec(v___y_3425_);
    lean_dec_ref(v___y_3424_);
    lean_dec(v___y_3423_);
    lean_dec_ref(v___y_3422_);
    lean_dec_ref(v_a_3418_);
    return v_res_3429_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg(
    mut v_motiveIds_3432_: *mut LeanObject,
    mut v_mainMotiveId_3433_: *mut LeanObject,
    mut v_unit_3434_: *mut LeanObject,
    mut v_star_3435_: *mut LeanObject,
    mut v_minorEntries_3436_: *mut LeanObject,
    mut v_minorIdx_3437_: *mut LeanObject,
    mut v_casesOnParams_3438_: *mut LeanObject,
    mut v_recArgs_3439_: *mut LeanObject,
    mut v_k_3440_: *mut LeanObject,
    mut v_a_3441_: *mut LeanObject,
    mut v_a_3442_: *mut LeanObject,
    mut v_a_3443_: *mut LeanObject,
    mut v_a_3444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: u8 = 0;
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: u8 = 0;
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3446_ = lean_array_get_size(v_minorEntries_3436_);
                v___x_3447_ = lean_nat_dec_lt(v_minorIdx_3437_, v___x_3446_);
                if v___x_3447_ == 0 {
                    lean_dec(v_minorIdx_3437_);
                    lean_dec_ref(v_minorEntries_3436_);
                    lean_dec_ref(v_star_3435_);
                    lean_dec_ref(v_unit_3434_);
                    lean_dec(v_mainMotiveId_3433_);
                    lean_dec_ref(v_motiveIds_3432_);
                    lean_inc(v_a_3444_);
                    lean_inc_ref(v_a_3443_);
                    lean_inc(v_a_3442_);
                    lean_inc_ref(v_a_3441_);
                    v___x_3448_ = lean_apply_7(
                        v_k_3440_,
                        v_casesOnParams_3438_,
                        v_recArgs_3439_,
                        v_a_3441_,
                        v_a_3442_,
                        v_a_3443_,
                        v_a_3444_,
                        lean_box(0),
                    );
                    return v___x_3448_;
                } else {
                    v___x_3449_ = lean_array_fget_borrowed(v_minorEntries_3436_, v_minorIdx_3437_);
                    v_fst_3450_ = lean_ctor_get(v___x_3449_, 0);
                    v_snd_3451_ = lean_ctor_get(v___x_3449_, 1);
                    lean_inc(v_snd_3451_);
                    v___x_3452_ = l_Lean_Expr_fvarId_x21(v_fst_3450_);
                    v___x_3453_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_3452_,
                        v_a_3441_,
                        v_a_3443_,
                        v_a_3444_,
                    );
                    if lean_obj_tag(v___x_3453_) == 0 {
                        v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
                        lean_inc_n(v_a_3454_, 2);
                        lean_dec_ref_known(v___x_3453_, 1);
                        v___x_3455_ = lean_box((v___x_3447_) as usize);
                        lean_inc_ref(v_unit_3434_);
                        lean_inc(v_mainMotiveId_3433_);
                        lean_inc_ref(v_motiveIds_3432_);
                        lean_inc(v_snd_3451_);
                        v___f_3456_ = lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___lam__1___boxed as *mut core::ffi::c_void, 20, 12);
                        lean_closure_set(v___f_3456_, 0, v_snd_3451_);
                        lean_closure_set(v___f_3456_, 1, v_star_3435_);
                        lean_closure_set(v___f_3456_, 2, v___x_3455_);
                        lean_closure_set(v___f_3456_, 3, v_minorIdx_3437_);
                        lean_closure_set(v___f_3456_, 4, v_recArgs_3439_);
                        lean_closure_set(v___f_3456_, 5, v_motiveIds_3432_);
                        lean_closure_set(v___f_3456_, 6, v_mainMotiveId_3433_);
                        lean_closure_set(v___f_3456_, 7, v_unit_3434_);
                        lean_closure_set(v___f_3456_, 8, v_minorEntries_3436_);
                        lean_closure_set(v___f_3456_, 9, v_casesOnParams_3438_);
                        lean_closure_set(v___f_3456_, 10, v_k_3440_);
                        lean_closure_set(v___f_3456_, 11, v_a_3454_);
                        v___x_3457_ = l_Lean_LocalDecl_type(v_a_3454_);
                        lean_dec(v_a_3454_);
                        v___x_3458_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0;
                        v___x_3459_ = (lean_unbox(v_snd_3451_) as u8);
                        lean_dec(v_snd_3451_);
                        v___x_3460_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg(v_motiveIds_3432_, v_mainMotiveId_3433_, v_unit_3434_, v___x_3457_, v___x_3459_, v___x_3458_, v___x_3458_, v___f_3456_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
                        return v___x_3460_;
                    } else {
                        lean_dec(v_snd_3451_);
                        lean_dec_ref(v_k_3440_);
                        lean_dec_ref(v_recArgs_3439_);
                        lean_dec_ref(v_casesOnParams_3438_);
                        lean_dec(v_minorIdx_3437_);
                        lean_dec_ref(v_minorEntries_3436_);
                        lean_dec_ref(v_star_3435_);
                        lean_dec_ref(v_unit_3434_);
                        lean_dec(v_mainMotiveId_3433_);
                        lean_dec_ref(v_motiveIds_3432_);
                        v_a_3461_ = lean_ctor_get(v___x_3453_, 0);
                        v_isSharedCheck_3468_ = (!lean_is_exclusive(v___x_3453_)) as u8;
                        if v_isSharedCheck_3468_ == 0 {
                            v___x_3463_ = v___x_3453_;
                            v_isShared_3464_ = v_isSharedCheck_3468_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3461_);
                            lean_dec(v___x_3453_);
                            v___x_3463_ = lean_box(0);
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
                    v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
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
    mut v_minorNonRecParams_3469_: *mut LeanObject,
    mut v_minorParams_3470_: *mut LeanObject,
    mut v___x_3471_: u8,
    mut v___x_3472_: u8,
    mut v___x_3473_: u8,
    mut v_minorIdx_3474_: *mut LeanObject,
    mut v_casesOnParams_3475_: *mut LeanObject,
    mut v_recArgs_3476_: *mut LeanObject,
    mut v_motiveIds_3477_: *mut LeanObject,
    mut v_mainMotiveId_3478_: *mut LeanObject,
    mut v_unit_3479_: *mut LeanObject,
    mut v_star_3480_: *mut LeanObject,
    mut v_minorEntries_3481_: *mut LeanObject,
    mut v_k_3482_: *mut LeanObject,
    mut v_newC_3483_: *mut LeanObject,
    mut v___y_3484_: *mut LeanObject,
    mut v___y_3485_: *mut LeanObject,
    mut v___y_3486_: *mut LeanObject,
    mut v___y_3487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3500_: u8 = 0;
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_newC_3483_);
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
                if lean_obj_tag(v___x_3490_) == 0 {
                    v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
                    lean_inc(v_a_3491_);
                    lean_dec_ref_known(v___x_3490_, 1);
                    v___x_3492_ = lean_unsigned_to_nat(1);
                    v___x_3493_ = lean_nat_add(v_minorIdx_3474_, v___x_3492_);
                    v___x_3494_ = lean_array_push(v_casesOnParams_3475_, v_newC_3483_);
                    v___x_3495_ = lean_array_push(v_recArgs_3476_, v_a_3491_);
                    v___x_3496_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg(v_motiveIds_3477_, v_mainMotiveId_3478_, v_unit_3479_, v_star_3480_, v_minorEntries_3481_, v___x_3493_, v___x_3494_, v___x_3495_, v_k_3482_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
                    return v___x_3496_;
                } else {
                    lean_dec_ref(v_newC_3483_);
                    lean_dec_ref(v_k_3482_);
                    lean_dec_ref(v_minorEntries_3481_);
                    lean_dec_ref(v_star_3480_);
                    lean_dec_ref(v_unit_3479_);
                    lean_dec(v_mainMotiveId_3478_);
                    lean_dec_ref(v_motiveIds_3477_);
                    lean_dec_ref(v_recArgs_3476_);
                    lean_dec_ref(v_casesOnParams_3475_);
                    v_a_3497_ = lean_ctor_get(v___x_3490_, 0);
                    v_isSharedCheck_3504_ = (!lean_is_exclusive(v___x_3490_)) as u8;
                    if v_isSharedCheck_3504_ == 0 {
                        v___x_3499_ = v___x_3490_;
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3497_);
                        lean_dec(v___x_3490_);
                        v___x_3499_ = lean_box(0);
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
                    v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
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
    mut v_motiveIds_3505_: *mut LeanObject,
    mut v_mainMotiveId_3506_: *mut LeanObject,
    mut v_unit_3507_: *mut LeanObject,
    mut v_star_3508_: *mut LeanObject,
    mut v_minorEntries_3509_: *mut LeanObject,
    mut v_minorIdx_3510_: *mut LeanObject,
    mut v_casesOnParams_3511_: *mut LeanObject,
    mut v_recArgs_3512_: *mut LeanObject,
    mut v_k_3513_: *mut LeanObject,
    mut v_a_3514_: *mut LeanObject,
    mut v_a_3515_: *mut LeanObject,
    mut v_a_3516_: *mut LeanObject,
    mut v_a_3517_: *mut LeanObject,
    mut v_a_3518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3519_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3517_);
    lean_dec_ref(v_a_3516_);
    lean_dec(v_a_3515_);
    lean_dec_ref(v_a_3514_);
    return v_res_3519_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors(
    mut v_00_u03b1_3520_: *mut LeanObject,
    mut v_indNames_3521_: *mut LeanObject,
    mut v_numParams_3522_: *mut LeanObject,
    mut v_numMotives_3523_: *mut LeanObject,
    mut v_numMinors_3524_: *mut LeanObject,
    mut v_recFVars_3525_: *mut LeanObject,
    mut v_motiveIds_3526_: *mut LeanObject,
    mut v_mainMotiveId_3527_: *mut LeanObject,
    mut v_unit_3528_: *mut LeanObject,
    mut v_star_3529_: *mut LeanObject,
    mut v_minorEntries_3530_: *mut LeanObject,
    mut v_minorIdx_3531_: *mut LeanObject,
    mut v_casesOnParams_3532_: *mut LeanObject,
    mut v_recArgs_3533_: *mut LeanObject,
    mut v_k_3534_: *mut LeanObject,
    mut v_a_3535_: *mut LeanObject,
    mut v_a_3536_: *mut LeanObject,
    mut v_a_3537_: *mut LeanObject,
    mut v_a_3538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03b1_3541_: *mut LeanObject = *_args.add(0);
    let mut v_indNames_3542_: *mut LeanObject = *_args.add(1);
    let mut v_numParams_3543_: *mut LeanObject = *_args.add(2);
    let mut v_numMotives_3544_: *mut LeanObject = *_args.add(3);
    let mut v_numMinors_3545_: *mut LeanObject = *_args.add(4);
    let mut v_recFVars_3546_: *mut LeanObject = *_args.add(5);
    let mut v_motiveIds_3547_: *mut LeanObject = *_args.add(6);
    let mut v_mainMotiveId_3548_: *mut LeanObject = *_args.add(7);
    let mut v_unit_3549_: *mut LeanObject = *_args.add(8);
    let mut v_star_3550_: *mut LeanObject = *_args.add(9);
    let mut v_minorEntries_3551_: *mut LeanObject = *_args.add(10);
    let mut v_minorIdx_3552_: *mut LeanObject = *_args.add(11);
    let mut v_casesOnParams_3553_: *mut LeanObject = *_args.add(12);
    let mut v_recArgs_3554_: *mut LeanObject = *_args.add(13);
    let mut v_k_3555_: *mut LeanObject = *_args.add(14);
    let mut v_a_3556_: *mut LeanObject = *_args.add(15);
    let mut v_a_3557_: *mut LeanObject = *_args.add(16);
    let mut v_a_3558_: *mut LeanObject = *_args.add(17);
    let mut v_a_3559_: *mut LeanObject = *_args.add(18);
    let mut v_a_3560_: *mut LeanObject = *_args.add(19);
    let mut v_res_3561_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3559_);
    lean_dec_ref(v_a_3558_);
    lean_dec(v_a_3557_);
    lean_dec_ref(v_a_3556_);
    lean_dec_ref(v_recFVars_3546_);
    lean_dec(v_numMinors_3545_);
    lean_dec(v_numMotives_3544_);
    lean_dec(v_numParams_3543_);
    lean_dec_ref(v_indNames_3542_);
    return v_res_3561_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8___redArg(
    mut v_name_3562_: *mut LeanObject,
    mut v_levelParams_3563_: *mut LeanObject,
    mut v_type_3564_: *mut LeanObject,
    mut v_value_3565_: *mut LeanObject,
    mut v_hints_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: u8 = 0;
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3578_: u8 = 0;
    let mut v___x_3579_: u8 = 0;
    let mut v___x_3580_: u8 = 0;
    let mut v_env_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: u8 = 0;
    let mut v___x_3583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3569_ = lean_st_ref_get(v___y_3567_);
                v_env_3581_ = lean_ctor_get(v___x_3569_, 0);
                lean_inc_ref_n(v_env_3581_, 2);
                lean_dec(v___x_3569_);
                v___x_3582_ = l_Lean_Environment_hasUnsafe(v_env_3581_, v_type_3564_);
                if v___x_3582_ == 0 {
                    v___x_3583_ = l_Lean_Environment_hasUnsafe(v_env_3581_, v_value_3565_);
                    v___y_3578_ = v___x_3583_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_env_3581_);
                    v___y_3578_ = v___x_3582_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                lean_inc(v_name_3562_);
                v___x_3572_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3572_, 0, v_name_3562_);
                lean_ctor_set(v___x_3572_, 1, v_levelParams_3563_);
                lean_ctor_set(v___x_3572_, 2, v_type_3564_);
                v___x_3573_ = lean_box(0);
                v___x_3574_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3574_, 0, v_name_3562_);
                lean_ctor_set(v___x_3574_, 1, v___x_3573_);
                v___x_3575_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_3575_, 0, v___x_3572_);
                lean_ctor_set(v___x_3575_, 1, v_value_3565_);
                lean_ctor_set(v___x_3575_, 2, v_hints_3566_);
                lean_ctor_set(v___x_3575_, 3, v___x_3574_);
                lean_ctor_set_uint8(
                    v___x_3575_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___y_3571_,
                );
                v___x_3576_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3576_, 0, v___x_3575_);
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
    mut v_name_3584_: *mut LeanObject,
    mut v_levelParams_3585_: *mut LeanObject,
    mut v_type_3586_: *mut LeanObject,
    mut v_value_3587_: *mut LeanObject,
    mut v_hints_3588_: *mut LeanObject,
    mut v___y_3589_: *mut LeanObject,
    mut v___y_3590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3591_: *mut LeanObject = core::ptr::null_mut();
    v_res_3591_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8___redArg(v_name_3584_, v_levelParams_3585_, v_type_3586_, v_value_3587_, v_hints_3588_, v___y_3589_);
    lean_dec(v___y_3589_);
    return v_res_3591_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8(
    mut v_name_3592_: *mut LeanObject,
    mut v_levelParams_3593_: *mut LeanObject,
    mut v_type_3594_: *mut LeanObject,
    mut v_value_3595_: *mut LeanObject,
    mut v_hints_3596_: *mut LeanObject,
    mut v___y_3597_: *mut LeanObject,
    mut v___y_3598_: *mut LeanObject,
    mut v___y_3599_: *mut LeanObject,
    mut v___y_3600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    v___x_3602_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8___redArg(v_name_3592_, v_levelParams_3593_, v_type_3594_, v_value_3595_, v_hints_3596_, v___y_3600_);
    return v___x_3602_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8___boxed(
    mut v_name_3603_: *mut LeanObject,
    mut v_levelParams_3604_: *mut LeanObject,
    mut v_type_3605_: *mut LeanObject,
    mut v_value_3606_: *mut LeanObject,
    mut v_hints_3607_: *mut LeanObject,
    mut v___y_3608_: *mut LeanObject,
    mut v___y_3609_: *mut LeanObject,
    mut v___y_3610_: *mut LeanObject,
    mut v___y_3611_: *mut LeanObject,
    mut v___y_3612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3613_: *mut LeanObject = core::ptr::null_mut();
    v_res_3613_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8(v_name_3603_, v_levelParams_3604_, v_type_3605_, v_value_3606_, v_hints_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
    lean_dec(v___y_3611_);
    lean_dec_ref(v___y_3610_);
    lean_dec(v___y_3609_);
    lean_dec_ref(v___y_3608_);
    return v_res_3613_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg___lam__0(
    mut v_k_3614_: *mut LeanObject,
    mut v_b_3615_: *mut LeanObject,
    mut v_c_3616_: *mut LeanObject,
    mut v___y_3617_: *mut LeanObject,
    mut v___y_3618_: *mut LeanObject,
    mut v___y_3619_: *mut LeanObject,
    mut v___y_3620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3620_);
    lean_inc_ref(v___y_3619_);
    lean_inc(v___y_3618_);
    lean_inc_ref(v___y_3617_);
    v___x_3622_ = lean_apply_7(
        v_k_3614_,
        v_b_3615_,
        v_c_3616_,
        v___y_3617_,
        v___y_3618_,
        v___y_3619_,
        v___y_3620_,
        lean_box(0),
    );
    return v___x_3622_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg___lam__0___boxed(
    mut v_k_3623_: *mut LeanObject,
    mut v_b_3624_: *mut LeanObject,
    mut v_c_3625_: *mut LeanObject,
    mut v___y_3626_: *mut LeanObject,
    mut v___y_3627_: *mut LeanObject,
    mut v___y_3628_: *mut LeanObject,
    mut v___y_3629_: *mut LeanObject,
    mut v___y_3630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3631_: *mut LeanObject = core::ptr::null_mut();
    v_res_3631_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg___lam__0(v_k_3623_, v_b_3624_, v_c_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
    lean_dec(v___y_3629_);
    lean_dec_ref(v___y_3628_);
    lean_dec(v___y_3627_);
    lean_dec_ref(v___y_3626_);
    return v_res_3631_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg(
    mut v_type_3632_: *mut LeanObject,
    mut v_k_3633_: *mut LeanObject,
    mut v_cleanupAnnotations_3634_: u8,
    mut v___y_3635_: *mut LeanObject,
    mut v___y_3636_: *mut LeanObject,
    mut v___y_3637_: *mut LeanObject,
    mut v___y_3638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3647_: u8 = 0;
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3651_: u8 = 0;
    let mut v_a_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3655_: u8 = 0;
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3640_ = lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_3640_, 0, v_k_3633_);
                v___x_3641_ = 0;
                v___x_3642_ = lean_box(0);
                v___x_3643_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        lean_box(0),
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
                if lean_obj_tag(v___x_3643_) == 0 {
                    v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
                    v_isSharedCheck_3651_ = (!lean_is_exclusive(v___x_3643_)) as u8;
                    if v_isSharedCheck_3651_ == 0 {
                        v___x_3646_ = v___x_3643_;
                        v_isShared_3647_ = v_isSharedCheck_3651_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3644_);
                        lean_dec(v___x_3643_);
                        v___x_3646_ = lean_box(0);
                        v_isShared_3647_ = v_isSharedCheck_3651_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3652_ = lean_ctor_get(v___x_3643_, 0);
                    v_isSharedCheck_3659_ = (!lean_is_exclusive(v___x_3643_)) as u8;
                    if v_isSharedCheck_3659_ == 0 {
                        v___x_3654_ = v___x_3643_;
                        v_isShared_3655_ = v_isSharedCheck_3659_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3652_);
                        lean_dec(v___x_3643_);
                        v___x_3654_ = lean_box(0);
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
                    v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
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
                    v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
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
    mut v_type_3660_: *mut LeanObject,
    mut v_k_3661_: *mut LeanObject,
    mut v_cleanupAnnotations_3662_: *mut LeanObject,
    mut v___y_3663_: *mut LeanObject,
    mut v___y_3664_: *mut LeanObject,
    mut v___y_3665_: *mut LeanObject,
    mut v___y_3666_: *mut LeanObject,
    mut v___y_3667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3668_: u8 = 0;
    let mut v_res_3669_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3668_ = (lean_unbox(v_cleanupAnnotations_3662_) as u8);
    v_res_3669_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg(v_type_3660_, v_k_3661_, v_cleanupAnnotations_boxed_3668_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
    lean_dec(v___y_3666_);
    lean_dec_ref(v___y_3665_);
    lean_dec(v___y_3664_);
    lean_dec_ref(v___y_3663_);
    return v_res_3669_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12(
    mut v_00_u03b1_3670_: *mut LeanObject,
    mut v_type_3671_: *mut LeanObject,
    mut v_k_3672_: *mut LeanObject,
    mut v_cleanupAnnotations_3673_: u8,
    mut v___y_3674_: *mut LeanObject,
    mut v___y_3675_: *mut LeanObject,
    mut v___y_3676_: *mut LeanObject,
    mut v___y_3677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    v___x_3679_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg(v_type_3671_, v_k_3672_, v_cleanupAnnotations_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
    return v___x_3679_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___boxed(
    mut v_00_u03b1_3680_: *mut LeanObject,
    mut v_type_3681_: *mut LeanObject,
    mut v_k_3682_: *mut LeanObject,
    mut v_cleanupAnnotations_3683_: *mut LeanObject,
    mut v___y_3684_: *mut LeanObject,
    mut v___y_3685_: *mut LeanObject,
    mut v___y_3686_: *mut LeanObject,
    mut v___y_3687_: *mut LeanObject,
    mut v___y_3688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3689_: u8 = 0;
    let mut v_res_3690_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3689_ = (lean_unbox(v_cleanupAnnotations_3683_) as u8);
    v_res_3690_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12(v_00_u03b1_3680_, v_type_3681_, v_k_3682_, v_cleanupAnnotations_boxed_3689_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
    lean_dec(v___y_3687_);
    lean_dec_ref(v___y_3686_);
    lean_dec(v___y_3685_);
    lean_dec_ref(v___y_3684_);
    return v_res_3690_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___redArg(
    mut v___x_3691_: *mut LeanObject,
    mut v___x_3692_: *mut LeanObject,
    mut v___x_3693_: *mut LeanObject,
    mut v_recFVars_3694_: *mut LeanObject,
    mut v_as_x27_3695_: *mut LeanObject,
    mut v_b_3696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3695_) == 0 {
                    v___x_3698_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3698_, 0, v_b_3696_);
                    return v___x_3698_;
                } else {
                    v_head_3699_ = lean_ctor_get(v_as_x27_3695_, 0);
                    v_tail_3700_ = lean_ctor_get(v_as_x27_3695_, 1);
                    v___x_3701_ = l_Lean_instInhabitedExpr;
                    v___x_3702_ = lean_nat_add(v___x_3691_, v___x_3692_);
                    v___x_3703_ = lean_nat_add(v___x_3702_, v___x_3693_);
                    lean_dec(v___x_3702_);
                    v___x_3704_ = lean_nat_add(v___x_3703_, v_head_3699_);
                    lean_dec(v___x_3703_);
                    v___x_3705_ =
                        lean_array_get_borrowed(v___x_3701_, v_recFVars_3694_, v___x_3704_);
                    lean_dec(v___x_3704_);
                    lean_inc(v___x_3705_);
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
    mut v___x_3708_: *mut LeanObject,
    mut v___x_3709_: *mut LeanObject,
    mut v___x_3710_: *mut LeanObject,
    mut v_recFVars_3711_: *mut LeanObject,
    mut v_as_x27_3712_: *mut LeanObject,
    mut v_b_3713_: *mut LeanObject,
    mut v___y_3714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3715_: *mut LeanObject = core::ptr::null_mut();
    v_res_3715_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___redArg(v___x_3708_, v___x_3709_, v___x_3710_, v_recFVars_3711_, v_as_x27_3712_, v_b_3713_);
    lean_dec(v_as_x27_3712_);
    lean_dec_ref(v_recFVars_3711_);
    lean_dec(v___x_3710_);
    lean_dec(v___x_3709_);
    lean_dec(v___x_3708_);
    return v_res_3715_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__0(
    mut v_numParams_3716_: *mut LeanObject,
    mut v_numMotives_3717_: *mut LeanObject,
    mut v_numMinors_3718_: *mut LeanObject,
    mut v_recFVars_3719_: *mut LeanObject,
    mut v___x_3720_: *mut LeanObject,
    mut v_recType_3721_: *mut LeanObject,
    mut v___x_3722_: u8,
    mut v___x_3723_: *mut LeanObject,
    mut v___x_3724_: *mut LeanObject,
    mut v___x_3725_: *mut LeanObject,
    mut v_casesOnParams_3726_: *mut LeanObject,
    mut v_recArgs_3727_: *mut LeanObject,
    mut v___y_3728_: *mut LeanObject,
    mut v___y_3729_: *mut LeanObject,
    mut v___y_3730_: *mut LeanObject,
    mut v___y_3731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3737_: u8 = 0;
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3750_: u8 = 0;
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3757_: u8 = 0;
    let mut v_a_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3761_: u8 = 0;
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3765_: u8 = 0;
    let mut v_a_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3769_: u8 = 0;
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3773_: u8 = 0;
    let mut v_isSharedCheck_3774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3733_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___redArg(v_numParams_3716_, v_numMotives_3717_, v_numMinors_3718_, v_recFVars_3719_, v___x_3720_, v_recArgs_3727_);
                v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
                v_isSharedCheck_3774_ = (!lean_is_exclusive(v___x_3733_)) as u8;
                if v_isSharedCheck_3774_ == 0 {
                    v___x_3736_ = v___x_3733_;
                    v_isShared_3737_ = v_isSharedCheck_3774_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3734_);
                    lean_dec(v___x_3733_);
                    v___x_3736_ = lean_box(0);
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
                if lean_obj_tag(v___x_3740_) == 0 {
                    v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
                    lean_inc(v_a_3741_);
                    lean_dec_ref_known(v___x_3740_, 1);
                    v___x_3742_ = l_Lean_mkAppN(v___x_3723_, v_a_3734_);
                    lean_dec(v_a_3734_);
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
                    if lean_obj_tag(v___x_3743_) == 0 {
                        v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
                        lean_inc(v_a_3744_);
                        lean_dec_ref_known(v___x_3743_, 1);
                        v___x_3745_ = lean_box(1);
                        v___x_3746_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8___redArg(v___x_3724_, v___x_3725_, v_a_3741_, v_a_3744_, v___x_3745_, v___y_3731_);
                        v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
                        v_isSharedCheck_3757_ = (!lean_is_exclusive(v___x_3746_)) as u8;
                        if v_isSharedCheck_3757_ == 0 {
                            v___x_3749_ = v___x_3746_;
                            v_isShared_3750_ = v_isSharedCheck_3757_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3747_);
                            lean_dec(v___x_3746_);
                            v___x_3749_ = lean_box(0);
                            v_isShared_3750_ = v_isSharedCheck_3757_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3741_);
                        lean_del_object(v___x_3736_);
                        lean_dec(v___x_3725_);
                        lean_dec(v___x_3724_);
                        v_a_3758_ = lean_ctor_get(v___x_3743_, 0);
                        v_isSharedCheck_3765_ = (!lean_is_exclusive(v___x_3743_)) as u8;
                        if v_isSharedCheck_3765_ == 0 {
                            v___x_3760_ = v___x_3743_;
                            v_isShared_3761_ = v_isSharedCheck_3765_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3758_);
                            lean_dec(v___x_3743_);
                            v___x_3760_ = lean_box(0);
                            v_isShared_3761_ = v_isSharedCheck_3765_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3736_);
                    lean_dec(v_a_3734_);
                    lean_dec(v___x_3725_);
                    lean_dec(v___x_3724_);
                    lean_dec_ref(v___x_3723_);
                    v_a_3766_ = lean_ctor_get(v___x_3740_, 0);
                    v_isSharedCheck_3773_ = (!lean_is_exclusive(v___x_3740_)) as u8;
                    if v_isSharedCheck_3773_ == 0 {
                        v___x_3768_ = v___x_3740_;
                        v_isShared_3769_ = v_isSharedCheck_3773_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3766_);
                        lean_dec(v___x_3740_);
                        v___x_3768_ = lean_box(0);
                        v_isShared_3769_ = v_isSharedCheck_3773_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3737_ == 0 {
                    lean_ctor_set_tag(v___x_3736_, 1);
                    lean_ctor_set(v___x_3736_, 0, v_a_3747_);
                    v___x_3752_ = v___x_3736_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3747_);
                    v___x_3752_ = v_reuseFailAlloc_3756_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3750_ == 0 {
                    lean_ctor_set(v___x_3749_, 0, v___x_3752_);
                    v___x_3754_ = v___x_3749_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3752_);
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
                    v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3758_);
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
                    v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numParams_3775_: *mut LeanObject = *_args.add(0);
    let mut v_numMotives_3776_: *mut LeanObject = *_args.add(1);
    let mut v_numMinors_3777_: *mut LeanObject = *_args.add(2);
    let mut v_recFVars_3778_: *mut LeanObject = *_args.add(3);
    let mut v___x_3779_: *mut LeanObject = *_args.add(4);
    let mut v_recType_3780_: *mut LeanObject = *_args.add(5);
    let mut v___x_3781_: *mut LeanObject = *_args.add(6);
    let mut v___x_3782_: *mut LeanObject = *_args.add(7);
    let mut v___x_3783_: *mut LeanObject = *_args.add(8);
    let mut v___x_3784_: *mut LeanObject = *_args.add(9);
    let mut v_casesOnParams_3785_: *mut LeanObject = *_args.add(10);
    let mut v_recArgs_3786_: *mut LeanObject = *_args.add(11);
    let mut v___y_3787_: *mut LeanObject = *_args.add(12);
    let mut v___y_3788_: *mut LeanObject = *_args.add(13);
    let mut v___y_3789_: *mut LeanObject = *_args.add(14);
    let mut v___y_3790_: *mut LeanObject = *_args.add(15);
    let mut v___y_3791_: *mut LeanObject = *_args.add(16);
    let mut v___x_12918__boxed_3792_: u8 = 0;
    let mut v_res_3793_: *mut LeanObject = core::ptr::null_mut();
    v___x_12918__boxed_3792_ = (lean_unbox(v___x_3781_) as u8);
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
    lean_dec(v___y_3790_);
    lean_dec_ref(v___y_3789_);
    lean_dec(v___y_3788_);
    lean_dec_ref(v___y_3787_);
    lean_dec_ref(v_casesOnParams_3785_);
    lean_dec(v___x_3779_);
    lean_dec_ref(v_recFVars_3778_);
    lean_dec(v_numMinors_3777_);
    lean_dec(v_numMotives_3776_);
    lean_dec(v_numParams_3775_);
    return v_res_3793_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10___redArg(
    mut v___x_3794_: *mut LeanObject,
    mut v___x_3795_: *mut LeanObject,
    mut v_recFVars_3796_: *mut LeanObject,
    mut v_as_x27_3797_: *mut LeanObject,
    mut v_b_3798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: u8 = 0;
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3797_) == 0 {
                    v___x_3800_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3800_, 0, v_b_3798_);
                    return v___x_3800_;
                } else {
                    v_tail_3801_ = lean_ctor_get(v_as_x27_3797_, 1);
                    v_fst_3802_ = lean_ctor_get(v_b_3798_, 0);
                    v_snd_3803_ = lean_ctor_get(v_b_3798_, 1);
                    v_isSharedCheck_3821_ = (!lean_is_exclusive(v_b_3798_)) as u8;
                    if v_isSharedCheck_3821_ == 0 {
                        v___x_3805_ = v_b_3798_;
                        v_isShared_3806_ = v_isSharedCheck_3821_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3803_);
                        lean_inc(v_fst_3802_);
                        lean_dec(v_b_3798_);
                        v___x_3805_ = lean_box(0);
                        v_isShared_3806_ = v_isSharedCheck_3821_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3807_ = l_Lean_instInhabitedExpr;
                v___x_3808_ = lean_unsigned_to_nat(1);
                v___x_3809_ = lean_nat_add(v___x_3794_, v___x_3795_);
                v___x_3810_ = lean_nat_add(v___x_3809_, v_snd_3803_);
                lean_dec(v___x_3809_);
                v___x_3811_ = lean_array_get_borrowed(v___x_3807_, v_recFVars_3796_, v___x_3810_);
                lean_dec(v___x_3810_);
                v___x_3812_ = 0;
                v___x_3813_ = lean_box((v___x_3812_) as usize);
                lean_inc(v___x_3811_);
                if v_isShared_3806_ == 0 {
                    lean_ctor_set(v___x_3805_, 1, v___x_3813_);
                    lean_ctor_set(v___x_3805_, 0, v___x_3811_);
                    v___x_3815_ = v___x_3805_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3811_);
                    lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___x_3813_);
                    v___x_3815_ = v_reuseFailAlloc_3820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3816_ = lean_array_push(v_fst_3802_, v___x_3815_);
                v___x_3817_ = lean_nat_add(v_snd_3803_, v___x_3808_);
                lean_dec(v_snd_3803_);
                v___x_3818_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3818_, 0, v___x_3816_);
                lean_ctor_set(v___x_3818_, 1, v___x_3817_);
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
    mut v___x_3822_: *mut LeanObject,
    mut v___x_3823_: *mut LeanObject,
    mut v_recFVars_3824_: *mut LeanObject,
    mut v_as_x27_3825_: *mut LeanObject,
    mut v_b_3826_: *mut LeanObject,
    mut v___y_3827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3828_: *mut LeanObject = core::ptr::null_mut();
    v_res_3828_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10___redArg(v___x_3822_, v___x_3823_, v_recFVars_3824_, v_as_x27_3825_, v_b_3826_);
    lean_dec(v_as_x27_3825_);
    lean_dec_ref(v_recFVars_3824_);
    lean_dec(v___x_3823_);
    lean_dec(v___x_3822_);
    return v_res_3828_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6___redArg(
    mut v___x_3829_: *mut LeanObject,
    mut v___x_3830_: *mut LeanObject,
    mut v_recFVars_3831_: *mut LeanObject,
    mut v_a_3832_: *mut LeanObject,
    mut v_declName_3833_: *mut LeanObject,
    mut v_as_x27_3834_: *mut LeanObject,
    mut v_b_3835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: u8 = 0;
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3834_) == 0 {
                    v___x_3837_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3837_, 0, v_b_3835_);
                    return v___x_3837_;
                } else {
                    v_tail_3838_ = lean_ctor_get(v_as_x27_3834_, 1);
                    v_fst_3839_ = lean_ctor_get(v_b_3835_, 0);
                    v_snd_3840_ = lean_ctor_get(v_b_3835_, 1);
                    v_isSharedCheck_3858_ = (!lean_is_exclusive(v_b_3835_)) as u8;
                    if v_isSharedCheck_3858_ == 0 {
                        v___x_3842_ = v_b_3835_;
                        v_isShared_3843_ = v_isSharedCheck_3858_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3840_);
                        lean_inc(v_fst_3839_);
                        lean_dec(v_b_3835_);
                        v___x_3842_ = lean_box(0);
                        v_isShared_3843_ = v_isSharedCheck_3858_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3844_ = l_Lean_instInhabitedExpr;
                v___x_3845_ = lean_unsigned_to_nat(1);
                v___x_3846_ = lean_nat_add(v___x_3829_, v___x_3830_);
                v___x_3847_ = lean_nat_add(v___x_3846_, v_snd_3840_);
                lean_dec(v___x_3846_);
                v___x_3848_ = lean_array_get_borrowed(v___x_3844_, v_recFVars_3831_, v___x_3847_);
                lean_dec(v___x_3847_);
                v___x_3849_ = lean_name_eq(v_a_3832_, v_declName_3833_);
                v___x_3850_ = lean_box((v___x_3849_) as usize);
                lean_inc(v___x_3848_);
                if v_isShared_3843_ == 0 {
                    lean_ctor_set(v___x_3842_, 1, v___x_3850_);
                    lean_ctor_set(v___x_3842_, 0, v___x_3848_);
                    v___x_3852_ = v___x_3842_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3848_);
                    lean_ctor_set(v_reuseFailAlloc_3857_, 1, v___x_3850_);
                    v___x_3852_ = v_reuseFailAlloc_3857_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3853_ = lean_array_push(v_fst_3839_, v___x_3852_);
                v___x_3854_ = lean_nat_add(v_snd_3840_, v___x_3845_);
                lean_dec(v_snd_3840_);
                v___x_3855_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3855_, 0, v___x_3853_);
                lean_ctor_set(v___x_3855_, 1, v___x_3854_);
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
    mut v___x_3859_: *mut LeanObject,
    mut v___x_3860_: *mut LeanObject,
    mut v_recFVars_3861_: *mut LeanObject,
    mut v_a_3862_: *mut LeanObject,
    mut v_declName_3863_: *mut LeanObject,
    mut v_as_x27_3864_: *mut LeanObject,
    mut v_b_3865_: *mut LeanObject,
    mut v___y_3866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3867_: *mut LeanObject = core::ptr::null_mut();
    v_res_3867_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6___redArg(v___x_3859_, v___x_3860_, v_recFVars_3861_, v_a_3862_, v_declName_3863_, v_as_x27_3864_, v_b_3865_);
    lean_dec(v_as_x27_3864_);
    lean_dec(v_declName_3863_);
    lean_dec(v_a_3862_);
    lean_dec_ref(v_recFVars_3861_);
    lean_dec(v___x_3860_);
    lean_dec(v___x_3859_);
    return v_res_3867_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11_spec__13(
    mut v_msgData_3868_: *mut LeanObject,
    mut v___y_3869_: *mut LeanObject,
    mut v___y_3870_: *mut LeanObject,
    mut v___y_3871_: *mut LeanObject,
    mut v___y_3872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    v___x_3874_ = lean_st_ref_get(v___y_3872_);
    v_env_3875_ = lean_ctor_get(v___x_3874_, 0);
    lean_inc_ref(v_env_3875_);
    lean_dec(v___x_3874_);
    v___x_3876_ = lean_st_ref_get(v___y_3870_);
    v_mctx_3877_ = lean_ctor_get(v___x_3876_, 0);
    lean_inc_ref(v_mctx_3877_);
    lean_dec(v___x_3876_);
    v_lctx_3878_ = lean_ctor_get(v___y_3869_, 2);
    v_options_3879_ = lean_ctor_get(v___y_3871_, 2);
    lean_inc_ref(v_options_3879_);
    lean_inc_ref(v_lctx_3878_);
    v___x_3880_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3880_, 0, v_env_3875_);
    lean_ctor_set(v___x_3880_, 1, v_mctx_3877_);
    lean_ctor_set(v___x_3880_, 2, v_lctx_3878_);
    lean_ctor_set(v___x_3880_, 3, v_options_3879_);
    v___x_3881_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3881_, 0, v___x_3880_);
    lean_ctor_set(v___x_3881_, 1, v_msgData_3868_);
    v___x_3882_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3882_, 0, v___x_3881_);
    return v___x_3882_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11_spec__13___boxed(
    mut v_msgData_3883_: *mut LeanObject,
    mut v___y_3884_: *mut LeanObject,
    mut v___y_3885_: *mut LeanObject,
    mut v___y_3886_: *mut LeanObject,
    mut v___y_3887_: *mut LeanObject,
    mut v___y_3888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3889_: *mut LeanObject = core::ptr::null_mut();
    v_res_3889_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11_spec__13(v_msgData_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
    lean_dec(v___y_3887_);
    lean_dec_ref(v___y_3886_);
    lean_dec(v___y_3885_);
    lean_dec_ref(v___y_3884_);
    return v_res_3889_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(
    mut v_msg_3890_: *mut LeanObject,
    mut v___y_3891_: *mut LeanObject,
    mut v___y_3892_: *mut LeanObject,
    mut v___y_3893_: *mut LeanObject,
    mut v___y_3894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3896_ = lean_ctor_get(v___y_3893_, 5);
                v___x_3897_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11_spec__13(v_msg_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
                v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
                v_isSharedCheck_3906_ = (!lean_is_exclusive(v___x_3897_)) as u8;
                if v_isSharedCheck_3906_ == 0 {
                    v___x_3900_ = v___x_3897_;
                    v_isShared_3901_ = v_isSharedCheck_3906_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3898_);
                    lean_dec(v___x_3897_);
                    v___x_3900_ = lean_box(0);
                    v_isShared_3901_ = v_isSharedCheck_3906_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3896_);
                v___x_3902_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3902_, 0, v_ref_3896_);
                lean_ctor_set(v___x_3902_, 1, v_a_3898_);
                if v_isShared_3901_ == 0 {
                    lean_ctor_set_tag(v___x_3900_, 1);
                    lean_ctor_set(v___x_3900_, 0, v___x_3902_);
                    v___x_3904_ = v___x_3900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3902_);
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
    mut v_msg_3907_: *mut LeanObject,
    mut v___y_3908_: *mut LeanObject,
    mut v___y_3909_: *mut LeanObject,
    mut v___y_3910_: *mut LeanObject,
    mut v___y_3911_: *mut LeanObject,
    mut v___y_3912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3913_: *mut LeanObject = core::ptr::null_mut();
    v_res_3913_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(v_msg_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
    lean_dec(v___y_3911_);
    lean_dec_ref(v___y_3910_);
    lean_dec(v___y_3909_);
    lean_dec_ref(v___y_3908_);
    return v_res_3913_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    v___x_3915_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__0;
    v___x_3916_ = l_Lean_stringToMessageData(v___x_3915_);
    return v___x_3916_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    v___x_3918_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__2;
    v___x_3919_ = l_Lean_stringToMessageData(v___x_3918_);
    return v___x_3919_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0(
    mut v_constName_3920_: *mut LeanObject,
    mut v___y_3921_: *mut LeanObject,
    mut v___y_3922_: *mut LeanObject,
    mut v___y_3923_: *mut LeanObject,
    mut v___y_3924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: u8 = 0;
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3939_: u8 = 0;
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3926_ = lean_st_ref_get(v___y_3924_);
                v_env_3927_ = lean_ctor_get(v___x_3926_, 0);
                lean_inc_ref(v_env_3927_);
                lean_dec(v___x_3926_);
                lean_inc(v_constName_3920_);
                v___x_3928_ = l_Lean_isInductiveCore_x3f(v_env_3927_, v_constName_3920_);
                if lean_obj_tag(v___x_3928_) == 0 {
                    v___x_3929_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1);
                    v___x_3930_ = 0;
                    v___x_3931_ = l_Lean_MessageData_ofConstName(v_constName_3920_, v___x_3930_);
                    v___x_3932_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3932_, 0, v___x_3929_);
                    lean_ctor_set(v___x_3932_, 1, v___x_3931_);
                    v___x_3933_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__3_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__3);
                    v___x_3934_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3934_, 0, v___x_3932_);
                    lean_ctor_set(v___x_3934_, 1, v___x_3933_);
                    v___x_3935_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(v___x_3934_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
                    return v___x_3935_;
                } else {
                    lean_dec(v_constName_3920_);
                    v_val_3936_ = lean_ctor_get(v___x_3928_, 0);
                    v_isSharedCheck_3943_ = (!lean_is_exclusive(v___x_3928_)) as u8;
                    if v_isSharedCheck_3943_ == 0 {
                        v___x_3938_ = v___x_3928_;
                        v_isShared_3939_ = v_isSharedCheck_3943_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3936_);
                        lean_dec(v___x_3928_);
                        v___x_3938_ = lean_box(0);
                        v_isShared_3939_ = v_isSharedCheck_3943_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3939_ == 0 {
                    lean_ctor_set_tag(v___x_3938_, 0);
                    v___x_3941_ = v___x_3938_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_val_3936_);
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
    mut v_constName_3944_: *mut LeanObject,
    mut v___y_3945_: *mut LeanObject,
    mut v___y_3946_: *mut LeanObject,
    mut v___y_3947_: *mut LeanObject,
    mut v___y_3948_: *mut LeanObject,
    mut v___y_3949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3950_: *mut LeanObject = core::ptr::null_mut();
    v_res_3950_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0(v_constName_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
    lean_dec(v___y_3948_);
    lean_dec_ref(v___y_3947_);
    lean_dec(v___y_3946_);
    lean_dec_ref(v___y_3945_);
    return v_res_3950_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__9(
    mut v___x_3951_: *mut LeanObject,
    mut v___x_3952_: *mut LeanObject,
    mut v_recFVars_3953_: *mut LeanObject,
    mut v_declName_3954_: *mut LeanObject,
    mut v_as_3955_: *mut LeanObject,
    mut v_sz_3956_: usize,
    mut v_i_3957_: usize,
    mut v_b_3958_: *mut LeanObject,
    mut v___y_3959_: *mut LeanObject,
    mut v___y_3960_: *mut LeanObject,
    mut v___y_3961_: *mut LeanObject,
    mut v___y_3962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3964_: u8 = 0;
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3973_: u8 = 0;
    let mut v_ctors_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: usize = 0;
    let mut v___x_3987_: usize = 0;
    let mut v_reuseFailAlloc_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3990_: u8 = 0;
    let mut v_reuseFailAlloc_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3992_: u8 = 0;
    let mut v_a_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3996_: u8 = 0;
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3964_ = lean_usize_dec_lt(v_i_3957_, v_sz_3956_);
                if v___x_3964_ == 0 {
                    v___x_3965_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3965_, 0, v_b_3958_);
                    return v___x_3965_;
                } else {
                    v_a_3966_ = lean_array_uget_borrowed(v_as_3955_, v_i_3957_);
                    lean_inc(v_a_3966_);
                    v___x_3967_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0(v_a_3966_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
                    if lean_obj_tag(v___x_3967_) == 0 {
                        v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
                        lean_inc(v_a_3968_);
                        lean_dec_ref_known(v___x_3967_, 1);
                        v_fst_3969_ = lean_ctor_get(v_b_3958_, 0);
                        v_snd_3970_ = lean_ctor_get(v_b_3958_, 1);
                        v_isSharedCheck_3992_ = (!lean_is_exclusive(v_b_3958_)) as u8;
                        if v_isSharedCheck_3992_ == 0 {
                            v___x_3972_ = v_b_3958_;
                            v_isShared_3973_ = v_isSharedCheck_3992_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_3970_);
                            lean_inc(v_fst_3969_);
                            lean_dec(v_b_3958_);
                            v___x_3972_ = lean_box(0);
                            v_isShared_3973_ = v_isSharedCheck_3992_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_3958_);
                        v_a_3993_ = lean_ctor_get(v___x_3967_, 0);
                        v_isSharedCheck_4000_ = (!lean_is_exclusive(v___x_3967_)) as u8;
                        if v_isSharedCheck_4000_ == 0 {
                            v___x_3995_ = v___x_3967_;
                            v_isShared_3996_ = v_isSharedCheck_4000_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3993_);
                            lean_dec(v___x_3967_);
                            v___x_3995_ = lean_box(0);
                            v_isShared_3996_ = v_isSharedCheck_4000_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_ctors_3974_ = lean_ctor_get(v_a_3968_, 4);
                lean_inc(v_ctors_3974_);
                lean_dec(v_a_3968_);
                if v_isShared_3973_ == 0 {
                    v___x_3976_ = v___x_3972_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_fst_3969_);
                    lean_ctor_set(v_reuseFailAlloc_3991_, 1, v_snd_3970_);
                    v___x_3976_ = v_reuseFailAlloc_3991_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3977_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6___redArg(v___x_3951_, v___x_3952_, v_recFVars_3953_, v_a_3966_, v_declName_3954_, v_ctors_3974_, v___x_3976_);
                lean_dec(v_ctors_3974_);
                if lean_obj_tag(v___x_3977_) == 0 {
                    v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
                    lean_inc(v_a_3978_);
                    lean_dec_ref_known(v___x_3977_, 1);
                    v_fst_3979_ = lean_ctor_get(v_a_3978_, 0);
                    v_snd_3980_ = lean_ctor_get(v_a_3978_, 1);
                    v_isSharedCheck_3990_ = (!lean_is_exclusive(v_a_3978_)) as u8;
                    if v_isSharedCheck_3990_ == 0 {
                        v___x_3982_ = v_a_3978_;
                        v_isShared_3983_ = v_isSharedCheck_3990_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_3980_);
                        lean_inc(v_fst_3979_);
                        lean_dec(v_a_3978_);
                        v___x_3982_ = lean_box(0);
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
                    v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_fst_3979_);
                    lean_ctor_set(v_reuseFailAlloc_3989_, 1, v_snd_3980_);
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
                    v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
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
    mut v___x_4001_: *mut LeanObject,
    mut v___x_4002_: *mut LeanObject,
    mut v_recFVars_4003_: *mut LeanObject,
    mut v_declName_4004_: *mut LeanObject,
    mut v_as_4005_: *mut LeanObject,
    mut v_sz_4006_: *mut LeanObject,
    mut v_i_4007_: *mut LeanObject,
    mut v_b_4008_: *mut LeanObject,
    mut v___y_4009_: *mut LeanObject,
    mut v___y_4010_: *mut LeanObject,
    mut v___y_4011_: *mut LeanObject,
    mut v___y_4012_: *mut LeanObject,
    mut v___y_4013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4014_: usize = 0;
    let mut v_i_boxed_4015_: usize = 0;
    let mut v_res_4016_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4014_ = lean_unbox_usize(v_sz_4006_);
    lean_dec(v_sz_4006_);
    v_i_boxed_4015_ = lean_unbox_usize(v_i_4007_);
    lean_dec(v_i_4007_);
    v_res_4016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__9(v___x_4001_, v___x_4002_, v_recFVars_4003_, v_declName_4004_, v_as_4005_, v_sz_boxed_4014_, v_i_boxed_4015_, v_b_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
    lean_dec(v___y_4012_);
    lean_dec_ref(v___y_4011_);
    lean_dec(v___y_4010_);
    lean_dec_ref(v___y_4009_);
    lean_dec_ref(v_as_4005_);
    lean_dec(v_declName_4004_);
    lean_dec_ref(v_recFVars_4003_);
    lean_dec(v___x_4002_);
    lean_dec(v___x_4001_);
    return v_res_4016_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5___redArg(
    mut v___x_4017_: *mut LeanObject,
    mut v_recFVars_4018_: *mut LeanObject,
    mut v___x_4019_: *mut LeanObject,
    mut v___x_4020_: *mut LeanObject,
    mut v_declName_4021_: *mut LeanObject,
    mut v_as_x27_4022_: *mut LeanObject,
    mut v_b_4023_: *mut LeanObject,
    mut v___y_4024_: *mut LeanObject,
    mut v___y_4025_: *mut LeanObject,
    mut v___y_4026_: *mut LeanObject,
    mut v___y_4027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4037_: u8 = 0;
    let mut v_fst_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v_fst_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4053_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4072_: u8 = 0;
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4076_: u8 = 0;
    let mut v_a_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4080_: u8 = 0;
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4084_: u8 = 0;
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: u8 = 0;
    let mut v_isSharedCheck_4103_: u8 = 0;
    let mut v_isSharedCheck_4104_: u8 = 0;
    let mut v_unused_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4106_: u8 = 0;
    let mut v_unused_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4022_) == 0 {
                    lean_dec_ref(v___x_4019_);
                    v___x_4029_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4029_, 0, v_b_4023_);
                    return v___x_4029_;
                } else {
                    v_snd_4030_ = lean_ctor_get(v_b_4023_, 1);
                    lean_inc(v_snd_4030_);
                    v_snd_4031_ = lean_ctor_get(v_snd_4030_, 1);
                    lean_inc(v_snd_4031_);
                    v_head_4032_ = lean_ctor_get(v_as_x27_4022_, 0);
                    v_tail_4033_ = lean_ctor_get(v_as_x27_4022_, 1);
                    v_fst_4034_ = lean_ctor_get(v_b_4023_, 0);
                    v_isSharedCheck_4106_ = (!lean_is_exclusive(v_b_4023_)) as u8;
                    if v_isSharedCheck_4106_ == 0 {
                        v_unused_4107_ = lean_ctor_get(v_b_4023_, 1);
                        lean_dec(v_unused_4107_);
                        v___x_4036_ = v_b_4023_;
                        v_isShared_4037_ = v_isSharedCheck_4106_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_4034_);
                        lean_dec(v_b_4023_);
                        v___x_4036_ = lean_box(0);
                        v_isShared_4037_ = v_isSharedCheck_4106_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4038_ = lean_ctor_get(v_snd_4030_, 0);
                v_isSharedCheck_4104_ = (!lean_is_exclusive(v_snd_4030_)) as u8;
                if v_isSharedCheck_4104_ == 0 {
                    v_unused_4105_ = lean_ctor_get(v_snd_4030_, 1);
                    lean_dec(v_unused_4105_);
                    v___x_4040_ = v_snd_4030_;
                    v_isShared_4041_ = v_isSharedCheck_4104_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fst_4038_);
                    lean_dec(v_snd_4030_);
                    v___x_4040_ = lean_box(0);
                    v_isShared_4041_ = v_isSharedCheck_4104_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_4042_ = lean_ctor_get(v_snd_4031_, 0);
                v_snd_4043_ = lean_ctor_get(v_snd_4031_, 1);
                v_isSharedCheck_4103_ = (!lean_is_exclusive(v_snd_4031_)) as u8;
                if v_isSharedCheck_4103_ == 0 {
                    v___x_4045_ = v_snd_4031_;
                    v_isShared_4046_ = v_isSharedCheck_4103_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_4043_);
                    lean_inc(v_fst_4042_);
                    lean_dec(v_snd_4031_);
                    v___x_4045_ = lean_box(0);
                    v_isShared_4046_ = v_isSharedCheck_4103_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4047_ = l_Lean_instInhabitedExpr;
                v___x_4048_ = lean_nat_add(v___x_4017_, v_head_4032_);
                v___x_4049_ = lean_array_get_borrowed(v___x_4047_, v_recFVars_4018_, v___x_4048_);
                lean_dec(v___x_4048_);
                v___x_4050_ = l_Lean_Expr_fvarId_x21(v___x_4049_);
                lean_inc(v___x_4050_);
                v___x_4051_ = lean_array_push(v_fst_4042_, v___x_4050_);
                v___x_4098_ = lean_array_get_size(v___x_4020_);
                v___x_4099_ = lean_nat_dec_lt(v_head_4032_, v___x_4098_);
                if v___x_4099_ == 0 {
                    v___y_4053_ = v___x_4099_;
                    state = 4;
                    continue;
                } else {
                    v___x_4100_ = lean_box(0);
                    v___x_4101_ = lean_array_get_borrowed(v___x_4100_, v___x_4020_, v_head_4032_);
                    v___x_4102_ = lean_name_eq(v___x_4101_, v_declName_4021_);
                    v___y_4053_ = v___x_4102_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_4053_ == 0 {
                    lean_dec(v___x_4050_);
                    lean_inc(v___y_4027_);
                    lean_inc_ref(v___y_4026_);
                    lean_inc(v___y_4025_);
                    lean_inc_ref(v___y_4024_);
                    lean_inc(v___x_4049_);
                    v___x_4054_ = lean_infer_type(
                        v___x_4049_,
                        v___y_4024_,
                        v___y_4025_,
                        v___y_4026_,
                        v___y_4027_,
                    );
                    if lean_obj_tag(v___x_4054_) == 0 {
                        v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
                        lean_inc(v_a_4055_);
                        lean_dec_ref_known(v___x_4054_, 1);
                        lean_inc_ref(v___x_4019_);
                        v___x_4056_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit(v_a_4055_, v___x_4019_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
                        if lean_obj_tag(v___x_4056_) == 0 {
                            v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
                            lean_inc(v_a_4057_);
                            lean_dec_ref_known(v___x_4056_, 1);
                            v___x_4058_ = lean_array_push(v_fst_4038_, v_a_4057_);
                            if v_isShared_4046_ == 0 {
                                lean_ctor_set(v___x_4045_, 0, v___x_4051_);
                                v___x_4060_ = v___x_4045_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4051_);
                                lean_ctor_set(v_reuseFailAlloc_4068_, 1, v_snd_4043_);
                                v___x_4060_ = v_reuseFailAlloc_4068_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_4051_);
                            lean_del_object(v___x_4045_);
                            lean_dec(v_snd_4043_);
                            lean_del_object(v___x_4040_);
                            lean_dec(v_fst_4038_);
                            lean_del_object(v___x_4036_);
                            lean_dec(v_fst_4034_);
                            lean_dec_ref(v___x_4019_);
                            v_a_4069_ = lean_ctor_get(v___x_4056_, 0);
                            v_isSharedCheck_4076_ = (!lean_is_exclusive(v___x_4056_)) as u8;
                            if v_isSharedCheck_4076_ == 0 {
                                v___x_4071_ = v___x_4056_;
                                v_isShared_4072_ = v_isSharedCheck_4076_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_4069_);
                                lean_dec(v___x_4056_);
                                v___x_4071_ = lean_box(0);
                                v_isShared_4072_ = v_isSharedCheck_4076_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_4051_);
                        lean_del_object(v___x_4045_);
                        lean_dec(v_snd_4043_);
                        lean_del_object(v___x_4040_);
                        lean_dec(v_fst_4038_);
                        lean_del_object(v___x_4036_);
                        lean_dec(v_fst_4034_);
                        lean_dec_ref(v___x_4019_);
                        v_a_4077_ = lean_ctor_get(v___x_4054_, 0);
                        v_isSharedCheck_4084_ = (!lean_is_exclusive(v___x_4054_)) as u8;
                        if v_isSharedCheck_4084_ == 0 {
                            v___x_4079_ = v___x_4054_;
                            v_isShared_4080_ = v_isSharedCheck_4084_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_4077_);
                            lean_dec(v___x_4054_);
                            v___x_4079_ = lean_box(0);
                            v_isShared_4080_ = v_isSharedCheck_4084_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_snd_4043_);
                    lean_inc_n(v___x_4049_, 2);
                    v___x_4085_ = lean_array_push(v_fst_4034_, v___x_4049_);
                    v___x_4086_ = lean_array_push(v_fst_4038_, v___x_4049_);
                    v___x_4087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4087_, 0, v___x_4050_);
                    if v_isShared_4046_ == 0 {
                        lean_ctor_set(v___x_4045_, 1, v___x_4087_);
                        lean_ctor_set(v___x_4045_, 0, v___x_4051_);
                        v___x_4089_ = v___x_4045_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4097_, 0, v___x_4051_);
                        lean_ctor_set(v_reuseFailAlloc_4097_, 1, v___x_4087_);
                        v___x_4089_ = v_reuseFailAlloc_4097_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4041_ == 0 {
                    lean_ctor_set(v___x_4040_, 1, v___x_4060_);
                    lean_ctor_set(v___x_4040_, 0, v___x_4058_);
                    v___x_4062_ = v___x_4040_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4058_);
                    lean_ctor_set(v_reuseFailAlloc_4067_, 1, v___x_4060_);
                    v___x_4062_ = v_reuseFailAlloc_4067_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4037_ == 0 {
                    lean_ctor_set(v___x_4036_, 1, v___x_4062_);
                    v___x_4064_ = v___x_4036_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_fst_4034_);
                    lean_ctor_set(v_reuseFailAlloc_4066_, 1, v___x_4062_);
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
                    v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
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
                    v_reuseFailAlloc_4083_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4077_);
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
                    lean_ctor_set(v___x_4040_, 1, v___x_4089_);
                    lean_ctor_set(v___x_4040_, 0, v___x_4086_);
                    v___x_4091_ = v___x_4040_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4086_);
                    lean_ctor_set(v_reuseFailAlloc_4096_, 1, v___x_4089_);
                    v___x_4091_ = v_reuseFailAlloc_4096_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4037_ == 0 {
                    lean_ctor_set(v___x_4036_, 1, v___x_4091_);
                    lean_ctor_set(v___x_4036_, 0, v___x_4085_);
                    v___x_4093_ = v___x_4036_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4085_);
                    lean_ctor_set(v_reuseFailAlloc_4095_, 1, v___x_4091_);
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
    mut v___x_4108_: *mut LeanObject,
    mut v_recFVars_4109_: *mut LeanObject,
    mut v___x_4110_: *mut LeanObject,
    mut v___x_4111_: *mut LeanObject,
    mut v_declName_4112_: *mut LeanObject,
    mut v_as_x27_4113_: *mut LeanObject,
    mut v_b_4114_: *mut LeanObject,
    mut v___y_4115_: *mut LeanObject,
    mut v___y_4116_: *mut LeanObject,
    mut v___y_4117_: *mut LeanObject,
    mut v___y_4118_: *mut LeanObject,
    mut v___y_4119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4120_: *mut LeanObject = core::ptr::null_mut();
    v_res_4120_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5___redArg(v___x_4108_, v_recFVars_4109_, v___x_4110_, v___x_4111_, v_declName_4112_, v_as_x27_4113_, v_b_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
    lean_dec(v___y_4118_);
    lean_dec_ref(v___y_4117_);
    lean_dec(v___y_4116_);
    lean_dec_ref(v___y_4115_);
    lean_dec(v_as_x27_4113_);
    lean_dec(v_declName_4112_);
    lean_dec_ref(v___x_4111_);
    lean_dec_ref(v_recFVars_4109_);
    lean_dec(v___x_4108_);
    return v_res_4120_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4___redArg(
    mut v_recFVars_4121_: *mut LeanObject,
    mut v_as_x27_4122_: *mut LeanObject,
    mut v_b_4123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4132_: u8 = 0;
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4122_) == 0 {
                    v___x_4125_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4125_, 0, v_b_4123_);
                    return v___x_4125_;
                } else {
                    v_head_4126_ = lean_ctor_get(v_as_x27_4122_, 0);
                    v_tail_4127_ = lean_ctor_get(v_as_x27_4122_, 1);
                    v_fst_4128_ = lean_ctor_get(v_b_4123_, 0);
                    v_snd_4129_ = lean_ctor_get(v_b_4123_, 1);
                    v_isSharedCheck_4141_ = (!lean_is_exclusive(v_b_4123_)) as u8;
                    if v_isSharedCheck_4141_ == 0 {
                        v___x_4131_ = v_b_4123_;
                        v_isShared_4132_ = v_isSharedCheck_4141_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4129_);
                        lean_inc(v_fst_4128_);
                        lean_dec(v_b_4123_);
                        v___x_4131_ = lean_box(0);
                        v_isShared_4132_ = v_isSharedCheck_4141_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4133_ = l_Lean_instInhabitedExpr;
                v___x_4134_ = lean_array_get_borrowed(v___x_4133_, v_recFVars_4121_, v_head_4126_);
                lean_inc_n(v___x_4134_, 2);
                v___x_4135_ = lean_array_push(v_fst_4128_, v___x_4134_);
                v___x_4136_ = lean_array_push(v_snd_4129_, v___x_4134_);
                if v_isShared_4132_ == 0 {
                    lean_ctor_set(v___x_4131_, 1, v___x_4136_);
                    lean_ctor_set(v___x_4131_, 0, v___x_4135_);
                    v___x_4138_ = v___x_4131_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4135_);
                    lean_ctor_set(v_reuseFailAlloc_4140_, 1, v___x_4136_);
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
    mut v_recFVars_4142_: *mut LeanObject,
    mut v_as_x27_4143_: *mut LeanObject,
    mut v_b_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4146_: *mut LeanObject = core::ptr::null_mut();
    v_res_4146_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4___redArg(v_recFVars_4142_, v_as_x27_4143_, v_b_4144_);
    lean_dec(v_as_x27_4143_);
    lean_dec_ref(v_recFVars_4142_);
    return v_res_4146_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__4()
-> *mut LeanObject {
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    v___x_4156_ =
        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__3;
    v___x_4157_ = l_Lean_stringToMessageData(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__6()
-> *mut LeanObject {
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    v___x_4159_ =
        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__5;
    v___x_4160_ = l_Lean_stringToMessageData(v___x_4159_);
    return v___x_4160_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__8()
-> *mut LeanObject {
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    v___x_4162_ =
        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__7;
    v___x_4163_ = l_Lean_stringToMessageData(v___x_4162_);
    return v___x_4163_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1(
    mut v_numParams_4164_: *mut LeanObject,
    mut v_numMotives_4165_: *mut LeanObject,
    mut v___x_4166_: *mut LeanObject,
    mut v___x_4167_: *mut LeanObject,
    mut v_declName_4168_: *mut LeanObject,
    mut v_numIndices_4169_: *mut LeanObject,
    mut v_numMinors_4170_: *mut LeanObject,
    mut v___x_4171_: u8,
    mut v___x_4172_: *mut LeanObject,
    mut v___x_4173_: *mut LeanObject,
    mut v___x_4174_: *mut LeanObject,
    mut v___x_4175_: *mut LeanObject,
    mut v_recFVars_4176_: *mut LeanObject,
    mut v_recType_4177_: *mut LeanObject,
    mut v___y_4178_: *mut LeanObject,
    mut v___y_4179_: *mut LeanObject,
    mut v___y_4180_: *mut LeanObject,
    mut v___y_4181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4213_: usize = 0;
    let mut v___x_4214_: usize = 0;
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4221_: u8 = 0;
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_a_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4237_: u8 = 0;
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4244_: u8 = 0;
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4247_: u8 = 0;
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4269_: u8 = 0;
    let mut v_unused_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut v_unused_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4275_: u8 = 0;
    let mut v_unused_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4281_: u8 = 0;
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4285_: u8 = 0;
    let mut v_reuseFailAlloc_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4183_ = lean_unsigned_to_nat(0);
                lean_inc(v_numParams_4164_);
                v___x_4184_ = l_List_range(v_numParams_4164_);
                v___x_4185_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__0;
                v___x_4186_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4___redArg(v_recFVars_4176_, v___x_4184_, v___x_4185_);
                lean_dec(v___x_4184_);
                v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
                lean_inc(v_a_4187_);
                lean_dec_ref(v___x_4186_);
                v_fst_4188_ = lean_ctor_get(v_a_4187_, 0);
                v_snd_4189_ = lean_ctor_get(v_a_4187_, 1);
                v_isSharedCheck_4287_ = (!lean_is_exclusive(v_a_4187_)) as u8;
                if v_isSharedCheck_4287_ == 0 {
                    v___x_4191_ = v_a_4187_;
                    v_isShared_4192_ = v_isSharedCheck_4287_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_4189_);
                    lean_inc(v_fst_4188_);
                    lean_dec(v_a_4187_);
                    v___x_4191_ = lean_box(0);
                    v_isShared_4192_ = v_isSharedCheck_4287_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_numMotives_4165_);
                v___x_4193_ = l_List_range(v_numMotives_4165_);
                v___x_4194_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__1;
                if v_isShared_4192_ == 0 {
                    lean_ctor_set(v___x_4191_, 1, v___x_4194_);
                    lean_ctor_set(v___x_4191_, 0, v_snd_4189_);
                    v___x_4196_ = v___x_4191_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4286_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_snd_4189_);
                    lean_ctor_set(v_reuseFailAlloc_4286_, 1, v___x_4194_);
                    v___x_4196_ = v_reuseFailAlloc_4286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4197_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4197_, 0, v_fst_4188_);
                lean_ctor_set(v___x_4197_, 1, v___x_4196_);
                lean_inc_ref(v___x_4166_);
                v___x_4198_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5___redArg(v_numParams_4164_, v_recFVars_4176_, v___x_4166_, v___x_4167_, v_declName_4168_, v___x_4193_, v___x_4197_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
                lean_dec(v___x_4193_);
                if lean_obj_tag(v___x_4198_) == 0 {
                    v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
                    lean_inc(v_a_4199_);
                    lean_dec_ref_known(v___x_4198_, 1);
                    v_snd_4200_ = lean_ctor_get(v_a_4199_, 1);
                    lean_inc(v_snd_4200_);
                    v_snd_4201_ = lean_ctor_get(v_snd_4200_, 1);
                    lean_inc(v_snd_4201_);
                    v_snd_4202_ = lean_ctor_get(v_snd_4201_, 1);
                    if lean_obj_tag(v_snd_4202_) == 1 {
                        lean_inc_ref(v_snd_4202_);
                        v_fst_4203_ = lean_ctor_get(v_a_4199_, 0);
                        lean_inc(v_fst_4203_);
                        lean_dec(v_a_4199_);
                        v_fst_4204_ = lean_ctor_get(v_snd_4200_, 0);
                        lean_inc(v_fst_4204_);
                        lean_dec(v_snd_4200_);
                        v_fst_4205_ = lean_ctor_get(v_snd_4201_, 0);
                        lean_inc(v_fst_4205_);
                        lean_dec(v_snd_4201_);
                        v_val_4206_ = lean_ctor_get(v_snd_4202_, 0);
                        lean_inc(v_val_4206_);
                        lean_dec_ref_known(v_snd_4202_, 1);
                        v___x_4207_ = lean_unsigned_to_nat(1);
                        v___x_4208_ = lean_nat_add(v_numIndices_4169_, v___x_4207_);
                        v___x_4209_ = l_List_range(v___x_4208_);
                        v___x_4210_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___redArg(v_numParams_4164_, v_numMotives_4165_, v_numMinors_4170_, v_recFVars_4176_, v___x_4209_, v_fst_4203_);
                        v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
                        lean_inc(v_a_4211_);
                        lean_dec_ref(v___x_4210_);
                        v___x_4212_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__2;
                        v_sz_4213_ = lean_array_size(v___x_4167_);
                        v___x_4214_ = 0usize;
                        v___x_4215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__9(v_numParams_4164_, v_numMotives_4165_, v_recFVars_4176_, v_declName_4168_, v___x_4167_, v_sz_4213_, v___x_4214_, v___x_4212_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
                        lean_dec(v_declName_4168_);
                        if lean_obj_tag(v___x_4215_) == 0 {
                            v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
                            lean_inc(v_a_4216_);
                            lean_dec_ref_known(v___x_4215_, 1);
                            v_fst_4217_ = lean_ctor_get(v_a_4216_, 0);
                            v_snd_4218_ = lean_ctor_get(v_a_4216_, 1);
                            v_isSharedCheck_4233_ = (!lean_is_exclusive(v_a_4216_)) as u8;
                            if v_isSharedCheck_4233_ == 0 {
                                v___x_4220_ = v_a_4216_;
                                v_isShared_4221_ = v_isSharedCheck_4233_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_snd_4218_);
                                lean_inc(v_fst_4217_);
                                lean_dec(v_a_4216_);
                                v___x_4220_ = lean_box(0);
                                v_isShared_4221_ = v_isSharedCheck_4233_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4211_);
                            lean_dec(v___x_4209_);
                            lean_dec(v_val_4206_);
                            lean_dec(v_fst_4205_);
                            lean_dec(v_fst_4204_);
                            lean_dec_ref(v_recType_4177_);
                            lean_dec_ref(v_recFVars_4176_);
                            lean_dec_ref(v___x_4175_);
                            lean_dec(v___x_4174_);
                            lean_dec(v___x_4173_);
                            lean_dec_ref(v___x_4172_);
                            lean_dec(v_numMinors_4170_);
                            lean_dec_ref(v___x_4166_);
                            lean_dec(v_numMotives_4165_);
                            lean_dec(v_numParams_4164_);
                            v_a_4234_ = lean_ctor_get(v___x_4215_, 0);
                            v_isSharedCheck_4241_ = (!lean_is_exclusive(v___x_4215_)) as u8;
                            if v_isSharedCheck_4241_ == 0 {
                                v___x_4236_ = v___x_4215_;
                                v_isShared_4237_ = v_isSharedCheck_4241_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4234_);
                                lean_dec(v___x_4215_);
                                v___x_4236_ = lean_box(0);
                                v_isShared_4237_ = v_isSharedCheck_4241_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_recType_4177_);
                        lean_dec_ref(v_recFVars_4176_);
                        lean_dec_ref(v___x_4175_);
                        lean_dec(v___x_4174_);
                        lean_dec(v___x_4173_);
                        lean_dec_ref(v___x_4172_);
                        lean_dec(v_numMinors_4170_);
                        lean_dec_ref(v___x_4166_);
                        lean_dec(v_numMotives_4165_);
                        lean_dec(v_numParams_4164_);
                        v_isSharedCheck_4275_ = (!lean_is_exclusive(v_a_4199_)) as u8;
                        if v_isSharedCheck_4275_ == 0 {
                            v_unused_4276_ = lean_ctor_get(v_a_4199_, 1);
                            lean_dec(v_unused_4276_);
                            v_unused_4277_ = lean_ctor_get(v_a_4199_, 0);
                            lean_dec(v_unused_4277_);
                            v___x_4243_ = v_a_4199_;
                            v_isShared_4244_ = v_isSharedCheck_4275_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v_a_4199_);
                            v___x_4243_ = lean_box(0);
                            v_isShared_4244_ = v_isSharedCheck_4275_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_recType_4177_);
                    lean_dec_ref(v_recFVars_4176_);
                    lean_dec_ref(v___x_4175_);
                    lean_dec(v___x_4174_);
                    lean_dec(v___x_4173_);
                    lean_dec_ref(v___x_4172_);
                    lean_dec(v_numMinors_4170_);
                    lean_dec(v_declName_4168_);
                    lean_dec_ref(v___x_4166_);
                    lean_dec(v_numMotives_4165_);
                    lean_dec(v_numParams_4164_);
                    v_a_4278_ = lean_ctor_get(v___x_4198_, 0);
                    v_isSharedCheck_4285_ = (!lean_is_exclusive(v___x_4198_)) as u8;
                    if v_isSharedCheck_4285_ == 0 {
                        v___x_4280_ = v___x_4198_;
                        v_isShared_4281_ = v_isSharedCheck_4285_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_4278_);
                        lean_dec(v___x_4198_);
                        v___x_4280_ = lean_box(0);
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
                    v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_fst_4217_);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 1, v_snd_4218_);
                    v___x_4225_ = v_reuseFailAlloc_4232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4226_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10___redArg(v_numParams_4164_, v_numMotives_4165_, v_recFVars_4176_, v___x_4223_, v___x_4225_);
                lean_dec(v___x_4223_);
                v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
                lean_inc(v_a_4227_);
                lean_dec_ref(v___x_4226_);
                v_fst_4228_ = lean_ctor_get(v_a_4227_, 0);
                lean_inc(v_fst_4228_);
                lean_dec(v_a_4227_);
                v___x_4229_ = lean_box((v___x_4171_) as usize);
                v___f_4230_ = lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__0___boxed as *mut core::ffi::c_void, 17, 10);
                lean_closure_set(v___f_4230_, 0, v_numParams_4164_);
                lean_closure_set(v___f_4230_, 1, v_numMotives_4165_);
                lean_closure_set(v___f_4230_, 2, v_numMinors_4170_);
                lean_closure_set(v___f_4230_, 3, v_recFVars_4176_);
                lean_closure_set(v___f_4230_, 4, v___x_4209_);
                lean_closure_set(v___f_4230_, 5, v_recType_4177_);
                lean_closure_set(v___f_4230_, 6, v___x_4229_);
                lean_closure_set(v___f_4230_, 7, v___x_4172_);
                lean_closure_set(v___f_4230_, 8, v___x_4173_);
                lean_closure_set(v___f_4230_, 9, v___x_4174_);
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
                    v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
                    v___x_4239_ = v_reuseFailAlloc_4240_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4239_;
            }
            7 => {
                v_isSharedCheck_4272_ = (!lean_is_exclusive(v_snd_4200_)) as u8;
                if v_isSharedCheck_4272_ == 0 {
                    v_unused_4273_ = lean_ctor_get(v_snd_4200_, 1);
                    lean_dec(v_unused_4273_);
                    v_unused_4274_ = lean_ctor_get(v_snd_4200_, 0);
                    lean_dec(v_unused_4274_);
                    v___x_4246_ = v_snd_4200_;
                    v_isShared_4247_ = v_isSharedCheck_4272_;
                    state = 8;
                    continue;
                } else {
                    lean_dec(v_snd_4200_);
                    v___x_4246_ = lean_box(0);
                    v_isShared_4247_ = v_isSharedCheck_4272_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_isSharedCheck_4269_ = (!lean_is_exclusive(v_snd_4201_)) as u8;
                if v_isSharedCheck_4269_ == 0 {
                    v_unused_4270_ = lean_ctor_get(v_snd_4201_, 1);
                    lean_dec(v_unused_4270_);
                    v_unused_4271_ = lean_ctor_get(v_snd_4201_, 0);
                    lean_dec(v_unused_4271_);
                    v___x_4249_ = v_snd_4201_;
                    v_isShared_4250_ = v_isSharedCheck_4269_;
                    state = 9;
                    continue;
                } else {
                    lean_dec(v_snd_4201_);
                    v___x_4249_ = lean_box(0);
                    v_isShared_4250_ = v_isSharedCheck_4269_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4251_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__4_once), _init_l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__4);
                v___x_4252_ = l_Lean_casesOnSuffix;
                lean_inc(v_declName_4168_);
                v___x_4253_ = l_Lean_Name_str___override(v_declName_4168_, v___x_4252_);
                v___x_4254_ = l_Lean_MessageData_ofName(v___x_4253_);
                if v_isShared_4250_ == 0 {
                    lean_ctor_set_tag(v___x_4249_, 7);
                    lean_ctor_set(v___x_4249_, 1, v___x_4254_);
                    lean_ctor_set(v___x_4249_, 0, v___x_4251_);
                    v___x_4256_ = v___x_4249_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4268_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4251_);
                    lean_ctor_set(v_reuseFailAlloc_4268_, 1, v___x_4254_);
                    v___x_4256_ = v_reuseFailAlloc_4268_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4257_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__6_once), _init_l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__6);
                if v_isShared_4247_ == 0 {
                    lean_ctor_set_tag(v___x_4246_, 7);
                    lean_ctor_set(v___x_4246_, 1, v___x_4257_);
                    lean_ctor_set(v___x_4246_, 0, v___x_4256_);
                    v___x_4259_ = v___x_4246_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4267_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4256_);
                    lean_ctor_set(v_reuseFailAlloc_4267_, 1, v___x_4257_);
                    v___x_4259_ = v_reuseFailAlloc_4267_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4260_ = l_Lean_MessageData_ofName(v_declName_4168_);
                if v_isShared_4244_ == 0 {
                    lean_ctor_set_tag(v___x_4243_, 7);
                    lean_ctor_set(v___x_4243_, 1, v___x_4260_);
                    lean_ctor_set(v___x_4243_, 0, v___x_4259_);
                    v___x_4262_ = v___x_4243_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4266_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4259_);
                    lean_ctor_set(v_reuseFailAlloc_4266_, 1, v___x_4260_);
                    v___x_4262_ = v_reuseFailAlloc_4266_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4263_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__8_once), _init_l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__8);
                v___x_4264_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4264_, 0, v___x_4262_);
                lean_ctor_set(v___x_4264_, 1, v___x_4263_);
                v___x_4265_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(v___x_4264_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
                return v___x_4265_;
            }
            13 => {
                if v_isShared_4281_ == 0 {
                    v___x_4283_ = v___x_4280_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numParams_4288_: *mut LeanObject = *_args.add(0);
    let mut v_numMotives_4289_: *mut LeanObject = *_args.add(1);
    let mut v___x_4290_: *mut LeanObject = *_args.add(2);
    let mut v___x_4291_: *mut LeanObject = *_args.add(3);
    let mut v_declName_4292_: *mut LeanObject = *_args.add(4);
    let mut v_numIndices_4293_: *mut LeanObject = *_args.add(5);
    let mut v_numMinors_4294_: *mut LeanObject = *_args.add(6);
    let mut v___x_4295_: *mut LeanObject = *_args.add(7);
    let mut v___x_4296_: *mut LeanObject = *_args.add(8);
    let mut v___x_4297_: *mut LeanObject = *_args.add(9);
    let mut v___x_4298_: *mut LeanObject = *_args.add(10);
    let mut v___x_4299_: *mut LeanObject = *_args.add(11);
    let mut v_recFVars_4300_: *mut LeanObject = *_args.add(12);
    let mut v_recType_4301_: *mut LeanObject = *_args.add(13);
    let mut v___y_4302_: *mut LeanObject = *_args.add(14);
    let mut v___y_4303_: *mut LeanObject = *_args.add(15);
    let mut v___y_4304_: *mut LeanObject = *_args.add(16);
    let mut v___y_4305_: *mut LeanObject = *_args.add(17);
    let mut v___y_4306_: *mut LeanObject = *_args.add(18);
    let mut v___x_13586__boxed_4307_: u8 = 0;
    let mut v_res_4308_: *mut LeanObject = core::ptr::null_mut();
    v___x_13586__boxed_4307_ = (lean_unbox(v___x_4295_) as u8);
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
    lean_dec(v___y_4305_);
    lean_dec_ref(v___y_4304_);
    lean_dec(v___y_4303_);
    lean_dec_ref(v___y_4302_);
    lean_dec(v_numIndices_4293_);
    lean_dec_ref(v___x_4291_);
    return v_res_4308_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18___redArg(
    mut v_ref_4309_: *mut LeanObject,
    mut v_msg_4310_: *mut LeanObject,
    mut v___y_4311_: *mut LeanObject,
    mut v___y_4312_: *mut LeanObject,
    mut v___y_4313_: *mut LeanObject,
    mut v___y_4314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4328_: u8 = 0;
    let mut v_cancelTk_x3f_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4330_: u8 = 0;
    let mut v_inheritedTraceOptions_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_4316_ = lean_ctor_get(v___y_4313_, 0);
    v_fileMap_4317_ = lean_ctor_get(v___y_4313_, 1);
    v_options_4318_ = lean_ctor_get(v___y_4313_, 2);
    v_currRecDepth_4319_ = lean_ctor_get(v___y_4313_, 3);
    v_maxRecDepth_4320_ = lean_ctor_get(v___y_4313_, 4);
    v_ref_4321_ = lean_ctor_get(v___y_4313_, 5);
    v_currNamespace_4322_ = lean_ctor_get(v___y_4313_, 6);
    v_openDecls_4323_ = lean_ctor_get(v___y_4313_, 7);
    v_initHeartbeats_4324_ = lean_ctor_get(v___y_4313_, 8);
    v_maxHeartbeats_4325_ = lean_ctor_get(v___y_4313_, 9);
    v_quotContext_4326_ = lean_ctor_get(v___y_4313_, 10);
    v_currMacroScope_4327_ = lean_ctor_get(v___y_4313_, 11);
    v_diag_4328_ = lean_ctor_get_uint8(
        v___y_4313_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4329_ = lean_ctor_get(v___y_4313_, 12);
    v_suppressElabErrors_4330_ = lean_ctor_get_uint8(
        v___y_4313_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4331_ = lean_ctor_get(v___y_4313_, 13);
    v_ref_4332_ = l_Lean_replaceRef(v_ref_4309_, v_ref_4321_);
    lean_inc_ref(v_inheritedTraceOptions_4331_);
    lean_inc(v_cancelTk_x3f_4329_);
    lean_inc(v_currMacroScope_4327_);
    lean_inc(v_quotContext_4326_);
    lean_inc(v_maxHeartbeats_4325_);
    lean_inc(v_initHeartbeats_4324_);
    lean_inc(v_openDecls_4323_);
    lean_inc(v_currNamespace_4322_);
    lean_inc(v_maxRecDepth_4320_);
    lean_inc(v_currRecDepth_4319_);
    lean_inc_ref(v_options_4318_);
    lean_inc_ref(v_fileMap_4317_);
    lean_inc_ref(v_fileName_4316_);
    v___x_4333_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_4333_, 0, v_fileName_4316_);
    lean_ctor_set(v___x_4333_, 1, v_fileMap_4317_);
    lean_ctor_set(v___x_4333_, 2, v_options_4318_);
    lean_ctor_set(v___x_4333_, 3, v_currRecDepth_4319_);
    lean_ctor_set(v___x_4333_, 4, v_maxRecDepth_4320_);
    lean_ctor_set(v___x_4333_, 5, v_ref_4332_);
    lean_ctor_set(v___x_4333_, 6, v_currNamespace_4322_);
    lean_ctor_set(v___x_4333_, 7, v_openDecls_4323_);
    lean_ctor_set(v___x_4333_, 8, v_initHeartbeats_4324_);
    lean_ctor_set(v___x_4333_, 9, v_maxHeartbeats_4325_);
    lean_ctor_set(v___x_4333_, 10, v_quotContext_4326_);
    lean_ctor_set(v___x_4333_, 11, v_currMacroScope_4327_);
    lean_ctor_set(v___x_4333_, 12, v_cancelTk_x3f_4329_);
    lean_ctor_set(v___x_4333_, 13, v_inheritedTraceOptions_4331_);
    lean_ctor_set_uint8(
        v___x_4333_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_4328_,
    );
    lean_ctor_set_uint8(
        v___x_4333_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4330_,
    );
    v___x_4334_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(v_msg_4310_, v___y_4311_, v___y_4312_, v___x_4333_, v___y_4314_);
    lean_dec_ref_known(v___x_4333_, 14);
    return v___x_4334_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18___redArg___boxed(
    mut v_ref_4335_: *mut LeanObject,
    mut v_msg_4336_: *mut LeanObject,
    mut v___y_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
    mut v___y_4341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4342_: *mut LeanObject = core::ptr::null_mut();
    v_res_4342_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18___redArg(v_ref_4335_, v_msg_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
    lean_dec(v___y_4340_);
    lean_dec_ref(v___y_4339_);
    lean_dec(v___y_4338_);
    lean_dec_ref(v___y_4337_);
    lean_dec(v_ref_4335_);
    return v_res_4342_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    v___x_4343_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4343_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    v___x_4344_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__0);
    v___x_4345_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4345_, 0, v___x_4344_);
    return v___x_4345_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    v___x_4346_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1);
    v___x_4347_ = lean_unsigned_to_nat(0);
    v___x_4348_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_4348_, 0, v___x_4347_);
    lean_ctor_set(v___x_4348_, 1, v___x_4347_);
    lean_ctor_set(v___x_4348_, 2, v___x_4347_);
    lean_ctor_set(v___x_4348_, 3, v___x_4347_);
    lean_ctor_set(v___x_4348_, 4, v___x_4346_);
    lean_ctor_set(v___x_4348_, 5, v___x_4346_);
    lean_ctor_set(v___x_4348_, 6, v___x_4346_);
    lean_ctor_set(v___x_4348_, 7, v___x_4346_);
    lean_ctor_set(v___x_4348_, 8, v___x_4346_);
    lean_ctor_set(v___x_4348_, 9, v___x_4346_);
    return v___x_4348_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    v___x_4349_ = lean_unsigned_to_nat(32);
    v___x_4350_ = lean_mk_empty_array_with_capacity(v___x_4349_);
    v___x_4351_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4351_, 0, v___x_4350_);
    return v___x_4351_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4352_: usize = 0;
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    v___x_4352_ = 5usize;
    v___x_4353_ = lean_unsigned_to_nat(0);
    v___x_4354_ = lean_unsigned_to_nat(32);
    v___x_4355_ = lean_mk_empty_array_with_capacity(v___x_4354_);
    v___x_4356_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__3);
    v___x_4357_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4357_, 0, v___x_4356_);
    lean_ctor_set(v___x_4357_, 1, v___x_4355_);
    lean_ctor_set(v___x_4357_, 2, v___x_4353_);
    lean_ctor_set(v___x_4357_, 3, v___x_4353_);
    lean_ctor_set_usize(v___x_4357_, 4, v___x_4352_);
    return v___x_4357_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    v___x_4358_ = lean_box(1);
    v___x_4359_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__4);
    v___x_4360_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1);
    v___x_4361_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4361_, 0, v___x_4360_);
    lean_ctor_set(v___x_4361_, 1, v___x_4359_);
    lean_ctor_set(v___x_4361_, 2, v___x_4358_);
    return v___x_4361_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    v___x_4363_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__6;
    v___x_4364_ = l_Lean_stringToMessageData(v___x_4363_);
    return v___x_4364_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    v___x_4366_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__8;
    v___x_4367_ = l_Lean_stringToMessageData(v___x_4366_);
    return v___x_4367_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    v___x_4369_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__10;
    v___x_4370_ = l_Lean_stringToMessageData(v___x_4369_);
    return v___x_4370_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    v___x_4372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__12;
    v___x_4373_ = l_Lean_stringToMessageData(v___x_4372_);
    return v___x_4373_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    v___x_4375_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__14;
    v___x_4376_ = l_Lean_stringToMessageData(v___x_4375_);
    return v___x_4376_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    v___x_4378_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__16;
    v___x_4379_ = l_Lean_stringToMessageData(v___x_4378_);
    return v___x_4379_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    v___x_4381_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__18;
    v___x_4382_ = l_Lean_stringToMessageData(v___x_4381_);
    return v___x_4382_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg(
    mut v_msg_4383_: *mut LeanObject,
    mut v_declHint_4384_: *mut LeanObject,
    mut v___y_4385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: u8 = 0;
    let mut v_isExporting_4390_: u8 = 0;
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: u8 = 0;
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4412_: u8 = 0;
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: u8 = 0;
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4444_: u8 = 0;
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4387_ = lean_st_ref_get(v___y_4385_);
                v_env_4388_ = lean_ctor_get(v___x_4387_, 0);
                lean_inc_ref(v_env_4388_);
                lean_dec(v___x_4387_);
                v___x_4389_ = l_Lean_Name_isAnonymous(v_declHint_4384_);
                if v___x_4389_ == 0 {
                    v_isExporting_4390_ = lean_ctor_get_uint8(
                        v_env_4388_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4390_ == 0 {
                        lean_dec_ref(v_env_4388_);
                        lean_dec(v_declHint_4384_);
                        v___x_4391_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4391_, 0, v_msg_4383_);
                        return v___x_4391_;
                    } else {
                        lean_inc_ref(v_env_4388_);
                        v___x_4392_ = l_Lean_Environment_setExporting(v_env_4388_, v___x_4389_);
                        lean_inc(v_declHint_4384_);
                        lean_inc_ref(v___x_4392_);
                        v___x_4393_ = l_Lean_Environment_contains(
                            v___x_4392_,
                            v_declHint_4384_,
                            v_isExporting_4390_,
                        );
                        if v___x_4393_ == 0 {
                            lean_dec_ref(v___x_4392_);
                            lean_dec_ref(v_env_4388_);
                            lean_dec(v_declHint_4384_);
                            v___x_4394_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4394_, 0, v_msg_4383_);
                            return v___x_4394_;
                        } else {
                            v___x_4395_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__2);
                            v___x_4396_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__5);
                            v___x_4397_ = l_Lean_Options_empty;
                            v___x_4398_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_4398_, 0, v___x_4392_);
                            lean_ctor_set(v___x_4398_, 1, v___x_4395_);
                            lean_ctor_set(v___x_4398_, 2, v___x_4396_);
                            lean_ctor_set(v___x_4398_, 3, v___x_4397_);
                            lean_inc(v_declHint_4384_);
                            v___x_4399_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4384_, v___x_4389_);
                            v_c_4400_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_4400_, 0, v___x_4398_);
                            lean_ctor_set(v_c_4400_, 1, v___x_4399_);
                            v___x_4401_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4388_,
                                v_declHint_4384_,
                            );
                            if lean_obj_tag(v___x_4401_) == 0 {
                                lean_dec_ref(v_env_4388_);
                                lean_dec(v_declHint_4384_);
                                v___x_4402_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7);
                                v___x_4403_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4403_, 0, v___x_4402_);
                                lean_ctor_set(v___x_4403_, 1, v_c_4400_);
                                v___x_4404_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__9);
                                v___x_4405_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4405_, 0, v___x_4403_);
                                lean_ctor_set(v___x_4405_, 1, v___x_4404_);
                                v___x_4406_ = l_Lean_MessageData_note(v___x_4405_);
                                v___x_4407_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4407_, 0, v_msg_4383_);
                                lean_ctor_set(v___x_4407_, 1, v___x_4406_);
                                v___x_4408_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_4408_, 0, v___x_4407_);
                                return v___x_4408_;
                            } else {
                                v_val_4409_ = lean_ctor_get(v___x_4401_, 0);
                                v_isSharedCheck_4444_ = (!lean_is_exclusive(v___x_4401_)) as u8;
                                if v_isSharedCheck_4444_ == 0 {
                                    v___x_4411_ = v___x_4401_;
                                    v_isShared_4412_ = v_isSharedCheck_4444_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_4409_);
                                    lean_dec(v___x_4401_);
                                    v___x_4411_ = lean_box(0);
                                    v_isShared_4412_ = v_isSharedCheck_4444_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_4388_);
                    lean_dec(v_declHint_4384_);
                    v___x_4445_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4445_, 0, v_msg_4383_);
                    return v___x_4445_;
                }
            }
            1 => {
                v___x_4413_ = lean_box(0);
                v___x_4414_ = l_Lean_Environment_header(v_env_4388_);
                lean_dec_ref(v_env_4388_);
                v___x_4415_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4414_);
                v_mod_4416_ = lean_array_get(v___x_4413_, v___x_4415_, v_val_4409_);
                lean_dec(v_val_4409_);
                lean_dec_ref(v___x_4415_);
                v___x_4417_ = l_Lean_isPrivateName(v_declHint_4384_);
                lean_dec(v_declHint_4384_);
                if v___x_4417_ == 0 {
                    v___x_4418_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__11);
                    v___x_4419_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4419_, 0, v___x_4418_);
                    lean_ctor_set(v___x_4419_, 1, v_c_4400_);
                    v___x_4420_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__13);
                    v___x_4421_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4421_, 0, v___x_4419_);
                    lean_ctor_set(v___x_4421_, 1, v___x_4420_);
                    v___x_4422_ = l_Lean_MessageData_ofName(v_mod_4416_);
                    v___x_4423_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4423_, 0, v___x_4421_);
                    lean_ctor_set(v___x_4423_, 1, v___x_4422_);
                    v___x_4424_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__15);
                    v___x_4425_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4425_, 0, v___x_4423_);
                    lean_ctor_set(v___x_4425_, 1, v___x_4424_);
                    v___x_4426_ = l_Lean_MessageData_note(v___x_4425_);
                    v___x_4427_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4427_, 0, v_msg_4383_);
                    lean_ctor_set(v___x_4427_, 1, v___x_4426_);
                    if v_isShared_4412_ == 0 {
                        lean_ctor_set_tag(v___x_4411_, 0);
                        lean_ctor_set(v___x_4411_, 0, v___x_4427_);
                        v___x_4429_ = v___x_4411_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4430_, 0, v___x_4427_);
                        v___x_4429_ = v_reuseFailAlloc_4430_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4431_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7);
                    v___x_4432_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4432_, 0, v___x_4431_);
                    lean_ctor_set(v___x_4432_, 1, v_c_4400_);
                    v___x_4433_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__17);
                    v___x_4434_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4434_, 0, v___x_4432_);
                    lean_ctor_set(v___x_4434_, 1, v___x_4433_);
                    v___x_4435_ = l_Lean_MessageData_ofName(v_mod_4416_);
                    v___x_4436_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4436_, 0, v___x_4434_);
                    lean_ctor_set(v___x_4436_, 1, v___x_4435_);
                    v___x_4437_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__19);
                    v___x_4438_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4438_, 0, v___x_4436_);
                    lean_ctor_set(v___x_4438_, 1, v___x_4437_);
                    v___x_4439_ = l_Lean_MessageData_note(v___x_4438_);
                    v___x_4440_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4440_, 0, v_msg_4383_);
                    lean_ctor_set(v___x_4440_, 1, v___x_4439_);
                    if v_isShared_4412_ == 0 {
                        lean_ctor_set_tag(v___x_4411_, 0);
                        lean_ctor_set(v___x_4411_, 0, v___x_4440_);
                        v___x_4442_ = v___x_4411_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
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
    mut v_msg_4446_: *mut LeanObject,
    mut v_declHint_4447_: *mut LeanObject,
    mut v___y_4448_: *mut LeanObject,
    mut v___y_4449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4450_: *mut LeanObject = core::ptr::null_mut();
    v_res_4450_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg(v_msg_4446_, v_declHint_4447_, v___y_4448_);
    lean_dec(v___y_4448_);
    return v_res_4450_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17(
    mut v_msg_4451_: *mut LeanObject,
    mut v_declHint_4452_: *mut LeanObject,
    mut v___y_4453_: *mut LeanObject,
    mut v___y_4454_: *mut LeanObject,
    mut v___y_4455_: *mut LeanObject,
    mut v___y_4456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4458_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg(v_msg_4451_, v_declHint_4452_, v___y_4456_);
                v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
                v_isSharedCheck_4468_ = (!lean_is_exclusive(v___x_4458_)) as u8;
                if v_isSharedCheck_4468_ == 0 {
                    v___x_4461_ = v___x_4458_;
                    v_isShared_4462_ = v_isSharedCheck_4468_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4459_);
                    lean_dec(v___x_4458_);
                    v___x_4461_ = lean_box(0);
                    v_isShared_4462_ = v_isSharedCheck_4468_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4463_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4464_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_4464_, 0, v___x_4463_);
                lean_ctor_set(v___x_4464_, 1, v_a_4459_);
                if v_isShared_4462_ == 0 {
                    lean_ctor_set(v___x_4461_, 0, v___x_4464_);
                    v___x_4466_ = v___x_4461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4464_);
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
    mut v_msg_4469_: *mut LeanObject,
    mut v_declHint_4470_: *mut LeanObject,
    mut v___y_4471_: *mut LeanObject,
    mut v___y_4472_: *mut LeanObject,
    mut v___y_4473_: *mut LeanObject,
    mut v___y_4474_: *mut LeanObject,
    mut v___y_4475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4476_: *mut LeanObject = core::ptr::null_mut();
    v_res_4476_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17(v_msg_4469_, v_declHint_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_);
    lean_dec(v___y_4474_);
    lean_dec_ref(v___y_4473_);
    lean_dec(v___y_4472_);
    lean_dec_ref(v___y_4471_);
    return v_res_4476_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16___redArg(
    mut v_ref_4477_: *mut LeanObject,
    mut v_msg_4478_: *mut LeanObject,
    mut v_declHint_4479_: *mut LeanObject,
    mut v___y_4480_: *mut LeanObject,
    mut v___y_4481_: *mut LeanObject,
    mut v___y_4482_: *mut LeanObject,
    mut v___y_4483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    v___x_4485_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17(v_msg_4478_, v_declHint_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
    v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
    lean_inc(v_a_4486_);
    lean_dec_ref(v___x_4485_);
    v___x_4487_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18___redArg(v_ref_4477_, v_a_4486_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
    return v___x_4487_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16___redArg___boxed(
    mut v_ref_4488_: *mut LeanObject,
    mut v_msg_4489_: *mut LeanObject,
    mut v_declHint_4490_: *mut LeanObject,
    mut v___y_4491_: *mut LeanObject,
    mut v___y_4492_: *mut LeanObject,
    mut v___y_4493_: *mut LeanObject,
    mut v___y_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4496_: *mut LeanObject = core::ptr::null_mut();
    v_res_4496_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16___redArg(v_ref_4488_, v_msg_4489_, v_declHint_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
    lean_dec(v___y_4494_);
    lean_dec_ref(v___y_4493_);
    lean_dec(v___y_4492_);
    lean_dec_ref(v___y_4491_);
    lean_dec(v_ref_4488_);
    return v_res_4496_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    v___x_4498_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__0;
    v___x_4499_ = l_Lean_stringToMessageData(v___x_4498_);
    return v___x_4499_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg(
    mut v_ref_4500_: *mut LeanObject,
    mut v_constName_4501_: *mut LeanObject,
    mut v___y_4502_: *mut LeanObject,
    mut v___y_4503_: *mut LeanObject,
    mut v___y_4504_: *mut LeanObject,
    mut v___y_4505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: u8 = 0;
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    v___x_4507_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__1);
    v___x_4508_ = 0;
    lean_inc(v_constName_4501_);
    v___x_4509_ = l_Lean_MessageData_ofConstName(v_constName_4501_, v___x_4508_);
    v___x_4510_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4510_, 0, v___x_4507_);
    lean_ctor_set(v___x_4510_, 1, v___x_4509_);
    v___x_4511_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1);
    v___x_4512_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4512_, 0, v___x_4510_);
    lean_ctor_set(v___x_4512_, 1, v___x_4511_);
    v___x_4513_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16___redArg(v_ref_4500_, v___x_4512_, v_constName_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
    return v___x_4513_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___boxed(
    mut v_ref_4514_: *mut LeanObject,
    mut v_constName_4515_: *mut LeanObject,
    mut v___y_4516_: *mut LeanObject,
    mut v___y_4517_: *mut LeanObject,
    mut v___y_4518_: *mut LeanObject,
    mut v___y_4519_: *mut LeanObject,
    mut v___y_4520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4521_: *mut LeanObject = core::ptr::null_mut();
    v_res_4521_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg(v_ref_4514_, v_constName_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
    lean_dec(v___y_4519_);
    lean_dec_ref(v___y_4518_);
    lean_dec(v___y_4517_);
    lean_dec_ref(v___y_4516_);
    lean_dec(v_ref_4514_);
    return v_res_4521_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3___redArg(
    mut v_constName_4522_: *mut LeanObject,
    mut v___y_4523_: *mut LeanObject,
    mut v___y_4524_: *mut LeanObject,
    mut v___y_4525_: *mut LeanObject,
    mut v___y_4526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    v_ref_4528_ = lean_ctor_get(v___y_4525_, 5);
    v___x_4529_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg(v_ref_4528_, v_constName_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
    return v___x_4529_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3___redArg___boxed(
    mut v_constName_4530_: *mut LeanObject,
    mut v___y_4531_: *mut LeanObject,
    mut v___y_4532_: *mut LeanObject,
    mut v___y_4533_: *mut LeanObject,
    mut v___y_4534_: *mut LeanObject,
    mut v___y_4535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4536_: *mut LeanObject = core::ptr::null_mut();
    v_res_4536_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3___redArg(v_constName_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
    lean_dec(v___y_4534_);
    lean_dec_ref(v___y_4533_);
    lean_dec(v___y_4532_);
    lean_dec_ref(v___y_4531_);
    return v_res_4536_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2(
    mut v_constName_4537_: *mut LeanObject,
    mut v___y_4538_: *mut LeanObject,
    mut v___y_4539_: *mut LeanObject,
    mut v___y_4540_: *mut LeanObject,
    mut v___y_4541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: u8 = 0;
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4551_: u8 = 0;
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4555_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4543_ = lean_st_ref_get(v___y_4541_);
                v_env_4544_ = lean_ctor_get(v___x_4543_, 0);
                lean_inc_ref(v_env_4544_);
                lean_dec(v___x_4543_);
                v___x_4545_ = 0;
                lean_inc(v_constName_4537_);
                v___x_4546_ =
                    l_Lean_Environment_find_x3f(v_env_4544_, v_constName_4537_, v___x_4545_);
                if lean_obj_tag(v___x_4546_) == 0 {
                    v___x_4547_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3___redArg(v_constName_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
                    return v___x_4547_;
                } else {
                    lean_dec(v_constName_4537_);
                    v_val_4548_ = lean_ctor_get(v___x_4546_, 0);
                    v_isSharedCheck_4555_ = (!lean_is_exclusive(v___x_4546_)) as u8;
                    if v_isSharedCheck_4555_ == 0 {
                        v___x_4550_ = v___x_4546_;
                        v_isShared_4551_ = v_isSharedCheck_4555_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4548_);
                        lean_dec(v___x_4546_);
                        v___x_4550_ = lean_box(0);
                        v_isShared_4551_ = v_isSharedCheck_4555_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4551_ == 0 {
                    lean_ctor_set_tag(v___x_4550_, 0);
                    v___x_4553_ = v___x_4550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_val_4548_);
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
    mut v_constName_4556_: *mut LeanObject,
    mut v___y_4557_: *mut LeanObject,
    mut v___y_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
    mut v___y_4560_: *mut LeanObject,
    mut v___y_4561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4562_: *mut LeanObject = core::ptr::null_mut();
    v_res_4562_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2(v_constName_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
    lean_dec(v___y_4560_);
    lean_dec_ref(v___y_4559_);
    lean_dec(v___y_4558_);
    lean_dec_ref(v___y_4557_);
    return v_res_4562_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__3(
    mut v_a_4563_: *mut LeanObject,
    mut v_a_4564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4570_: u8 = 0;
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4563_) == 0 {
                    v___x_4565_ = l_List_reverse___redArg(v_a_4564_);
                    return v___x_4565_;
                } else {
                    v_head_4566_ = lean_ctor_get(v_a_4563_, 0);
                    v_tail_4567_ = lean_ctor_get(v_a_4563_, 1);
                    v_isSharedCheck_4576_ = (!lean_is_exclusive(v_a_4563_)) as u8;
                    if v_isSharedCheck_4576_ == 0 {
                        v___x_4569_ = v_a_4563_;
                        v_isShared_4570_ = v_isSharedCheck_4576_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4567_);
                        lean_inc(v_head_4566_);
                        lean_dec(v_a_4563_);
                        v___x_4569_ = lean_box(0);
                        v_isShared_4570_ = v_isSharedCheck_4576_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4571_ = l_Lean_mkLevelParam(v_head_4566_);
                if v_isShared_4570_ == 0 {
                    lean_ctor_set(v___x_4569_, 1, v_a_4564_);
                    lean_ctor_set(v___x_4569_, 0, v___x_4571_);
                    v___x_4573_ = v___x_4569_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4571_);
                    lean_ctor_set(v_reuseFailAlloc_4575_, 1, v_a_4564_);
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
-> *mut LeanObject {
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    v___x_4577_ = l_instMonadEIO(lean_box(0));
    return v___x_4577_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1(
    mut v_msg_4582_: *mut LeanObject,
    mut v___y_4583_: *mut LeanObject,
    mut v___y_4584_: *mut LeanObject,
    mut v___y_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4593_: u8 = 0;
    let mut v_toFunctor_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4600_: u8 = 0;
    let mut v___f_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4617_: u8 = 0;
    let mut v_toFunctor_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4624_: u8 = 0;
    let mut v___f_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10082__overap_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4643_: u8 = 0;
    let mut v_unused_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4645_: u8 = 0;
    let mut v_unused_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4649_: u8 = 0;
    let mut v_unused_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4651_: u8 = 0;
    let mut v_unused_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4588_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__0_once), _init_l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__0);
                v___x_4589_ = l_StateRefT_x27_instMonad___redArg(v___x_4588_);
                v_toApplicative_4590_ = lean_ctor_get(v___x_4589_, 0);
                v_isSharedCheck_4651_ = (!lean_is_exclusive(v___x_4589_)) as u8;
                if v_isSharedCheck_4651_ == 0 {
                    v_unused_4652_ = lean_ctor_get(v___x_4589_, 1);
                    lean_dec(v_unused_4652_);
                    v___x_4592_ = v___x_4589_;
                    v_isShared_4593_ = v_isSharedCheck_4651_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4590_);
                    lean_dec(v___x_4589_);
                    v___x_4592_ = lean_box(0);
                    v_isShared_4593_ = v_isSharedCheck_4651_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4594_ = lean_ctor_get(v_toApplicative_4590_, 0);
                v_toSeq_4595_ = lean_ctor_get(v_toApplicative_4590_, 2);
                v_toSeqLeft_4596_ = lean_ctor_get(v_toApplicative_4590_, 3);
                v_toSeqRight_4597_ = lean_ctor_get(v_toApplicative_4590_, 4);
                v_isSharedCheck_4649_ = (!lean_is_exclusive(v_toApplicative_4590_)) as u8;
                if v_isSharedCheck_4649_ == 0 {
                    v_unused_4650_ = lean_ctor_get(v_toApplicative_4590_, 1);
                    lean_dec(v_unused_4650_);
                    v___x_4599_ = v_toApplicative_4590_;
                    v_isShared_4600_ = v_isSharedCheck_4649_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4597_);
                    lean_inc(v_toSeqLeft_4596_);
                    lean_inc(v_toSeq_4595_);
                    lean_inc(v_toFunctor_4594_);
                    lean_dec(v_toApplicative_4590_);
                    v___x_4599_ = lean_box(0);
                    v_isShared_4600_ = v_isSharedCheck_4649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4601_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__1;
                v___f_4602_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__2;
                lean_inc_ref(v_toFunctor_4594_);
                v___f_4603_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4603_, 0, v_toFunctor_4594_);
                v___f_4604_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4604_, 0, v_toFunctor_4594_);
                v___x_4605_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4605_, 0, v___f_4603_);
                lean_ctor_set(v___x_4605_, 1, v___f_4604_);
                v___f_4606_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4606_, 0, v_toSeqRight_4597_);
                v___f_4607_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4607_, 0, v_toSeqLeft_4596_);
                v___f_4608_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4608_, 0, v_toSeq_4595_);
                if v_isShared_4600_ == 0 {
                    lean_ctor_set(v___x_4599_, 4, v___f_4606_);
                    lean_ctor_set(v___x_4599_, 3, v___f_4607_);
                    lean_ctor_set(v___x_4599_, 2, v___f_4608_);
                    lean_ctor_set(v___x_4599_, 1, v___f_4601_);
                    lean_ctor_set(v___x_4599_, 0, v___x_4605_);
                    v___x_4610_ = v___x_4599_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4605_);
                    lean_ctor_set(v_reuseFailAlloc_4648_, 1, v___f_4601_);
                    lean_ctor_set(v_reuseFailAlloc_4648_, 2, v___f_4608_);
                    lean_ctor_set(v_reuseFailAlloc_4648_, 3, v___f_4607_);
                    lean_ctor_set(v_reuseFailAlloc_4648_, 4, v___f_4606_);
                    v___x_4610_ = v_reuseFailAlloc_4648_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4593_ == 0 {
                    lean_ctor_set(v___x_4592_, 1, v___f_4602_);
                    lean_ctor_set(v___x_4592_, 0, v___x_4610_);
                    v___x_4612_ = v___x_4592_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4610_);
                    lean_ctor_set(v_reuseFailAlloc_4647_, 1, v___f_4602_);
                    v___x_4612_ = v_reuseFailAlloc_4647_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4613_ = l_StateRefT_x27_instMonad___redArg(v___x_4612_);
                v_toApplicative_4614_ = lean_ctor_get(v___x_4613_, 0);
                v_isSharedCheck_4645_ = (!lean_is_exclusive(v___x_4613_)) as u8;
                if v_isSharedCheck_4645_ == 0 {
                    v_unused_4646_ = lean_ctor_get(v___x_4613_, 1);
                    lean_dec(v_unused_4646_);
                    v___x_4616_ = v___x_4613_;
                    v_isShared_4617_ = v_isSharedCheck_4645_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4614_);
                    lean_dec(v___x_4613_);
                    v___x_4616_ = lean_box(0);
                    v_isShared_4617_ = v_isSharedCheck_4645_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4618_ = lean_ctor_get(v_toApplicative_4614_, 0);
                v_toSeq_4619_ = lean_ctor_get(v_toApplicative_4614_, 2);
                v_toSeqLeft_4620_ = lean_ctor_get(v_toApplicative_4614_, 3);
                v_toSeqRight_4621_ = lean_ctor_get(v_toApplicative_4614_, 4);
                v_isSharedCheck_4643_ = (!lean_is_exclusive(v_toApplicative_4614_)) as u8;
                if v_isSharedCheck_4643_ == 0 {
                    v_unused_4644_ = lean_ctor_get(v_toApplicative_4614_, 1);
                    lean_dec(v_unused_4644_);
                    v___x_4623_ = v_toApplicative_4614_;
                    v_isShared_4624_ = v_isSharedCheck_4643_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4621_);
                    lean_inc(v_toSeqLeft_4620_);
                    lean_inc(v_toSeq_4619_);
                    lean_inc(v_toFunctor_4618_);
                    lean_dec(v_toApplicative_4614_);
                    v___x_4623_ = lean_box(0);
                    v_isShared_4624_ = v_isSharedCheck_4643_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4625_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__3;
                v___f_4626_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__4;
                lean_inc_ref(v_toFunctor_4618_);
                v___f_4627_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4627_, 0, v_toFunctor_4618_);
                v___f_4628_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4628_, 0, v_toFunctor_4618_);
                v___x_4629_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4629_, 0, v___f_4627_);
                lean_ctor_set(v___x_4629_, 1, v___f_4628_);
                v___f_4630_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4630_, 0, v_toSeqRight_4621_);
                v___f_4631_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4631_, 0, v_toSeqLeft_4620_);
                v___f_4632_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4632_, 0, v_toSeq_4619_);
                if v_isShared_4624_ == 0 {
                    lean_ctor_set(v___x_4623_, 4, v___f_4630_);
                    lean_ctor_set(v___x_4623_, 3, v___f_4631_);
                    lean_ctor_set(v___x_4623_, 2, v___f_4632_);
                    lean_ctor_set(v___x_4623_, 1, v___f_4625_);
                    lean_ctor_set(v___x_4623_, 0, v___x_4629_);
                    v___x_4634_ = v___x_4623_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4629_);
                    lean_ctor_set(v_reuseFailAlloc_4642_, 1, v___f_4625_);
                    lean_ctor_set(v_reuseFailAlloc_4642_, 2, v___f_4632_);
                    lean_ctor_set(v_reuseFailAlloc_4642_, 3, v___f_4631_);
                    lean_ctor_set(v_reuseFailAlloc_4642_, 4, v___f_4630_);
                    v___x_4634_ = v_reuseFailAlloc_4642_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4617_ == 0 {
                    lean_ctor_set(v___x_4616_, 1, v___f_4626_);
                    lean_ctor_set(v___x_4616_, 0, v___x_4634_);
                    v___x_4636_ = v___x_4616_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4634_);
                    lean_ctor_set(v_reuseFailAlloc_4641_, 1, v___f_4626_);
                    v___x_4636_ = v_reuseFailAlloc_4641_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4637_ = lean_box(0);
                v___x_4638_ = l_instInhabitedOfMonad___redArg(v___x_4636_, v___x_4637_);
                v___x_10082__overap_4639_ = lean_panic_fn_borrowed(v___x_4638_, v_msg_4582_);
                lean_dec(v___x_4638_);
                lean_inc(v___y_4586_);
                lean_inc_ref(v___y_4585_);
                lean_inc(v___y_4584_);
                lean_inc_ref(v___y_4583_);
                v___x_4640_ = lean_apply_5(
                    v___x_10082__overap_4639_,
                    v___y_4583_,
                    v___y_4584_,
                    v___y_4585_,
                    v___y_4586_,
                    lean_box(0),
                );
                return v___x_4640_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___boxed(
    mut v_msg_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
    mut v___y_4655_: *mut LeanObject,
    mut v___y_4656_: *mut LeanObject,
    mut v___y_4657_: *mut LeanObject,
    mut v___y_4658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4659_: *mut LeanObject = core::ptr::null_mut();
    v_res_4659_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1(v_msg_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_);
    lean_dec(v___y_4657_);
    lean_dec_ref(v___y_4656_);
    lean_dec(v___y_4655_);
    lean_dec_ref(v___y_4654_);
    return v_res_4659_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    v___x_4661_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__0;
    v___x_4662_ = l_Lean_stringToMessageData(v___x_4661_);
    return v___x_4662_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    v___x_4666_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__4;
    v___x_4667_ = lean_unsigned_to_nat(11);
    v___x_4668_ = lean_unsigned_to_nat(129);
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
    mut v_constName_4672_: *mut LeanObject,
    mut v___y_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
    mut v___y_4676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: u8 = 0;
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: u8 = 0;
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_4691_: u8 = 0;
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4696_: u8 = 0;
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4700_: u8 = 0;
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4706_: u8 = 0;
    let mut v_val_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4711_: u8 = 0;
    let mut v_a_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4715_: u8 = 0;
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4686_ = lean_st_ref_get(v___y_4676_);
                v_env_4687_ = lean_ctor_get(v___x_4686_, 0);
                lean_inc_ref(v_env_4687_);
                lean_dec(v___x_4686_);
                v___x_4688_ = 0;
                lean_inc(v_constName_4672_);
                v___x_4689_ =
                    l_Lean_Environment_findAsync_x3f(v_env_4687_, v_constName_4672_, v___x_4688_);
                if lean_obj_tag(v___x_4689_) == 1 {
                    v_val_4690_ = lean_ctor_get(v___x_4689_, 0);
                    lean_inc(v_val_4690_);
                    lean_dec_ref_known(v___x_4689_, 1);
                    v_kind_4691_ = lean_ctor_get_uint8(
                        v_val_4690_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    if v_kind_4691_ == 7 {
                        v___x_4692_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4690_);
                        if lean_obj_tag(v___x_4692_) == 7 {
                            lean_dec(v_constName_4672_);
                            v_val_4693_ = lean_ctor_get(v___x_4692_, 0);
                            v_isSharedCheck_4700_ = (!lean_is_exclusive(v___x_4692_)) as u8;
                            if v_isSharedCheck_4700_ == 0 {
                                v___x_4695_ = v___x_4692_;
                                v_isShared_4696_ = v_isSharedCheck_4700_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_val_4693_);
                                lean_dec(v___x_4692_);
                                v___x_4695_ = lean_box(0);
                                v_isShared_4696_ = v_isSharedCheck_4700_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_4692_);
                            v___x_4701_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__5_once), _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__5);
                            v___x_4702_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1(v___x_4701_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
                            if lean_obj_tag(v___x_4702_) == 0 {
                                v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
                                v_isSharedCheck_4711_ = (!lean_is_exclusive(v___x_4702_)) as u8;
                                if v_isSharedCheck_4711_ == 0 {
                                    v___x_4705_ = v___x_4702_;
                                    v_isShared_4706_ = v_isSharedCheck_4711_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_4703_);
                                    lean_dec(v___x_4702_);
                                    v___x_4705_ = lean_box(0);
                                    v_isShared_4706_ = v_isSharedCheck_4711_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v_constName_4672_);
                                v_a_4712_ = lean_ctor_get(v___x_4702_, 0);
                                v_isSharedCheck_4719_ = (!lean_is_exclusive(v___x_4702_)) as u8;
                                if v_isSharedCheck_4719_ == 0 {
                                    v___x_4714_ = v___x_4702_;
                                    v_isShared_4715_ = v_isSharedCheck_4719_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_4712_);
                                    lean_dec(v___x_4702_);
                                    v___x_4714_ = lean_box(0);
                                    v_isShared_4715_ = v_isSharedCheck_4719_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_val_4690_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4689_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4679_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1);
                v___x_4680_ = 0;
                v___x_4681_ = l_Lean_MessageData_ofConstName(v_constName_4672_, v___x_4680_);
                v___x_4682_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4682_, 0, v___x_4679_);
                lean_ctor_set(v___x_4682_, 1, v___x_4681_);
                v___x_4683_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__1_once), _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__1);
                v___x_4684_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4684_, 0, v___x_4682_);
                lean_ctor_set(v___x_4684_, 1, v___x_4683_);
                v___x_4685_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(v___x_4684_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
                return v___x_4685_;
            }
            2 => {
                if v_isShared_4696_ == 0 {
                    lean_ctor_set_tag(v___x_4695_, 0);
                    v___x_4698_ = v___x_4695_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4699_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_val_4693_);
                    v___x_4698_ = v_reuseFailAlloc_4699_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4698_;
            }
            4 => {
                if lean_obj_tag(v_a_4703_) == 0 {
                    lean_del_object(v___x_4705_);
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_constName_4672_);
                    v_val_4707_ = lean_ctor_get(v_a_4703_, 0);
                    lean_inc(v_val_4707_);
                    lean_dec_ref_known(v_a_4703_, 1);
                    if v_isShared_4706_ == 0 {
                        lean_ctor_set(v___x_4705_, 0, v_val_4707_);
                        v___x_4709_ = v___x_4705_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4710_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_val_4707_);
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
                    v_reuseFailAlloc_4718_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4712_);
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
    mut v_constName_4720_: *mut LeanObject,
    mut v___y_4721_: *mut LeanObject,
    mut v___y_4722_: *mut LeanObject,
    mut v___y_4723_: *mut LeanObject,
    mut v___y_4724_: *mut LeanObject,
    mut v___y_4725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4726_: *mut LeanObject = core::ptr::null_mut();
    v_res_4726_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1(v_constName_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_);
    lean_dec(v___y_4724_);
    lean_dec_ref(v___y_4723_);
    lean_dec(v___y_4722_);
    lean_dec_ref(v___y_4721_);
    return v_res_4726_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl(
    mut v_declName_4734_: *mut LeanObject,
    mut v_a_4735_: *mut LeanObject,
    mut v_a_4736_: *mut LeanObject,
    mut v_a_4737_: *mut LeanObject,
    mut v_a_4738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_all_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numMotives_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numMinors_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: u8 = 0;
    let mut v___x_4762_: u8 = 0;
    let mut v___y_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: u8 = 0;
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4782_: u8 = 0;
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4786_: u8 = 0;
    let mut v_a_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4790_: u8 = 0;
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4794_: u8 = 0;
    let mut v_a_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4798_: u8 = 0;
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4802_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_4734_);
                v___x_4740_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0(v_declName_4734_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_);
                if lean_obj_tag(v___x_4740_) == 0 {
                    v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
                    lean_inc(v_a_4741_);
                    lean_dec_ref_known(v___x_4740_, 1);
                    lean_inc_n(v_declName_4734_, 2);
                    v___x_4742_ = l_Lean_mkCasesOnName(v_declName_4734_);
                    v___x_4743_ = l_Lean_mkRecName(v_declName_4734_);
                    lean_inc(v___x_4743_);
                    v___x_4744_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1(v___x_4743_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_);
                    if lean_obj_tag(v___x_4744_) == 0 {
                        v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
                        lean_inc(v_a_4745_);
                        lean_dec_ref_known(v___x_4744_, 1);
                        lean_inc(v___x_4743_);
                        v___x_4746_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2(v___x_4743_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_);
                        if lean_obj_tag(v___x_4746_) == 0 {
                            v_toConstantVal_4747_ = lean_ctor_get(v_a_4741_, 0);
                            lean_inc_ref(v_toConstantVal_4747_);
                            lean_dec(v_a_4741_);
                            v_a_4748_ = lean_ctor_get(v___x_4746_, 0);
                            lean_inc(v_a_4748_);
                            lean_dec_ref_known(v___x_4746_, 1);
                            v_all_4749_ = lean_ctor_get(v_a_4745_, 1);
                            lean_inc(v_all_4749_);
                            v_numParams_4750_ = lean_ctor_get(v_a_4745_, 2);
                            lean_inc(v_numParams_4750_);
                            v_numIndices_4751_ = lean_ctor_get(v_a_4745_, 3);
                            lean_inc(v_numIndices_4751_);
                            v_numMotives_4752_ = lean_ctor_get(v_a_4745_, 4);
                            lean_inc(v_numMotives_4752_);
                            v_numMinors_4753_ = lean_ctor_get(v_a_4745_, 5);
                            lean_inc(v_numMinors_4753_);
                            lean_dec(v_a_4745_);
                            v_levelParams_4754_ = lean_ctor_get(v_toConstantVal_4747_, 1);
                            lean_inc(v_levelParams_4754_);
                            lean_dec_ref(v_toConstantVal_4747_);
                            v___x_4755_ = lean_array_mk(v_all_4749_);
                            v___x_4756_ = l_Lean_ConstantInfo_levelParams(v_a_4748_);
                            v___x_4757_ = lean_box(0);
                            lean_inc(v___x_4756_);
                            v___x_4758_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__3(v___x_4756_, v___x_4757_);
                            v___x_4759_ = l_List_lengthTR___redArg(v___x_4756_);
                            v___x_4760_ = l_List_lengthTR___redArg(v_levelParams_4754_);
                            lean_dec(v_levelParams_4754_);
                            v___x_4761_ = lean_nat_dec_eq(v___x_4759_, v___x_4760_);
                            lean_dec(v___x_4760_);
                            lean_dec(v___x_4759_);
                            v___x_4762_ = 1;
                            if v___x_4761_ == 0 {
                                v___x_4776_ = lean_box(0);
                                v___x_4777_ = l_List_head_x21___redArg(v___x_4776_, v___x_4758_);
                                v___y_4764_ = v___x_4777_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4778_ = lean_box(0);
                                v___y_4764_ = v___x_4778_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4745_);
                            lean_dec(v___x_4743_);
                            lean_dec(v___x_4742_);
                            lean_dec(v_a_4741_);
                            lean_dec(v_declName_4734_);
                            v_a_4779_ = lean_ctor_get(v___x_4746_, 0);
                            v_isSharedCheck_4786_ = (!lean_is_exclusive(v___x_4746_)) as u8;
                            if v_isSharedCheck_4786_ == 0 {
                                v___x_4781_ = v___x_4746_;
                                v_isShared_4782_ = v_isSharedCheck_4786_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_4779_);
                                lean_dec(v___x_4746_);
                                v___x_4781_ = lean_box(0);
                                v_isShared_4782_ = v_isSharedCheck_4786_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_4743_);
                        lean_dec(v___x_4742_);
                        lean_dec(v_a_4741_);
                        lean_dec(v_declName_4734_);
                        v_a_4787_ = lean_ctor_get(v___x_4744_, 0);
                        v_isSharedCheck_4794_ = (!lean_is_exclusive(v___x_4744_)) as u8;
                        if v_isSharedCheck_4794_ == 0 {
                            v___x_4789_ = v___x_4744_;
                            v_isShared_4790_ = v_isSharedCheck_4794_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4787_);
                            lean_dec(v___x_4744_);
                            v___x_4789_ = lean_box(0);
                            v_isShared_4790_ = v_isSharedCheck_4794_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_declName_4734_);
                    v_a_4795_ = lean_ctor_get(v___x_4740_, 0);
                    v_isSharedCheck_4802_ = (!lean_is_exclusive(v___x_4740_)) as u8;
                    if v_isSharedCheck_4802_ == 0 {
                        v___x_4797_ = v___x_4740_;
                        v_isShared_4798_ = v_isSharedCheck_4802_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4795_);
                        lean_dec(v___x_4740_);
                        v___x_4797_ = lean_box(0);
                        v_isShared_4798_ = v_isSharedCheck_4802_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4765_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__1;
                v___x_4766_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4766_, 0, v___y_4764_);
                lean_ctor_set(v___x_4766_, 1, v___x_4757_);
                lean_inc_ref(v___x_4766_);
                v___x_4767_ = l_Lean_mkConst(v___x_4765_, v___x_4766_);
                v___x_4768_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__3;
                v___x_4769_ = l_Lean_mkConst(v___x_4768_, v___x_4766_);
                v___x_4770_ = l_Lean_mkConst(v___x_4743_, v___x_4758_);
                v___x_4771_ = lean_box((v___x_4762_) as usize);
                v___f_4772_ = lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___boxed as *mut core::ffi::c_void, 19, 12);
                lean_closure_set(v___f_4772_, 0, v_numParams_4750_);
                lean_closure_set(v___f_4772_, 1, v_numMotives_4752_);
                lean_closure_set(v___f_4772_, 2, v___x_4767_);
                lean_closure_set(v___f_4772_, 3, v___x_4755_);
                lean_closure_set(v___f_4772_, 4, v_declName_4734_);
                lean_closure_set(v___f_4772_, 5, v_numIndices_4751_);
                lean_closure_set(v___f_4772_, 6, v_numMinors_4753_);
                lean_closure_set(v___f_4772_, 7, v___x_4771_);
                lean_closure_set(v___f_4772_, 8, v___x_4770_);
                lean_closure_set(v___f_4772_, 9, v___x_4742_);
                lean_closure_set(v___f_4772_, 10, v___x_4756_);
                lean_closure_set(v___f_4772_, 11, v___x_4769_);
                v___x_4773_ = l_Lean_ConstantInfo_type(v_a_4748_);
                lean_dec(v_a_4748_);
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
                    v_reuseFailAlloc_4785_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_a_4779_);
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
                    v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4787_);
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
                    v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
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
    mut v_declName_4803_: *mut LeanObject,
    mut v_a_4804_: *mut LeanObject,
    mut v_a_4805_: *mut LeanObject,
    mut v_a_4806_: *mut LeanObject,
    mut v_a_4807_: *mut LeanObject,
    mut v_a_4808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4809_: *mut LeanObject = core::ptr::null_mut();
    v_res_4809_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl(
        v_declName_4803_,
        v_a_4804_,
        v_a_4805_,
        v_a_4806_,
        v_a_4807_,
    );
    lean_dec(v_a_4807_);
    lean_dec_ref(v_a_4806_);
    lean_dec(v_a_4805_);
    lean_dec_ref(v_a_4804_);
    return v_res_4809_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4(
    mut v_recFVars_4810_: *mut LeanObject,
    mut v_as_4811_: *mut LeanObject,
    mut v_as_x27_4812_: *mut LeanObject,
    mut v_b_4813_: *mut LeanObject,
    mut v_a_4814_: *mut LeanObject,
    mut v___y_4815_: *mut LeanObject,
    mut v___y_4816_: *mut LeanObject,
    mut v___y_4817_: *mut LeanObject,
    mut v___y_4818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    v___x_4820_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4___redArg(v_recFVars_4810_, v_as_x27_4812_, v_b_4813_);
    return v___x_4820_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4___boxed(
    mut v_recFVars_4821_: *mut LeanObject,
    mut v_as_4822_: *mut LeanObject,
    mut v_as_x27_4823_: *mut LeanObject,
    mut v_b_4824_: *mut LeanObject,
    mut v_a_4825_: *mut LeanObject,
    mut v___y_4826_: *mut LeanObject,
    mut v___y_4827_: *mut LeanObject,
    mut v___y_4828_: *mut LeanObject,
    mut v___y_4829_: *mut LeanObject,
    mut v___y_4830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4831_: *mut LeanObject = core::ptr::null_mut();
    v_res_4831_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4(v_recFVars_4821_, v_as_4822_, v_as_x27_4823_, v_b_4824_, v_a_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
    lean_dec(v___y_4829_);
    lean_dec_ref(v___y_4828_);
    lean_dec(v___y_4827_);
    lean_dec_ref(v___y_4826_);
    lean_dec(v_as_x27_4823_);
    lean_dec(v_as_4822_);
    lean_dec_ref(v_recFVars_4821_);
    return v_res_4831_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5(
    mut v___x_4832_: *mut LeanObject,
    mut v_recFVars_4833_: *mut LeanObject,
    mut v___x_4834_: *mut LeanObject,
    mut v___x_4835_: *mut LeanObject,
    mut v_declName_4836_: *mut LeanObject,
    mut v_as_4837_: *mut LeanObject,
    mut v_as_x27_4838_: *mut LeanObject,
    mut v_b_4839_: *mut LeanObject,
    mut v_a_4840_: *mut LeanObject,
    mut v___y_4841_: *mut LeanObject,
    mut v___y_4842_: *mut LeanObject,
    mut v___y_4843_: *mut LeanObject,
    mut v___y_4844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    v___x_4846_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5___redArg(v___x_4832_, v_recFVars_4833_, v___x_4834_, v___x_4835_, v_declName_4836_, v_as_x27_4838_, v_b_4839_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
    return v___x_4846_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5___boxed(
    mut v___x_4847_: *mut LeanObject,
    mut v_recFVars_4848_: *mut LeanObject,
    mut v___x_4849_: *mut LeanObject,
    mut v___x_4850_: *mut LeanObject,
    mut v_declName_4851_: *mut LeanObject,
    mut v_as_4852_: *mut LeanObject,
    mut v_as_x27_4853_: *mut LeanObject,
    mut v_b_4854_: *mut LeanObject,
    mut v_a_4855_: *mut LeanObject,
    mut v___y_4856_: *mut LeanObject,
    mut v___y_4857_: *mut LeanObject,
    mut v___y_4858_: *mut LeanObject,
    mut v___y_4859_: *mut LeanObject,
    mut v___y_4860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4861_: *mut LeanObject = core::ptr::null_mut();
    v_res_4861_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5(v___x_4847_, v_recFVars_4848_, v___x_4849_, v___x_4850_, v_declName_4851_, v_as_4852_, v_as_x27_4853_, v_b_4854_, v_a_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
    lean_dec(v___y_4859_);
    lean_dec_ref(v___y_4858_);
    lean_dec(v___y_4857_);
    lean_dec_ref(v___y_4856_);
    lean_dec(v_as_x27_4853_);
    lean_dec(v_as_4852_);
    lean_dec(v_declName_4851_);
    lean_dec_ref(v___x_4850_);
    lean_dec_ref(v_recFVars_4848_);
    lean_dec(v___x_4847_);
    return v_res_4861_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6(
    mut v___x_4862_: *mut LeanObject,
    mut v___x_4863_: *mut LeanObject,
    mut v_recFVars_4864_: *mut LeanObject,
    mut v_a_4865_: *mut LeanObject,
    mut v_declName_4866_: *mut LeanObject,
    mut v_as_4867_: *mut LeanObject,
    mut v_as_x27_4868_: *mut LeanObject,
    mut v_b_4869_: *mut LeanObject,
    mut v_a_4870_: *mut LeanObject,
    mut v___y_4871_: *mut LeanObject,
    mut v___y_4872_: *mut LeanObject,
    mut v___y_4873_: *mut LeanObject,
    mut v___y_4874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    v___x_4876_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6___redArg(v___x_4862_, v___x_4863_, v_recFVars_4864_, v_a_4865_, v_declName_4866_, v_as_x27_4868_, v_b_4869_);
    return v___x_4876_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6___boxed(
    mut v___x_4877_: *mut LeanObject,
    mut v___x_4878_: *mut LeanObject,
    mut v_recFVars_4879_: *mut LeanObject,
    mut v_a_4880_: *mut LeanObject,
    mut v_declName_4881_: *mut LeanObject,
    mut v_as_4882_: *mut LeanObject,
    mut v_as_x27_4883_: *mut LeanObject,
    mut v_b_4884_: *mut LeanObject,
    mut v_a_4885_: *mut LeanObject,
    mut v___y_4886_: *mut LeanObject,
    mut v___y_4887_: *mut LeanObject,
    mut v___y_4888_: *mut LeanObject,
    mut v___y_4889_: *mut LeanObject,
    mut v___y_4890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4891_: *mut LeanObject = core::ptr::null_mut();
    v_res_4891_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6(v___x_4877_, v___x_4878_, v_recFVars_4879_, v_a_4880_, v_declName_4881_, v_as_4882_, v_as_x27_4883_, v_b_4884_, v_a_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
    lean_dec(v___y_4889_);
    lean_dec_ref(v___y_4888_);
    lean_dec(v___y_4887_);
    lean_dec_ref(v___y_4886_);
    lean_dec(v_as_x27_4883_);
    lean_dec(v_as_4882_);
    lean_dec(v_declName_4881_);
    lean_dec(v_a_4880_);
    lean_dec_ref(v_recFVars_4879_);
    lean_dec(v___x_4878_);
    lean_dec(v___x_4877_);
    return v_res_4891_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7(
    mut v___x_4892_: *mut LeanObject,
    mut v___x_4893_: *mut LeanObject,
    mut v___x_4894_: *mut LeanObject,
    mut v_recFVars_4895_: *mut LeanObject,
    mut v_as_4896_: *mut LeanObject,
    mut v_as_x27_4897_: *mut LeanObject,
    mut v_b_4898_: *mut LeanObject,
    mut v_a_4899_: *mut LeanObject,
    mut v___y_4900_: *mut LeanObject,
    mut v___y_4901_: *mut LeanObject,
    mut v___y_4902_: *mut LeanObject,
    mut v___y_4903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    v___x_4905_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___redArg(v___x_4892_, v___x_4893_, v___x_4894_, v_recFVars_4895_, v_as_x27_4897_, v_b_4898_);
    return v___x_4905_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___boxed(
    mut v___x_4906_: *mut LeanObject,
    mut v___x_4907_: *mut LeanObject,
    mut v___x_4908_: *mut LeanObject,
    mut v_recFVars_4909_: *mut LeanObject,
    mut v_as_4910_: *mut LeanObject,
    mut v_as_x27_4911_: *mut LeanObject,
    mut v_b_4912_: *mut LeanObject,
    mut v_a_4913_: *mut LeanObject,
    mut v___y_4914_: *mut LeanObject,
    mut v___y_4915_: *mut LeanObject,
    mut v___y_4916_: *mut LeanObject,
    mut v___y_4917_: *mut LeanObject,
    mut v___y_4918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4919_: *mut LeanObject = core::ptr::null_mut();
    v_res_4919_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7(v___x_4906_, v___x_4907_, v___x_4908_, v_recFVars_4909_, v_as_4910_, v_as_x27_4911_, v_b_4912_, v_a_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_);
    lean_dec(v___y_4917_);
    lean_dec_ref(v___y_4916_);
    lean_dec(v___y_4915_);
    lean_dec_ref(v___y_4914_);
    lean_dec(v_as_x27_4911_);
    lean_dec(v_as_4910_);
    lean_dec_ref(v_recFVars_4909_);
    lean_dec(v___x_4908_);
    lean_dec(v___x_4907_);
    lean_dec(v___x_4906_);
    return v_res_4919_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10(
    mut v___x_4920_: *mut LeanObject,
    mut v___x_4921_: *mut LeanObject,
    mut v_recFVars_4922_: *mut LeanObject,
    mut v_as_4923_: *mut LeanObject,
    mut v_as_x27_4924_: *mut LeanObject,
    mut v_b_4925_: *mut LeanObject,
    mut v_a_4926_: *mut LeanObject,
    mut v___y_4927_: *mut LeanObject,
    mut v___y_4928_: *mut LeanObject,
    mut v___y_4929_: *mut LeanObject,
    mut v___y_4930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    v___x_4932_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10___redArg(v___x_4920_, v___x_4921_, v_recFVars_4922_, v_as_x27_4924_, v_b_4925_);
    return v___x_4932_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10___boxed(
    mut v___x_4933_: *mut LeanObject,
    mut v___x_4934_: *mut LeanObject,
    mut v_recFVars_4935_: *mut LeanObject,
    mut v_as_4936_: *mut LeanObject,
    mut v_as_x27_4937_: *mut LeanObject,
    mut v_b_4938_: *mut LeanObject,
    mut v_a_4939_: *mut LeanObject,
    mut v___y_4940_: *mut LeanObject,
    mut v___y_4941_: *mut LeanObject,
    mut v___y_4942_: *mut LeanObject,
    mut v___y_4943_: *mut LeanObject,
    mut v___y_4944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4945_: *mut LeanObject = core::ptr::null_mut();
    v_res_4945_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10(v___x_4933_, v___x_4934_, v_recFVars_4935_, v_as_4936_, v_as_x27_4937_, v_b_4938_, v_a_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
    lean_dec(v___y_4943_);
    lean_dec_ref(v___y_4942_);
    lean_dec(v___y_4941_);
    lean_dec_ref(v___y_4940_);
    lean_dec(v_as_x27_4937_);
    lean_dec(v_as_4936_);
    lean_dec_ref(v_recFVars_4935_);
    lean_dec(v___x_4934_);
    lean_dec(v___x_4933_);
    return v_res_4945_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11(
    mut v_00_u03b1_4946_: *mut LeanObject,
    mut v_msg_4947_: *mut LeanObject,
    mut v___y_4948_: *mut LeanObject,
    mut v___y_4949_: *mut LeanObject,
    mut v___y_4950_: *mut LeanObject,
    mut v___y_4951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
    v___x_4953_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(v_msg_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
    return v___x_4953_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___boxed(
    mut v_00_u03b1_4954_: *mut LeanObject,
    mut v_msg_4955_: *mut LeanObject,
    mut v___y_4956_: *mut LeanObject,
    mut v___y_4957_: *mut LeanObject,
    mut v___y_4958_: *mut LeanObject,
    mut v___y_4959_: *mut LeanObject,
    mut v___y_4960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4961_: *mut LeanObject = core::ptr::null_mut();
    v_res_4961_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11(v_00_u03b1_4954_, v_msg_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_);
    lean_dec(v___y_4959_);
    lean_dec_ref(v___y_4958_);
    lean_dec(v___y_4957_);
    lean_dec_ref(v___y_4956_);
    return v_res_4961_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3(
    mut v_00_u03b1_4962_: *mut LeanObject,
    mut v_constName_4963_: *mut LeanObject,
    mut v___y_4964_: *mut LeanObject,
    mut v___y_4965_: *mut LeanObject,
    mut v___y_4966_: *mut LeanObject,
    mut v___y_4967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    v___x_4969_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3___redArg(v_constName_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
    return v___x_4969_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3___boxed(
    mut v_00_u03b1_4970_: *mut LeanObject,
    mut v_constName_4971_: *mut LeanObject,
    mut v___y_4972_: *mut LeanObject,
    mut v___y_4973_: *mut LeanObject,
    mut v___y_4974_: *mut LeanObject,
    mut v___y_4975_: *mut LeanObject,
    mut v___y_4976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4977_: *mut LeanObject = core::ptr::null_mut();
    v_res_4977_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3(v_00_u03b1_4970_, v_constName_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
    lean_dec(v___y_4975_);
    lean_dec_ref(v___y_4974_);
    lean_dec(v___y_4973_);
    lean_dec_ref(v___y_4972_);
    return v_res_4977_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6(
    mut v_00_u03b1_4978_: *mut LeanObject,
    mut v_ref_4979_: *mut LeanObject,
    mut v_constName_4980_: *mut LeanObject,
    mut v___y_4981_: *mut LeanObject,
    mut v___y_4982_: *mut LeanObject,
    mut v___y_4983_: *mut LeanObject,
    mut v___y_4984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    v___x_4986_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg(v_ref_4979_, v_constName_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_);
    return v___x_4986_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b1_4987_: *mut LeanObject,
    mut v_ref_4988_: *mut LeanObject,
    mut v_constName_4989_: *mut LeanObject,
    mut v___y_4990_: *mut LeanObject,
    mut v___y_4991_: *mut LeanObject,
    mut v___y_4992_: *mut LeanObject,
    mut v___y_4993_: *mut LeanObject,
    mut v___y_4994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4995_: *mut LeanObject = core::ptr::null_mut();
    v_res_4995_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6(v_00_u03b1_4987_, v_ref_4988_, v_constName_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_);
    lean_dec(v___y_4993_);
    lean_dec_ref(v___y_4992_);
    lean_dec(v___y_4991_);
    lean_dec_ref(v___y_4990_);
    lean_dec(v_ref_4988_);
    return v_res_4995_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16(
    mut v_00_u03b1_4996_: *mut LeanObject,
    mut v_ref_4997_: *mut LeanObject,
    mut v_msg_4998_: *mut LeanObject,
    mut v_declHint_4999_: *mut LeanObject,
    mut v___y_5000_: *mut LeanObject,
    mut v___y_5001_: *mut LeanObject,
    mut v___y_5002_: *mut LeanObject,
    mut v___y_5003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    v___x_5005_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16___redArg(v_ref_4997_, v_msg_4998_, v_declHint_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
    return v___x_5005_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16___boxed(
    mut v_00_u03b1_5006_: *mut LeanObject,
    mut v_ref_5007_: *mut LeanObject,
    mut v_msg_5008_: *mut LeanObject,
    mut v_declHint_5009_: *mut LeanObject,
    mut v___y_5010_: *mut LeanObject,
    mut v___y_5011_: *mut LeanObject,
    mut v___y_5012_: *mut LeanObject,
    mut v___y_5013_: *mut LeanObject,
    mut v___y_5014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5015_: *mut LeanObject = core::ptr::null_mut();
    v_res_5015_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16(v_00_u03b1_5006_, v_ref_5007_, v_msg_5008_, v_declHint_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
    lean_dec(v___y_5013_);
    lean_dec_ref(v___y_5012_);
    lean_dec(v___y_5011_);
    lean_dec_ref(v___y_5010_);
    lean_dec(v_ref_5007_);
    return v_res_5015_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18(
    mut v_msg_5016_: *mut LeanObject,
    mut v_declHint_5017_: *mut LeanObject,
    mut v___y_5018_: *mut LeanObject,
    mut v___y_5019_: *mut LeanObject,
    mut v___y_5020_: *mut LeanObject,
    mut v___y_5021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    v___x_5023_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg(v_msg_5016_, v_declHint_5017_, v___y_5021_);
    return v___x_5023_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___boxed(
    mut v_msg_5024_: *mut LeanObject,
    mut v_declHint_5025_: *mut LeanObject,
    mut v___y_5026_: *mut LeanObject,
    mut v___y_5027_: *mut LeanObject,
    mut v___y_5028_: *mut LeanObject,
    mut v___y_5029_: *mut LeanObject,
    mut v___y_5030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5031_: *mut LeanObject = core::ptr::null_mut();
    v_res_5031_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18(v_msg_5024_, v_declHint_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
    lean_dec(v___y_5029_);
    lean_dec_ref(v___y_5028_);
    lean_dec(v___y_5027_);
    lean_dec_ref(v___y_5026_);
    return v_res_5031_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18(
    mut v_00_u03b1_5032_: *mut LeanObject,
    mut v_ref_5033_: *mut LeanObject,
    mut v_msg_5034_: *mut LeanObject,
    mut v___y_5035_: *mut LeanObject,
    mut v___y_5036_: *mut LeanObject,
    mut v___y_5037_: *mut LeanObject,
    mut v___y_5038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    v___x_5040_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18___redArg(v_ref_5033_, v_msg_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
    return v___x_5040_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18___boxed(
    mut v_00_u03b1_5041_: *mut LeanObject,
    mut v_ref_5042_: *mut LeanObject,
    mut v_msg_5043_: *mut LeanObject,
    mut v___y_5044_: *mut LeanObject,
    mut v___y_5045_: *mut LeanObject,
    mut v___y_5046_: *mut LeanObject,
    mut v___y_5047_: *mut LeanObject,
    mut v___y_5048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5049_: *mut LeanObject = core::ptr::null_mut();
    v_res_5049_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18(v_00_u03b1_5041_, v_ref_5042_, v_msg_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_);
    lean_dec(v___y_5047_);
    lean_dec_ref(v___y_5046_);
    lean_dec(v___y_5045_);
    lean_dec_ref(v___y_5044_);
    lean_dec(v_ref_5042_);
    return v_res_5049_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    v___x_5050_ = lean_unsigned_to_nat(32);
    v___x_5051_ = lean_mk_empty_array_with_capacity(v___x_5050_);
    v___x_5052_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5052_, 0, v___x_5051_);
    return v___x_5052_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5053_: usize = 0;
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    v___x_5053_ = 5usize;
    v___x_5054_ = lean_unsigned_to_nat(0);
    v___x_5055_ = lean_unsigned_to_nat(32);
    v___x_5056_ = lean_mk_empty_array_with_capacity(v___x_5055_);
    v___x_5057_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__0);
    v___x_5058_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_5058_, 0, v___x_5057_);
    lean_ctor_set(v___x_5058_, 1, v___x_5056_);
    lean_ctor_set(v___x_5058_, 2, v___x_5054_);
    lean_ctor_set(v___x_5058_, 3, v___x_5054_);
    lean_ctor_set_usize(v___x_5058_, 4, v___x_5053_);
    return v___x_5058_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg(
    mut v___y_5059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5076_: u8 = 0;
    let mut v_tid_5077_: u64 = 0;
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5080_: u8 = 0;
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5090_: u8 = 0;
    let mut v_unused_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5092_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5061_ = lean_st_ref_get(v___y_5059_);
                v_traceState_5062_ = lean_ctor_get(v___x_5061_, 4);
                lean_inc_ref(v_traceState_5062_);
                lean_dec(v___x_5061_);
                v_traces_5063_ = lean_ctor_get(v_traceState_5062_, 0);
                lean_inc_ref(v_traces_5063_);
                lean_dec_ref(v_traceState_5062_);
                v___x_5064_ = lean_st_ref_take(v___y_5059_);
                v_traceState_5065_ = lean_ctor_get(v___x_5064_, 4);
                v_env_5066_ = lean_ctor_get(v___x_5064_, 0);
                v_nextMacroScope_5067_ = lean_ctor_get(v___x_5064_, 1);
                v_ngen_5068_ = lean_ctor_get(v___x_5064_, 2);
                v_auxDeclNGen_5069_ = lean_ctor_get(v___x_5064_, 3);
                v_cache_5070_ = lean_ctor_get(v___x_5064_, 5);
                v_messages_5071_ = lean_ctor_get(v___x_5064_, 6);
                v_infoState_5072_ = lean_ctor_get(v___x_5064_, 7);
                v_snapshotTasks_5073_ = lean_ctor_get(v___x_5064_, 8);
                v_isSharedCheck_5092_ = (!lean_is_exclusive(v___x_5064_)) as u8;
                if v_isSharedCheck_5092_ == 0 {
                    v___x_5075_ = v___x_5064_;
                    v_isShared_5076_ = v_isSharedCheck_5092_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5073_);
                    lean_inc(v_infoState_5072_);
                    lean_inc(v_messages_5071_);
                    lean_inc(v_cache_5070_);
                    lean_inc(v_traceState_5065_);
                    lean_inc(v_auxDeclNGen_5069_);
                    lean_inc(v_ngen_5068_);
                    lean_inc(v_nextMacroScope_5067_);
                    lean_inc(v_env_5066_);
                    lean_dec(v___x_5064_);
                    v___x_5075_ = lean_box(0);
                    v_isShared_5076_ = v_isSharedCheck_5092_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_5077_ = lean_ctor_get_uint64(
                    v_traceState_5065_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5090_ = (!lean_is_exclusive(v_traceState_5065_)) as u8;
                if v_isSharedCheck_5090_ == 0 {
                    v_unused_5091_ = lean_ctor_get(v_traceState_5065_, 0);
                    lean_dec(v_unused_5091_);
                    v___x_5079_ = v_traceState_5065_;
                    v_isShared_5080_ = v_isSharedCheck_5090_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_traceState_5065_);
                    v___x_5079_ = lean_box(0);
                    v_isShared_5080_ = v_isSharedCheck_5090_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5081_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__1);
                if v_isShared_5080_ == 0 {
                    lean_ctor_set(v___x_5079_, 0, v___x_5081_);
                    v___x_5083_ = v___x_5079_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5081_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5089_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5077_,
                    );
                    v___x_5083_ = v_reuseFailAlloc_5089_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5076_ == 0 {
                    lean_ctor_set(v___x_5075_, 4, v___x_5083_);
                    v___x_5085_ = v___x_5075_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_env_5066_);
                    lean_ctor_set(v_reuseFailAlloc_5088_, 1, v_nextMacroScope_5067_);
                    lean_ctor_set(v_reuseFailAlloc_5088_, 2, v_ngen_5068_);
                    lean_ctor_set(v_reuseFailAlloc_5088_, 3, v_auxDeclNGen_5069_);
                    lean_ctor_set(v_reuseFailAlloc_5088_, 4, v___x_5083_);
                    lean_ctor_set(v_reuseFailAlloc_5088_, 5, v_cache_5070_);
                    lean_ctor_set(v_reuseFailAlloc_5088_, 6, v_messages_5071_);
                    lean_ctor_set(v_reuseFailAlloc_5088_, 7, v_infoState_5072_);
                    lean_ctor_set(v_reuseFailAlloc_5088_, 8, v_snapshotTasks_5073_);
                    v___x_5085_ = v_reuseFailAlloc_5088_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5086_ = lean_st_ref_set(v___y_5059_, v___x_5085_);
                v___x_5087_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5087_, 0, v_traces_5063_);
                return v___x_5087_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___boxed(
    mut v___y_5093_: *mut LeanObject,
    mut v___y_5094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5095_: *mut LeanObject = core::ptr::null_mut();
    v_res_5095_ =
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg(
            v___y_5093_,
        );
    lean_dec(v___y_5093_);
    return v_res_5095_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1(
    mut v___y_5096_: *mut LeanObject,
    mut v___y_5097_: *mut LeanObject,
    mut v___y_5098_: *mut LeanObject,
    mut v___y_5099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    v___x_5101_ =
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg(
            v___y_5099_,
        );
    return v___x_5101_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___boxed(
    mut v___y_5102_: *mut LeanObject,
    mut v___y_5103_: *mut LeanObject,
    mut v___y_5104_: *mut LeanObject,
    mut v___y_5105_: *mut LeanObject,
    mut v___y_5106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5107_: *mut LeanObject = core::ptr::null_mut();
    v_res_5107_ =
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1(
            v___y_5102_,
            v___y_5103_,
            v___y_5104_,
            v___y_5105_,
        );
    lean_dec(v___y_5105_);
    lean_dec_ref(v___y_5104_);
    lean_dec(v___y_5103_);
    lean_dec_ref(v___y_5102_);
    return v_res_5107_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_mkCasesOn_spec__2(
    mut v_opts_5108_: *mut LeanObject,
    mut v_opt_5109_: *mut LeanObject,
) -> u8 {
    let mut v_name_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    v_name_5110_ = lean_ctor_get(v_opt_5109_, 0);
    v_defValue_5111_ = lean_ctor_get(v_opt_5109_, 1);
    v_map_5112_ = lean_ctor_get(v_opts_5108_, 0);
    v___x_5113_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5112_,
            v_name_5110_,
        );
    if lean_obj_tag(v___x_5113_) == 0 {
        let mut v___x_5114_: u8 = 0;
        v___x_5114_ = (lean_unbox(v_defValue_5111_) as u8);
        return v___x_5114_;
    } else {
        let mut v_val_5115_: *mut LeanObject = core::ptr::null_mut();
        v_val_5115_ = lean_ctor_get(v___x_5113_, 0);
        lean_inc(v_val_5115_);
        lean_dec_ref_known(v___x_5113_, 1);
        if lean_obj_tag(v_val_5115_) == 1 {
            let mut v_v_5116_: u8 = 0;
            v_v_5116_ = lean_ctor_get_uint8(v_val_5115_, 0 as u32);
            lean_dec_ref_known(v_val_5115_, 0);
            return v_v_5116_;
        } else {
            let mut v___x_5117_: u8 = 0;
            lean_dec(v_val_5115_);
            v___x_5117_ = (lean_unbox(v_defValue_5111_) as u8);
            return v___x_5117_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_mkCasesOn_spec__2___boxed(
    mut v_opts_5118_: *mut LeanObject,
    mut v_opt_5119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5120_: u8 = 0;
    let mut v_r_5121_: *mut LeanObject = core::ptr::null_mut();
    v_res_5120_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__2(v_opts_5118_, v_opt_5119_);
    lean_dec_ref(v_opt_5119_);
    lean_dec_ref(v_opts_5118_);
    v_r_5121_ = lean_box((v_res_5120_) as usize);
    return v_r_5121_;
}
pub unsafe fn l_Lean_mkCasesOn___lam__0(
    mut v_declName_5122_: *mut LeanObject,
    mut v_x_5123_: *mut LeanObject,
    mut v___y_5124_: *mut LeanObject,
    mut v___y_5125_: *mut LeanObject,
    mut v___y_5126_: *mut LeanObject,
    mut v___y_5127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    v___x_5129_ = l_Lean_MessageData_ofName(v_declName_5122_);
    v___x_5130_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5130_, 0, v___x_5129_);
    return v___x_5130_;
}
pub unsafe fn l_Lean_mkCasesOn___lam__0___boxed(
    mut v_declName_5131_: *mut LeanObject,
    mut v_x_5132_: *mut LeanObject,
    mut v___y_5133_: *mut LeanObject,
    mut v___y_5134_: *mut LeanObject,
    mut v___y_5135_: *mut LeanObject,
    mut v___y_5136_: *mut LeanObject,
    mut v___y_5137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5138_: *mut LeanObject = core::ptr::null_mut();
    v_res_5138_ = l_Lean_mkCasesOn___lam__0(
        v_declName_5131_,
        v_x_5132_,
        v___y_5133_,
        v___y_5134_,
        v___y_5135_,
        v___y_5136_,
    );
    lean_dec(v___y_5136_);
    lean_dec_ref(v___y_5135_);
    lean_dec(v___y_5134_);
    lean_dec_ref(v___y_5133_);
    lean_dec_ref(v_x_5132_);
    return v_res_5138_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__7(
    mut v_opts_5139_: *mut LeanObject,
    mut v_opt_5140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    v_name_5141_ = lean_ctor_get(v_opt_5140_, 0);
    v_defValue_5142_ = lean_ctor_get(v_opt_5140_, 1);
    v_map_5143_ = lean_ctor_get(v_opts_5139_, 0);
    v___x_5144_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5143_,
            v_name_5141_,
        );
    if lean_obj_tag(v___x_5144_) == 0 {
        lean_inc(v_defValue_5142_);
        return v_defValue_5142_;
    } else {
        let mut v_val_5145_: *mut LeanObject = core::ptr::null_mut();
        v_val_5145_ = lean_ctor_get(v___x_5144_, 0);
        lean_inc(v_val_5145_);
        lean_dec_ref_known(v___x_5144_, 1);
        if lean_obj_tag(v_val_5145_) == 3 {
            let mut v_v_5146_: *mut LeanObject = core::ptr::null_mut();
            v_v_5146_ = lean_ctor_get(v_val_5145_, 0);
            lean_inc(v_v_5146_);
            lean_dec_ref_known(v_val_5145_, 1);
            return v_v_5146_;
        } else {
            lean_dec(v_val_5145_);
            lean_inc(v_defValue_5142_);
            return v_defValue_5142_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__7___boxed(
    mut v_opts_5147_: *mut LeanObject,
    mut v_opt_5148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5149_: *mut LeanObject = core::ptr::null_mut();
    v_res_5149_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__7(v_opts_5147_, v_opt_5148_);
    lean_dec_ref(v_opt_5148_);
    lean_dec_ref(v_opts_5147_);
    return v_res_5149_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6___redArg(
    mut v_x_5150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5155_: u8 = 0;
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5159_: u8 = 0;
    let mut v_a_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5163_: u8 = 0;
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5150_) == 0 {
                    v_a_5152_ = lean_ctor_get(v_x_5150_, 0);
                    v_isSharedCheck_5159_ = (!lean_is_exclusive(v_x_5150_)) as u8;
                    if v_isSharedCheck_5159_ == 0 {
                        v___x_5154_ = v_x_5150_;
                        v_isShared_5155_ = v_isSharedCheck_5159_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5152_);
                        lean_dec(v_x_5150_);
                        v___x_5154_ = lean_box(0);
                        v_isShared_5155_ = v_isSharedCheck_5159_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5160_ = lean_ctor_get(v_x_5150_, 0);
                    v_isSharedCheck_5167_ = (!lean_is_exclusive(v_x_5150_)) as u8;
                    if v_isSharedCheck_5167_ == 0 {
                        v___x_5162_ = v_x_5150_;
                        v_isShared_5163_ = v_isSharedCheck_5167_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5160_);
                        lean_dec(v_x_5150_);
                        v___x_5162_ = lean_box(0);
                        v_isShared_5163_ = v_isSharedCheck_5167_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5155_ == 0 {
                    lean_ctor_set_tag(v___x_5154_, 1);
                    v___x_5157_ = v___x_5154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5158_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5158_, 0, v_a_5152_);
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
                    lean_ctor_set_tag(v___x_5162_, 0);
                    v___x_5165_ = v___x_5162_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5166_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5166_, 0, v_a_5160_);
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
    mut v_x_5168_: *mut LeanObject,
    mut v___y_5169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5170_: *mut LeanObject = core::ptr::null_mut();
    v_res_5170_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6___redArg(v_x_5168_);
    return v_res_5170_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__4(
    mut v_e_5171_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_e_5171_) == 0 {
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
    mut v_e_5174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5175_: u8 = 0;
    let mut v_r_5176_: *mut LeanObject = core::ptr::null_mut();
    v_res_5175_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__4(v_e_5174_);
    lean_dec_ref(v_e_5174_);
    v_r_5176_ = lean_box((v_res_5175_) as usize);
    return v_r_5176_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5_spec__6(
    mut v_sz_5177_: usize,
    mut v_i_5178_: usize,
    mut v_bs_5179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5180_: u8 = 0;
    let mut v_v_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: usize = 0;
    let mut v___x_5186_: usize = 0;
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5180_ = lean_usize_dec_lt(v_i_5178_, v_sz_5177_);
                if v___x_5180_ == 0 {
                    return v_bs_5179_;
                } else {
                    v_v_5181_ = lean_array_uget_borrowed(v_bs_5179_, v_i_5178_);
                    v_msg_5182_ = lean_ctor_get(v_v_5181_, 1);
                    lean_inc_ref(v_msg_5182_);
                    v___x_5183_ = lean_unsigned_to_nat(0);
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
    mut v_sz_5189_: *mut LeanObject,
    mut v_i_5190_: *mut LeanObject,
    mut v_bs_5191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5192_: usize = 0;
    let mut v_i_boxed_5193_: usize = 0;
    let mut v_res_5194_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5192_ = lean_unbox_usize(v_sz_5189_);
    lean_dec(v_sz_5189_);
    v_i_boxed_5193_ = lean_unbox_usize(v_i_5190_);
    lean_dec(v_i_5190_);
    v_res_5194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5_spec__6(v_sz_boxed_5192_, v_i_boxed_5193_, v_bs_5191_);
    return v_res_5194_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5(
    mut v_oldTraces_5195_: *mut LeanObject,
    mut v_data_5196_: *mut LeanObject,
    mut v_ref_5197_: *mut LeanObject,
    mut v_msg_5198_: *mut LeanObject,
    mut v___y_5199_: *mut LeanObject,
    mut v___y_5200_: *mut LeanObject,
    mut v___y_5201_: *mut LeanObject,
    mut v___y_5202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5216_: u8 = 0;
    let mut v_cancelTk_x3f_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5218_: u8 = 0;
    let mut v_inheritedTraceOptions_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traces_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5226_: usize = 0;
    let mut v___x_5227_: usize = 0;
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5234_: u8 = 0;
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5247_: u8 = 0;
    let mut v_tid_5248_: u64 = 0;
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5265_: u8 = 0;
    let mut v_unused_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5267_: u8 = 0;
    let mut v_isSharedCheck_5268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5204_ = lean_ctor_get(v___y_5201_, 0);
                v_fileMap_5205_ = lean_ctor_get(v___y_5201_, 1);
                v_options_5206_ = lean_ctor_get(v___y_5201_, 2);
                v_currRecDepth_5207_ = lean_ctor_get(v___y_5201_, 3);
                v_maxRecDepth_5208_ = lean_ctor_get(v___y_5201_, 4);
                v_ref_5209_ = lean_ctor_get(v___y_5201_, 5);
                v_currNamespace_5210_ = lean_ctor_get(v___y_5201_, 6);
                v_openDecls_5211_ = lean_ctor_get(v___y_5201_, 7);
                v_initHeartbeats_5212_ = lean_ctor_get(v___y_5201_, 8);
                v_maxHeartbeats_5213_ = lean_ctor_get(v___y_5201_, 9);
                v_quotContext_5214_ = lean_ctor_get(v___y_5201_, 10);
                v_currMacroScope_5215_ = lean_ctor_get(v___y_5201_, 11);
                v_diag_5216_ = lean_ctor_get_uint8(
                    v___y_5201_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5217_ = lean_ctor_get(v___y_5201_, 12);
                v_suppressElabErrors_5218_ = lean_ctor_get_uint8(
                    v___y_5201_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5219_ = lean_ctor_get(v___y_5201_, 13);
                v___x_5220_ = lean_st_ref_get(v___y_5202_);
                v_traceState_5221_ = lean_ctor_get(v___x_5220_, 4);
                lean_inc_ref(v_traceState_5221_);
                lean_dec(v___x_5220_);
                v_traces_5222_ = lean_ctor_get(v_traceState_5221_, 0);
                lean_inc_ref(v_traces_5222_);
                lean_dec_ref(v_traceState_5221_);
                v_ref_5223_ = l_Lean_replaceRef(v_ref_5197_, v_ref_5209_);
                lean_inc_ref(v_inheritedTraceOptions_5219_);
                lean_inc(v_cancelTk_x3f_5217_);
                lean_inc(v_currMacroScope_5215_);
                lean_inc(v_quotContext_5214_);
                lean_inc(v_maxHeartbeats_5213_);
                lean_inc(v_initHeartbeats_5212_);
                lean_inc(v_openDecls_5211_);
                lean_inc(v_currNamespace_5210_);
                lean_inc(v_maxRecDepth_5208_);
                lean_inc(v_currRecDepth_5207_);
                lean_inc_ref(v_options_5206_);
                lean_inc_ref(v_fileMap_5205_);
                lean_inc_ref(v_fileName_5204_);
                v___x_5224_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_5224_, 0, v_fileName_5204_);
                lean_ctor_set(v___x_5224_, 1, v_fileMap_5205_);
                lean_ctor_set(v___x_5224_, 2, v_options_5206_);
                lean_ctor_set(v___x_5224_, 3, v_currRecDepth_5207_);
                lean_ctor_set(v___x_5224_, 4, v_maxRecDepth_5208_);
                lean_ctor_set(v___x_5224_, 5, v_ref_5223_);
                lean_ctor_set(v___x_5224_, 6, v_currNamespace_5210_);
                lean_ctor_set(v___x_5224_, 7, v_openDecls_5211_);
                lean_ctor_set(v___x_5224_, 8, v_initHeartbeats_5212_);
                lean_ctor_set(v___x_5224_, 9, v_maxHeartbeats_5213_);
                lean_ctor_set(v___x_5224_, 10, v_quotContext_5214_);
                lean_ctor_set(v___x_5224_, 11, v_currMacroScope_5215_);
                lean_ctor_set(v___x_5224_, 12, v_cancelTk_x3f_5217_);
                lean_ctor_set(v___x_5224_, 13, v_inheritedTraceOptions_5219_);
                lean_ctor_set_uint8(
                    v___x_5224_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_5216_,
                );
                lean_ctor_set_uint8(
                    v___x_5224_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5218_,
                );
                v___x_5225_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5222_);
                lean_dec_ref(v_traces_5222_);
                v_sz_5226_ = lean_array_size(v___x_5225_);
                v___x_5227_ = 0usize;
                v___x_5228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5_spec__6(v_sz_5226_, v___x_5227_, v___x_5225_);
                v_msg_5229_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v_msg_5229_, 0, v_data_5196_);
                lean_ctor_set(v_msg_5229_, 1, v_msg_5198_);
                lean_ctor_set(v_msg_5229_, 2, v___x_5228_);
                v___x_5230_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11_spec__13(v_msg_5229_, v___y_5199_, v___y_5200_, v___x_5224_, v___y_5202_);
                lean_dec_ref_known(v___x_5224_, 14);
                v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
                v_isSharedCheck_5268_ = (!lean_is_exclusive(v___x_5230_)) as u8;
                if v_isSharedCheck_5268_ == 0 {
                    v___x_5233_ = v___x_5230_;
                    v_isShared_5234_ = v_isSharedCheck_5268_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5231_);
                    lean_dec(v___x_5230_);
                    v___x_5233_ = lean_box(0);
                    v_isShared_5234_ = v_isSharedCheck_5268_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5235_ = lean_st_ref_take(v___y_5202_);
                v_traceState_5236_ = lean_ctor_get(v___x_5235_, 4);
                v_env_5237_ = lean_ctor_get(v___x_5235_, 0);
                v_nextMacroScope_5238_ = lean_ctor_get(v___x_5235_, 1);
                v_ngen_5239_ = lean_ctor_get(v___x_5235_, 2);
                v_auxDeclNGen_5240_ = lean_ctor_get(v___x_5235_, 3);
                v_cache_5241_ = lean_ctor_get(v___x_5235_, 5);
                v_messages_5242_ = lean_ctor_get(v___x_5235_, 6);
                v_infoState_5243_ = lean_ctor_get(v___x_5235_, 7);
                v_snapshotTasks_5244_ = lean_ctor_get(v___x_5235_, 8);
                v_isSharedCheck_5267_ = (!lean_is_exclusive(v___x_5235_)) as u8;
                if v_isSharedCheck_5267_ == 0 {
                    v___x_5246_ = v___x_5235_;
                    v_isShared_5247_ = v_isSharedCheck_5267_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5244_);
                    lean_inc(v_infoState_5243_);
                    lean_inc(v_messages_5242_);
                    lean_inc(v_cache_5241_);
                    lean_inc(v_traceState_5236_);
                    lean_inc(v_auxDeclNGen_5240_);
                    lean_inc(v_ngen_5239_);
                    lean_inc(v_nextMacroScope_5238_);
                    lean_inc(v_env_5237_);
                    lean_dec(v___x_5235_);
                    v___x_5246_ = lean_box(0);
                    v_isShared_5247_ = v_isSharedCheck_5267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5248_ = lean_ctor_get_uint64(
                    v_traceState_5236_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5265_ = (!lean_is_exclusive(v_traceState_5236_)) as u8;
                if v_isSharedCheck_5265_ == 0 {
                    v_unused_5266_ = lean_ctor_get(v_traceState_5236_, 0);
                    lean_dec(v_unused_5266_);
                    v___x_5250_ = v_traceState_5236_;
                    v_isShared_5251_ = v_isSharedCheck_5265_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_traceState_5236_);
                    v___x_5250_ = lean_box(0);
                    v_isShared_5251_ = v_isSharedCheck_5265_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5252_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5252_, 0, v_ref_5197_);
                lean_ctor_set(v___x_5252_, 1, v_a_5231_);
                v___x_5253_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5195_, v___x_5252_);
                if v_isShared_5251_ == 0 {
                    lean_ctor_set(v___x_5250_, 0, v___x_5253_);
                    v___x_5255_ = v___x_5250_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5264_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5264_, 0, v___x_5253_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5264_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5248_,
                    );
                    v___x_5255_ = v_reuseFailAlloc_5264_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5247_ == 0 {
                    lean_ctor_set(v___x_5246_, 4, v___x_5255_);
                    v___x_5257_ = v___x_5246_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_env_5237_);
                    lean_ctor_set(v_reuseFailAlloc_5263_, 1, v_nextMacroScope_5238_);
                    lean_ctor_set(v_reuseFailAlloc_5263_, 2, v_ngen_5239_);
                    lean_ctor_set(v_reuseFailAlloc_5263_, 3, v_auxDeclNGen_5240_);
                    lean_ctor_set(v_reuseFailAlloc_5263_, 4, v___x_5255_);
                    lean_ctor_set(v_reuseFailAlloc_5263_, 5, v_cache_5241_);
                    lean_ctor_set(v_reuseFailAlloc_5263_, 6, v_messages_5242_);
                    lean_ctor_set(v_reuseFailAlloc_5263_, 7, v_infoState_5243_);
                    lean_ctor_set(v_reuseFailAlloc_5263_, 8, v_snapshotTasks_5244_);
                    v___x_5257_ = v_reuseFailAlloc_5263_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5258_ = lean_st_ref_set(v___y_5202_, v___x_5257_);
                v___x_5259_ = lean_box(0);
                if v_isShared_5234_ == 0 {
                    lean_ctor_set(v___x_5233_, 0, v___x_5259_);
                    v___x_5261_ = v___x_5233_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5262_, 0, v___x_5259_);
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
    mut v_oldTraces_5269_: *mut LeanObject,
    mut v_data_5270_: *mut LeanObject,
    mut v_ref_5271_: *mut LeanObject,
    mut v_msg_5272_: *mut LeanObject,
    mut v___y_5273_: *mut LeanObject,
    mut v___y_5274_: *mut LeanObject,
    mut v___y_5275_: *mut LeanObject,
    mut v___y_5276_: *mut LeanObject,
    mut v___y_5277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5278_: *mut LeanObject = core::ptr::null_mut();
    v_res_5278_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5(v_oldTraces_5269_, v_data_5270_, v_ref_5271_, v_msg_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
    lean_dec(v___y_5276_);
    lean_dec_ref(v___y_5275_);
    lean_dec(v___y_5274_);
    lean_dec_ref(v___y_5273_);
    return v_res_5278_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    v___x_5280_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__0;
    v___x_5281_ = l_Lean_stringToMessageData(v___x_5280_);
    return v___x_5281_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__2()
-> f64 {
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: f64 = 0.0;
    v___x_5282_ = lean_unsigned_to_nat(0);
    v___x_5283_ = lean_float_of_nat(v___x_5282_);
    return v___x_5283_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__4()
-> *mut LeanObject {
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    v___x_5285_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__3;
    v___x_5286_ = l_Lean_stringToMessageData(v___x_5285_);
    return v___x_5286_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__5()
-> f64 {
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: f64 = 0.0;
    v___x_5287_ = lean_unsigned_to_nat(1000);
    v___x_5288_ = lean_float_of_nat(v___x_5287_);
    return v___x_5288_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3(
    mut v_cls_5289_: *mut LeanObject,
    mut v_collapsed_5290_: u8,
    mut v_tag_5291_: *mut LeanObject,
    mut v_opts_5292_: *mut LeanObject,
    mut v_clsEnabled_5293_: u8,
    mut v_oldTraces_5294_: *mut LeanObject,
    mut v_msg_5295_: *mut LeanObject,
    mut v_resStartStop_5296_: *mut LeanObject,
    mut v___y_5297_: *mut LeanObject,
    mut v___y_5298_: *mut LeanObject,
    mut v___y_5299_: *mut LeanObject,
    mut v___y_5300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5306_: u8 = 0;
    let mut v___y_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5317_: u8 = 0;
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: u8 = 0;
    let mut v___y_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_5323_: u8 = 0;
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: f64 = 0.0;
    let mut v_data_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: f64 = 0.0;
    let mut v___x_5337_: f64 = 0.0;
    let mut v_reuseFailAlloc_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5346_: u8 = 0;
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5359_: u8 = 0;
    let mut v_tid_5360_: u64 = 0;
    let mut v_traces_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5364_: u8 = 0;
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5374_: u8 = 0;
    let mut v_isSharedCheck_5375_: u8 = 0;
    let mut v___y_5377_: f64 = 0.0;
    let mut v___x_5378_: f64 = 0.0;
    let mut v___x_5379_: f64 = 0.0;
    let mut v___x_5380_: f64 = 0.0;
    let mut v___x_5381_: u8 = 0;
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: u8 = 0;
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: f64 = 0.0;
    let mut v___x_5387_: f64 = 0.0;
    let mut v___x_5388_: f64 = 0.0;
    let mut v___x_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: f64 = 0.0;
    let mut v_isSharedCheck_5392_: u8 = 0;
    let mut v_isSharedCheck_5393_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5302_ = lean_ctor_get(v_resStartStop_5296_, 0);
                v_snd_5303_ = lean_ctor_get(v_resStartStop_5296_, 1);
                v_isSharedCheck_5393_ = (!lean_is_exclusive(v_resStartStop_5296_)) as u8;
                if v_isSharedCheck_5393_ == 0 {
                    v___x_5305_ = v_resStartStop_5296_;
                    v_isShared_5306_ = v_isSharedCheck_5393_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_5303_);
                    lean_inc(v_fst_5302_);
                    lean_dec(v_resStartStop_5296_);
                    v___x_5305_ = lean_box(0);
                    v_isShared_5306_ = v_isSharedCheck_5393_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_5313_ = lean_ctor_get(v_snd_5303_, 0);
                v_snd_5314_ = lean_ctor_get(v_snd_5303_, 1);
                v_isSharedCheck_5392_ = (!lean_is_exclusive(v_snd_5303_)) as u8;
                if v_isSharedCheck_5392_ == 0 {
                    v___x_5316_ = v_snd_5303_;
                    v_isShared_5317_ = v_isSharedCheck_5392_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_5314_);
                    lean_inc(v_fst_5313_);
                    lean_dec(v_snd_5303_);
                    v___x_5316_ = lean_box(0);
                    v_isShared_5317_ = v_isSharedCheck_5392_;
                    state = 3;
                    continue;
                }
            }
            2 => {
                lean_inc(v___y_5309_);
                v___x_5311_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5(v_oldTraces_5294_, v_data_5310_, v___y_5309_, v___y_5308_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_);
                if lean_obj_tag(v___x_5311_) == 0 {
                    lean_dec_ref_known(v___x_5311_, 1);
                    v___x_5312_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6___redArg(v_fst_5302_);
                    return v___x_5312_;
                } else {
                    lean_dec(v_fst_5302_);
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
                        v___x_5387_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__5);
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
                v___x_5326_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__1);
                if v_isShared_5317_ == 0 {
                    lean_ctor_set_tag(v___x_5316_, 7);
                    lean_ctor_set(v___x_5316_, 1, v___x_5326_);
                    lean_ctor_set(v___x_5316_, 0, v___x_5325_);
                    v___x_5328_ = v___x_5316_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5339_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5339_, 0, v___x_5325_);
                    lean_ctor_set(v_reuseFailAlloc_5339_, 1, v___x_5326_);
                    v___x_5328_ = v_reuseFailAlloc_5339_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5306_ == 0 {
                    lean_ctor_set_tag(v___x_5305_, 7);
                    lean_ctor_set(v___x_5305_, 1, v_a_5322_);
                    lean_ctor_set(v___x_5305_, 0, v___x_5328_);
                    v_m_5330_ = v___x_5305_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5338_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5338_, 0, v___x_5328_);
                    lean_ctor_set(v_reuseFailAlloc_5338_, 1, v_a_5322_);
                    v_m_5330_ = v_reuseFailAlloc_5338_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5331_ = lean_box((v_result_5323_) as usize);
                v___x_5332_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5332_, 0, v___x_5331_);
                v___x_5333_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__2);
                lean_inc_ref(v_tag_5291_);
                lean_inc_ref(v___x_5332_);
                lean_inc(v_cls_5289_);
                v_data_5334_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v_data_5334_, 0, v_cls_5289_);
                lean_ctor_set(v_data_5334_, 1, v___x_5332_);
                lean_ctor_set(v_data_5334_, 2, v_tag_5291_);
                lean_ctor_set_float(
                    v_data_5334_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5333_,
                );
                lean_ctor_set_float(
                    v_data_5334_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_5333_,
                );
                lean_ctor_set_uint8(
                    v_data_5334_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v_collapsed_5290_,
                );
                if v___x_5319_ == 0 {
                    lean_dec_ref_known(v___x_5332_, 1);
                    lean_dec(v_snd_5314_);
                    lean_dec(v_fst_5313_);
                    lean_dec_ref(v_tag_5291_);
                    lean_dec(v_cls_5289_);
                    v___y_5308_ = v_m_5330_;
                    v___y_5309_ = v___y_5321_;
                    v_data_5310_ = v_data_5334_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref_known(v_data_5334_, 3);
                    v_data_5335_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v_data_5335_, 0, v_cls_5289_);
                    lean_ctor_set(v_data_5335_, 1, v___x_5332_);
                    lean_ctor_set(v_data_5335_, 2, v_tag_5291_);
                    v___x_5336_ = lean_unbox_float(v_fst_5313_);
                    lean_dec(v_fst_5313_);
                    lean_ctor_set_float(
                        v_data_5335_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_5336_,
                    );
                    v___x_5337_ = lean_unbox_float(v_snd_5314_);
                    lean_dec(v_snd_5314_);
                    lean_ctor_set_float(
                        v_data_5335_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_5337_,
                    );
                    lean_ctor_set_uint8(
                        v_data_5335_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
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
                v_ref_5341_ = lean_ctor_get(v___y_5299_, 5);
                lean_inc(v___y_5300_);
                lean_inc_ref(v___y_5299_);
                lean_inc(v___y_5298_);
                lean_inc_ref(v___y_5297_);
                lean_inc(v_fst_5302_);
                v___x_5342_ = lean_apply_6(
                    v_msg_5295_,
                    v_fst_5302_,
                    v___y_5297_,
                    v___y_5298_,
                    v___y_5299_,
                    v___y_5300_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5342_) == 0 {
                    v_a_5343_ = lean_ctor_get(v___x_5342_, 0);
                    lean_inc(v_a_5343_);
                    lean_dec_ref_known(v___x_5342_, 1);
                    v___y_5321_ = v_ref_5341_;
                    v_a_5322_ = v_a_5343_;
                    state = 4;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_5342_, 1);
                    v___x_5344_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__4);
                    v___y_5321_ = v_ref_5341_;
                    v_a_5322_ = v___x_5344_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                if v_clsEnabled_5293_ == 0 {
                    if v___y_5346_ == 0 {
                        lean_del_object(v___x_5316_);
                        lean_dec(v_snd_5314_);
                        lean_dec(v_fst_5313_);
                        lean_del_object(v___x_5305_);
                        lean_dec_ref(v_msg_5295_);
                        lean_dec_ref(v_tag_5291_);
                        lean_dec(v_cls_5289_);
                        v___x_5347_ = lean_st_ref_take(v___y_5300_);
                        v_traceState_5348_ = lean_ctor_get(v___x_5347_, 4);
                        v_env_5349_ = lean_ctor_get(v___x_5347_, 0);
                        v_nextMacroScope_5350_ = lean_ctor_get(v___x_5347_, 1);
                        v_ngen_5351_ = lean_ctor_get(v___x_5347_, 2);
                        v_auxDeclNGen_5352_ = lean_ctor_get(v___x_5347_, 3);
                        v_cache_5353_ = lean_ctor_get(v___x_5347_, 5);
                        v_messages_5354_ = lean_ctor_get(v___x_5347_, 6);
                        v_infoState_5355_ = lean_ctor_get(v___x_5347_, 7);
                        v_snapshotTasks_5356_ = lean_ctor_get(v___x_5347_, 8);
                        v_isSharedCheck_5375_ = (!lean_is_exclusive(v___x_5347_)) as u8;
                        if v_isSharedCheck_5375_ == 0 {
                            v___x_5358_ = v___x_5347_;
                            v_isShared_5359_ = v_isSharedCheck_5375_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_5356_);
                            lean_inc(v_infoState_5355_);
                            lean_inc(v_messages_5354_);
                            lean_inc(v_cache_5353_);
                            lean_inc(v_traceState_5348_);
                            lean_inc(v_auxDeclNGen_5352_);
                            lean_inc(v_ngen_5351_);
                            lean_inc(v_nextMacroScope_5350_);
                            lean_inc(v_env_5349_);
                            lean_dec(v___x_5347_);
                            v___x_5358_ = lean_box(0);
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
                v_tid_5360_ = lean_ctor_get_uint64(
                    v_traceState_5348_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_5361_ = lean_ctor_get(v_traceState_5348_, 0);
                v_isSharedCheck_5374_ = (!lean_is_exclusive(v_traceState_5348_)) as u8;
                if v_isSharedCheck_5374_ == 0 {
                    v___x_5363_ = v_traceState_5348_;
                    v_isShared_5364_ = v_isSharedCheck_5374_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_traces_5361_);
                    lean_dec(v_traceState_5348_);
                    v___x_5363_ = lean_box(0);
                    v_isShared_5364_ = v_isSharedCheck_5374_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5365_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_5294_, v_traces_5361_);
                lean_dec_ref(v_traces_5361_);
                if v_isShared_5364_ == 0 {
                    lean_ctor_set(v___x_5363_, 0, v___x_5365_);
                    v___x_5367_ = v___x_5363_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5373_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5373_, 0, v___x_5365_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_5373_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_5360_,
                    );
                    v___x_5367_ = v_reuseFailAlloc_5373_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5359_ == 0 {
                    lean_ctor_set(v___x_5358_, 4, v___x_5367_);
                    v___x_5369_ = v___x_5358_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_env_5349_);
                    lean_ctor_set(v_reuseFailAlloc_5372_, 1, v_nextMacroScope_5350_);
                    lean_ctor_set(v_reuseFailAlloc_5372_, 2, v_ngen_5351_);
                    lean_ctor_set(v_reuseFailAlloc_5372_, 3, v_auxDeclNGen_5352_);
                    lean_ctor_set(v_reuseFailAlloc_5372_, 4, v___x_5367_);
                    lean_ctor_set(v_reuseFailAlloc_5372_, 5, v_cache_5353_);
                    lean_ctor_set(v_reuseFailAlloc_5372_, 6, v_messages_5354_);
                    lean_ctor_set(v_reuseFailAlloc_5372_, 7, v_infoState_5355_);
                    lean_ctor_set(v_reuseFailAlloc_5372_, 8, v_snapshotTasks_5356_);
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
                v___x_5378_ = lean_unbox_float(v_snd_5314_);
                v___x_5379_ = lean_unbox_float(v_fst_5313_);
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
    mut v_cls_5394_: *mut LeanObject,
    mut v_collapsed_5395_: *mut LeanObject,
    mut v_tag_5396_: *mut LeanObject,
    mut v_opts_5397_: *mut LeanObject,
    mut v_clsEnabled_5398_: *mut LeanObject,
    mut v_oldTraces_5399_: *mut LeanObject,
    mut v_msg_5400_: *mut LeanObject,
    mut v_resStartStop_5401_: *mut LeanObject,
    mut v___y_5402_: *mut LeanObject,
    mut v___y_5403_: *mut LeanObject,
    mut v___y_5404_: *mut LeanObject,
    mut v___y_5405_: *mut LeanObject,
    mut v___y_5406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_5407_: u8 = 0;
    let mut v_clsEnabled_boxed_5408_: u8 = 0;
    let mut v_res_5409_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5407_ = (lean_unbox(v_collapsed_5395_) as u8);
    v_clsEnabled_boxed_5408_ = (lean_unbox(v_clsEnabled_5398_) as u8);
    v_res_5409_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3(v_cls_5394_, v_collapsed_boxed_5407_, v_tag_5396_, v_opts_5397_, v_clsEnabled_boxed_5408_, v_oldTraces_5399_, v_msg_5400_, v_resStartStop_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
    lean_dec(v___y_5405_);
    lean_dec_ref(v___y_5404_);
    lean_dec(v___y_5403_);
    lean_dec_ref(v___y_5402_);
    lean_dec_ref(v_opts_5397_);
    return v_res_5409_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    v___x_5410_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5410_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    v___x_5411_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0);
    v___x_5412_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5412_, 0, v___x_5411_);
    return v___x_5412_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    v___x_5413_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1);
    v___x_5414_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5414_, 0, v___x_5413_);
    lean_ctor_set(v___x_5414_, 1, v___x_5413_);
    return v___x_5414_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    v___x_5415_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1);
    v___x_5416_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_5416_, 0, v___x_5415_);
    lean_ctor_set(v___x_5416_, 1, v___x_5415_);
    lean_ctor_set(v___x_5416_, 2, v___x_5415_);
    lean_ctor_set(v___x_5416_, 3, v___x_5415_);
    lean_ctor_set(v___x_5416_, 4, v___x_5415_);
    lean_ctor_set(v___x_5416_, 5, v___x_5415_);
    return v___x_5416_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(
    mut v_declName_5417_: *mut LeanObject,
    mut v_s_5418_: u8,
    mut v___y_5419_: *mut LeanObject,
    mut v___y_5420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5433_: u8 = 0;
    let mut v___x_5434_: u8 = 0;
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5448_: u8 = 0;
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5456_: u8 = 0;
    let mut v_unused_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5459_: u8 = 0;
    let mut v_unused_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5422_ = lean_st_ref_take(v___y_5420_);
                v_env_5423_ = lean_ctor_get(v___x_5422_, 0);
                v_nextMacroScope_5424_ = lean_ctor_get(v___x_5422_, 1);
                v_ngen_5425_ = lean_ctor_get(v___x_5422_, 2);
                v_auxDeclNGen_5426_ = lean_ctor_get(v___x_5422_, 3);
                v_traceState_5427_ = lean_ctor_get(v___x_5422_, 4);
                v_messages_5428_ = lean_ctor_get(v___x_5422_, 6);
                v_infoState_5429_ = lean_ctor_get(v___x_5422_, 7);
                v_snapshotTasks_5430_ = lean_ctor_get(v___x_5422_, 8);
                v_isSharedCheck_5459_ = (!lean_is_exclusive(v___x_5422_)) as u8;
                if v_isSharedCheck_5459_ == 0 {
                    v_unused_5460_ = lean_ctor_get(v___x_5422_, 5);
                    lean_dec(v_unused_5460_);
                    v___x_5432_ = v___x_5422_;
                    v_isShared_5433_ = v_isSharedCheck_5459_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5430_);
                    lean_inc(v_infoState_5429_);
                    lean_inc(v_messages_5428_);
                    lean_inc(v_traceState_5427_);
                    lean_inc(v_auxDeclNGen_5426_);
                    lean_inc(v_ngen_5425_);
                    lean_inc(v_nextMacroScope_5424_);
                    lean_inc(v_env_5423_);
                    lean_dec(v___x_5422_);
                    v___x_5432_ = lean_box(0);
                    v_isShared_5433_ = v_isSharedCheck_5459_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5434_ = 0;
                v___x_5435_ = lean_box(0);
                v___x_5436_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_5423_,
                    v_declName_5417_,
                    v_s_5418_,
                    v___x_5434_,
                    v___x_5435_,
                );
                v___x_5437_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
                if v_isShared_5433_ == 0 {
                    lean_ctor_set(v___x_5432_, 5, v___x_5437_);
                    lean_ctor_set(v___x_5432_, 0, v___x_5436_);
                    v___x_5439_ = v___x_5432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5458_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5458_, 0, v___x_5436_);
                    lean_ctor_set(v_reuseFailAlloc_5458_, 1, v_nextMacroScope_5424_);
                    lean_ctor_set(v_reuseFailAlloc_5458_, 2, v_ngen_5425_);
                    lean_ctor_set(v_reuseFailAlloc_5458_, 3, v_auxDeclNGen_5426_);
                    lean_ctor_set(v_reuseFailAlloc_5458_, 4, v_traceState_5427_);
                    lean_ctor_set(v_reuseFailAlloc_5458_, 5, v___x_5437_);
                    lean_ctor_set(v_reuseFailAlloc_5458_, 6, v_messages_5428_);
                    lean_ctor_set(v_reuseFailAlloc_5458_, 7, v_infoState_5429_);
                    lean_ctor_set(v_reuseFailAlloc_5458_, 8, v_snapshotTasks_5430_);
                    v___x_5439_ = v_reuseFailAlloc_5458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5440_ = lean_st_ref_set(v___y_5420_, v___x_5439_);
                v___x_5441_ = lean_st_ref_take(v___y_5419_);
                v_mctx_5442_ = lean_ctor_get(v___x_5441_, 0);
                v_zetaDeltaFVarIds_5443_ = lean_ctor_get(v___x_5441_, 2);
                v_postponed_5444_ = lean_ctor_get(v___x_5441_, 3);
                v_diag_5445_ = lean_ctor_get(v___x_5441_, 4);
                v_isSharedCheck_5456_ = (!lean_is_exclusive(v___x_5441_)) as u8;
                if v_isSharedCheck_5456_ == 0 {
                    v_unused_5457_ = lean_ctor_get(v___x_5441_, 1);
                    lean_dec(v_unused_5457_);
                    v___x_5447_ = v___x_5441_;
                    v_isShared_5448_ = v_isSharedCheck_5456_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_5445_);
                    lean_inc(v_postponed_5444_);
                    lean_inc(v_zetaDeltaFVarIds_5443_);
                    lean_inc(v_mctx_5442_);
                    lean_dec(v___x_5441_);
                    v___x_5447_ = lean_box(0);
                    v_isShared_5448_ = v_isSharedCheck_5456_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5449_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
                if v_isShared_5448_ == 0 {
                    lean_ctor_set(v___x_5447_, 1, v___x_5449_);
                    v___x_5451_ = v___x_5447_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5455_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_mctx_5442_);
                    lean_ctor_set(v_reuseFailAlloc_5455_, 1, v___x_5449_);
                    lean_ctor_set(v_reuseFailAlloc_5455_, 2, v_zetaDeltaFVarIds_5443_);
                    lean_ctor_set(v_reuseFailAlloc_5455_, 3, v_postponed_5444_);
                    lean_ctor_set(v_reuseFailAlloc_5455_, 4, v_diag_5445_);
                    v___x_5451_ = v_reuseFailAlloc_5455_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5452_ = lean_st_ref_set(v___y_5419_, v___x_5451_);
                v___x_5453_ = lean_box(0);
                v___x_5454_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5454_, 0, v___x_5453_);
                return v___x_5454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___boxed(
    mut v_declName_5461_: *mut LeanObject,
    mut v_s_5462_: *mut LeanObject,
    mut v___y_5463_: *mut LeanObject,
    mut v___y_5464_: *mut LeanObject,
    mut v___y_5465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_5466_: u8 = 0;
    let mut v_res_5467_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_5466_ = (lean_unbox(v_s_5462_) as u8);
    v_res_5467_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_declName_5461_, v_s_boxed_5466_, v___y_5463_, v___y_5464_);
    lean_dec(v___y_5464_);
    lean_dec(v___y_5463_);
    return v_res_5467_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(
    mut v_declName_5468_: *mut LeanObject,
    mut v___y_5469_: *mut LeanObject,
    mut v___y_5470_: *mut LeanObject,
    mut v___y_5471_: *mut LeanObject,
    mut v___y_5472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5474_: u8 = 0;
    let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
    v___x_5474_ = 0;
    v___x_5475_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_declName_5468_, v___x_5474_, v___y_5470_, v___y_5472_);
    return v___x_5475_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0___boxed(
    mut v_declName_5476_: *mut LeanObject,
    mut v___y_5477_: *mut LeanObject,
    mut v___y_5478_: *mut LeanObject,
    mut v___y_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5482_: *mut LeanObject = core::ptr::null_mut();
    v_res_5482_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(
        v_declName_5476_,
        v___y_5477_,
        v___y_5478_,
        v___y_5479_,
        v___y_5480_,
    );
    lean_dec(v___y_5480_);
    lean_dec_ref(v___y_5479_);
    lean_dec(v___y_5478_);
    lean_dec_ref(v___y_5477_);
    return v_res_5482_;
}
pub unsafe fn _init_l_Lean_mkCasesOn___closed__6() -> *mut LeanObject {
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    v___x_5492_ = l_Lean_mkCasesOn___closed__2;
    v___x_5493_ = l_Lean_mkCasesOn___closed__5;
    v___x_5494_ = l_Lean_Name_append(v___x_5493_, v___x_5492_);
    return v___x_5494_;
}
pub unsafe fn _init_l_Lean_mkCasesOn___closed__7() -> f64 {
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: f64 = 0.0;
    v___x_5495_ = lean_unsigned_to_nat(1000000000);
    v___x_5496_ = lean_float_of_nat(v___x_5495_);
    return v___x_5496_;
}
pub unsafe fn l_Lean_mkCasesOn(
    mut v_declName_5497_: *mut LeanObject,
    mut v_a_5498_: *mut LeanObject,
    mut v_a_5499_: *mut LeanObject,
    mut v_a_5500_: *mut LeanObject,
    mut v_a_5501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5505_: u8 = 0;
    let mut v_name_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5522_: u8 = 0;
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5535_: u8 = 0;
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5542_: u8 = 0;
    let mut v_unused_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5545_: u8 = 0;
    let mut v_unused_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5550_: u8 = 0;
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5554_: u8 = 0;
    let mut v___f_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: u8 = 0;
    let mut v___y_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: f64 = 0.0;
    let mut v___x_5566_: f64 = 0.0;
    let mut v___x_5567_: f64 = 0.0;
    let mut v___x_5568_: f64 = 0.0;
    let mut v___x_5569_: f64 = 0.0;
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5587_: u8 = 0;
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5591_: u8 = 0;
    let mut v_a_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: f64 = 0.0;
    let mut v___x_5599_: f64 = 0.0;
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5617_: u8 = 0;
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5621_: u8 = 0;
    let mut v_a_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: u8 = 0;
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5644_: u8 = 0;
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5657_: u8 = 0;
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5664_: u8 = 0;
    let mut v_unused_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5667_: u8 = 0;
    let mut v_unused_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: u8 = 0;
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5687_: u8 = 0;
    let mut v___x_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5700_: u8 = 0;
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5707_: u8 = 0;
    let mut v_unused_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5710_: u8 = 0;
    let mut v_unused_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: u8 = 0;
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5730_: u8 = 0;
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5743_: u8 = 0;
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5750_: u8 = 0;
    let mut v_unused_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5753_: u8 = 0;
    let mut v_unused_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5758_: u8 = 0;
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5503_ = lean_ctor_get(v_a_5500_, 2);
                v_inheritedTraceOptions_5504_ = lean_ctor_get(v_a_5500_, 13);
                v_hasTrace_5505_ = lean_ctor_get_uint8(
                    v_options_5503_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_inc(v_declName_5497_);
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
                    if lean_obj_tag(v___x_5507_) == 0 {
                        v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
                        lean_inc(v_a_5508_);
                        lean_dec_ref_known(v___x_5507_, 1);
                        v___x_5509_ =
                            l_Lean_addDecl(v_a_5508_, v_hasTrace_5505_, v_a_5500_, v_a_5501_);
                        if lean_obj_tag(v___x_5509_) == 0 {
                            lean_dec_ref_known(v___x_5509_, 1);
                            lean_inc(v_name_5506_);
                            v___x_5510_ =
                                l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(
                                    v_name_5506_,
                                    v_a_5498_,
                                    v_a_5499_,
                                    v_a_5500_,
                                    v_a_5501_,
                                );
                            lean_dec_ref(v___x_5510_);
                            v___x_5511_ = lean_st_ref_take(v_a_5501_);
                            v_env_5512_ = lean_ctor_get(v___x_5511_, 0);
                            v_nextMacroScope_5513_ = lean_ctor_get(v___x_5511_, 1);
                            v_ngen_5514_ = lean_ctor_get(v___x_5511_, 2);
                            v_auxDeclNGen_5515_ = lean_ctor_get(v___x_5511_, 3);
                            v_traceState_5516_ = lean_ctor_get(v___x_5511_, 4);
                            v_messages_5517_ = lean_ctor_get(v___x_5511_, 6);
                            v_infoState_5518_ = lean_ctor_get(v___x_5511_, 7);
                            v_snapshotTasks_5519_ = lean_ctor_get(v___x_5511_, 8);
                            v_isSharedCheck_5545_ = (!lean_is_exclusive(v___x_5511_)) as u8;
                            if v_isSharedCheck_5545_ == 0 {
                                v_unused_5546_ = lean_ctor_get(v___x_5511_, 5);
                                lean_dec(v_unused_5546_);
                                v___x_5521_ = v___x_5511_;
                                v_isShared_5522_ = v_isSharedCheck_5545_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_snapshotTasks_5519_);
                                lean_inc(v_infoState_5518_);
                                lean_inc(v_messages_5517_);
                                lean_inc(v_traceState_5516_);
                                lean_inc(v_auxDeclNGen_5515_);
                                lean_inc(v_ngen_5514_);
                                lean_inc(v_nextMacroScope_5513_);
                                lean_inc(v_env_5512_);
                                lean_dec(v___x_5511_);
                                v___x_5521_ = lean_box(0);
                                v_isShared_5522_ = v_isSharedCheck_5545_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_name_5506_);
                            return v___x_5509_;
                        }
                    } else {
                        lean_dec(v_name_5506_);
                        v_a_5547_ = lean_ctor_get(v___x_5507_, 0);
                        v_isSharedCheck_5554_ = (!lean_is_exclusive(v___x_5507_)) as u8;
                        if v_isSharedCheck_5554_ == 0 {
                            v___x_5549_ = v___x_5507_;
                            v_isShared_5550_ = v_isSharedCheck_5554_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5547_);
                            lean_dec(v___x_5507_);
                            v___x_5549_ = lean_box(0);
                            v_isShared_5550_ = v_isSharedCheck_5554_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_declName_5497_);
                    v___f_5555_ = lean_alloc_closure(
                        l_Lean_mkCasesOn___lam__0___boxed as *mut core::ffi::c_void,
                        7,
                        1,
                    );
                    lean_closure_set(v___f_5555_, 0, v_declName_5497_);
                    v___x_5556_ = l_Lean_mkCasesOn___closed__2;
                    v___x_5557_ = l_Lean_mkCasesOn___closed__3;
                    v___x_5558_ = lean_obj_once(
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
                            lean_dec_ref(v___f_5555_);
                            v___x_5715_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl(v_declName_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
                            if lean_obj_tag(v___x_5715_) == 0 {
                                v_a_5716_ = lean_ctor_get(v___x_5715_, 0);
                                lean_inc(v_a_5716_);
                                lean_dec_ref_known(v___x_5715_, 1);
                                v___x_5717_ =
                                    l_Lean_addDecl(v_a_5716_, v___x_5714_, v_a_5500_, v_a_5501_);
                                if lean_obj_tag(v___x_5717_) == 0 {
                                    lean_dec_ref_known(v___x_5717_, 1);
                                    lean_inc(v_name_5506_);
                                    v___x_5718_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(v_name_5506_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
                                    lean_dec_ref(v___x_5718_);
                                    v___x_5719_ = lean_st_ref_take(v_a_5501_);
                                    v_env_5720_ = lean_ctor_get(v___x_5719_, 0);
                                    v_nextMacroScope_5721_ = lean_ctor_get(v___x_5719_, 1);
                                    v_ngen_5722_ = lean_ctor_get(v___x_5719_, 2);
                                    v_auxDeclNGen_5723_ = lean_ctor_get(v___x_5719_, 3);
                                    v_traceState_5724_ = lean_ctor_get(v___x_5719_, 4);
                                    v_messages_5725_ = lean_ctor_get(v___x_5719_, 6);
                                    v_infoState_5726_ = lean_ctor_get(v___x_5719_, 7);
                                    v_snapshotTasks_5727_ = lean_ctor_get(v___x_5719_, 8);
                                    v_isSharedCheck_5753_ = (!lean_is_exclusive(v___x_5719_)) as u8;
                                    if v_isSharedCheck_5753_ == 0 {
                                        v_unused_5754_ = lean_ctor_get(v___x_5719_, 5);
                                        lean_dec(v_unused_5754_);
                                        v___x_5729_ = v___x_5719_;
                                        v_isShared_5730_ = v_isSharedCheck_5753_;
                                        state = 26;
                                        continue;
                                    } else {
                                        lean_inc(v_snapshotTasks_5727_);
                                        lean_inc(v_infoState_5726_);
                                        lean_inc(v_messages_5725_);
                                        lean_inc(v_traceState_5724_);
                                        lean_inc(v_auxDeclNGen_5723_);
                                        lean_inc(v_ngen_5722_);
                                        lean_inc(v_nextMacroScope_5721_);
                                        lean_inc(v_env_5720_);
                                        lean_dec(v___x_5719_);
                                        v___x_5729_ = lean_box(0);
                                        v_isShared_5730_ = v_isSharedCheck_5753_;
                                        state = 26;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_name_5506_);
                                    return v___x_5717_;
                                }
                            } else {
                                lean_dec(v_name_5506_);
                                v_a_5755_ = lean_ctor_get(v___x_5715_, 0);
                                v_isSharedCheck_5762_ = (!lean_is_exclusive(v___x_5715_)) as u8;
                                if v_isSharedCheck_5762_ == 0 {
                                    v___x_5757_ = v___x_5715_;
                                    v_isShared_5758_ = v_isSharedCheck_5762_;
                                    state = 30;
                                    continue;
                                } else {
                                    lean_inc(v_a_5755_);
                                    lean_dec(v___x_5715_);
                                    v___x_5757_ = lean_box(0);
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
                lean_inc(v_name_5506_);
                v___x_5523_ = l_Lean_markAuxRecursor(v_env_5512_, v_name_5506_);
                v___x_5524_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
                if v_isShared_5522_ == 0 {
                    lean_ctor_set(v___x_5521_, 5, v___x_5524_);
                    lean_ctor_set(v___x_5521_, 0, v___x_5523_);
                    v___x_5526_ = v___x_5521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5544_, 0, v___x_5523_);
                    lean_ctor_set(v_reuseFailAlloc_5544_, 1, v_nextMacroScope_5513_);
                    lean_ctor_set(v_reuseFailAlloc_5544_, 2, v_ngen_5514_);
                    lean_ctor_set(v_reuseFailAlloc_5544_, 3, v_auxDeclNGen_5515_);
                    lean_ctor_set(v_reuseFailAlloc_5544_, 4, v_traceState_5516_);
                    lean_ctor_set(v_reuseFailAlloc_5544_, 5, v___x_5524_);
                    lean_ctor_set(v_reuseFailAlloc_5544_, 6, v_messages_5517_);
                    lean_ctor_set(v_reuseFailAlloc_5544_, 7, v_infoState_5518_);
                    lean_ctor_set(v_reuseFailAlloc_5544_, 8, v_snapshotTasks_5519_);
                    v___x_5526_ = v_reuseFailAlloc_5544_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5527_ = lean_st_ref_set(v_a_5501_, v___x_5526_);
                v___x_5528_ = lean_st_ref_take(v_a_5499_);
                v_mctx_5529_ = lean_ctor_get(v___x_5528_, 0);
                v_zetaDeltaFVarIds_5530_ = lean_ctor_get(v___x_5528_, 2);
                v_postponed_5531_ = lean_ctor_get(v___x_5528_, 3);
                v_diag_5532_ = lean_ctor_get(v___x_5528_, 4);
                v_isSharedCheck_5542_ = (!lean_is_exclusive(v___x_5528_)) as u8;
                if v_isSharedCheck_5542_ == 0 {
                    v_unused_5543_ = lean_ctor_get(v___x_5528_, 1);
                    lean_dec(v_unused_5543_);
                    v___x_5534_ = v___x_5528_;
                    v_isShared_5535_ = v_isSharedCheck_5542_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_5532_);
                    lean_inc(v_postponed_5531_);
                    lean_inc(v_zetaDeltaFVarIds_5530_);
                    lean_inc(v_mctx_5529_);
                    lean_dec(v___x_5528_);
                    v___x_5534_ = lean_box(0);
                    v_isShared_5535_ = v_isSharedCheck_5542_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5536_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
                if v_isShared_5535_ == 0 {
                    lean_ctor_set(v___x_5534_, 1, v___x_5536_);
                    v___x_5538_ = v___x_5534_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_mctx_5529_);
                    lean_ctor_set(v_reuseFailAlloc_5541_, 1, v___x_5536_);
                    lean_ctor_set(v_reuseFailAlloc_5541_, 2, v_zetaDeltaFVarIds_5530_);
                    lean_ctor_set(v_reuseFailAlloc_5541_, 3, v_postponed_5531_);
                    lean_ctor_set(v_reuseFailAlloc_5541_, 4, v_diag_5532_);
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
                    v_reuseFailAlloc_5553_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5547_);
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
                v___x_5566_ = lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_mkCasesOn___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_mkCasesOn___closed__7_once),
                    _init_l_Lean_mkCasesOn___closed__7,
                );
                v___x_5567_ = lean_float_div(v___x_5565_, v___x_5566_);
                v___x_5568_ = lean_float_of_nat(v___x_5564_);
                v___x_5569_ = lean_float_div(v___x_5568_, v___x_5566_);
                v___x_5570_ = lean_box_float(v___x_5567_);
                v___x_5571_ = lean_box_float(v___x_5569_);
                v___x_5572_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5572_, 0, v___x_5570_);
                lean_ctor_set(v___x_5572_, 1, v___x_5571_);
                v___x_5573_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5573_, 0, v_a_5563_);
                lean_ctor_set(v___x_5573_, 1, v___x_5572_);
                v___x_5574_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3(v___x_5556_, v_hasTrace_5505_, v___x_5557_, v_options_5503_, v___x_5559_, v___y_5562_, v___f_5555_, v___x_5573_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
                return v___x_5574_;
            }
            8 => {
                v___x_5579_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5579_, 0, v_a_5578_);
                v___y_5561_ = v___y_5576_;
                v___y_5562_ = v___y_5577_;
                v_a_5563_ = v___x_5579_;
                state = 7;
                continue;
            }
            9 => {
                if lean_obj_tag(v___y_5583_) == 0 {
                    v_a_5584_ = lean_ctor_get(v___y_5583_, 0);
                    v_isSharedCheck_5591_ = (!lean_is_exclusive(v___y_5583_)) as u8;
                    if v_isSharedCheck_5591_ == 0 {
                        v___x_5586_ = v___y_5583_;
                        v_isShared_5587_ = v_isSharedCheck_5591_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5584_);
                        lean_dec(v___y_5583_);
                        v___x_5586_ = lean_box(0);
                        v_isShared_5587_ = v_isSharedCheck_5591_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_a_5592_ = lean_ctor_get(v___y_5583_, 0);
                    lean_inc(v_a_5592_);
                    lean_dec_ref_known(v___y_5583_, 1);
                    v___y_5576_ = v___y_5581_;
                    v___y_5577_ = v___y_5582_;
                    v_a_5578_ = v_a_5592_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v_isShared_5587_ == 0 {
                    lean_ctor_set_tag(v___x_5586_, 1);
                    v___x_5589_ = v___x_5586_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_a_5584_);
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
                v___x_5600_ = lean_box_float(v___x_5598_);
                v___x_5601_ = lean_box_float(v___x_5599_);
                v___x_5602_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5602_, 0, v___x_5600_);
                lean_ctor_set(v___x_5602_, 1, v___x_5601_);
                v___x_5603_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5603_, 0, v_a_5596_);
                lean_ctor_set(v___x_5603_, 1, v___x_5602_);
                v___x_5604_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3(v___x_5556_, v_hasTrace_5505_, v___x_5557_, v_options_5503_, v___x_5559_, v___y_5594_, v___f_5555_, v___x_5603_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
                return v___x_5604_;
            }
            13 => {
                v___x_5609_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5609_, 0, v_a_5608_);
                v___y_5594_ = v___y_5606_;
                v___y_5595_ = v___y_5607_;
                v_a_5596_ = v___x_5609_;
                state = 12;
                continue;
            }
            14 => {
                if lean_obj_tag(v___y_5613_) == 0 {
                    v_a_5614_ = lean_ctor_get(v___y_5613_, 0);
                    v_isSharedCheck_5621_ = (!lean_is_exclusive(v___y_5613_)) as u8;
                    if v_isSharedCheck_5621_ == 0 {
                        v___x_5616_ = v___y_5613_;
                        v_isShared_5617_ = v_isSharedCheck_5621_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_5614_);
                        lean_dec(v___y_5613_);
                        v___x_5616_ = lean_box(0);
                        v_isShared_5617_ = v_isSharedCheck_5621_;
                        state = 15;
                        continue;
                    }
                } else {
                    v_a_5622_ = lean_ctor_get(v___y_5613_, 0);
                    lean_inc(v_a_5622_);
                    lean_dec_ref_known(v___y_5613_, 1);
                    v___y_5606_ = v___y_5611_;
                    v___y_5607_ = v___y_5612_;
                    v_a_5608_ = v_a_5622_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                if v_isShared_5617_ == 0 {
                    lean_ctor_set_tag(v___x_5616_, 1);
                    v___x_5619_ = v___x_5616_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5620_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_a_5614_);
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
                v_a_5625_ = lean_ctor_get(v___x_5624_, 0);
                lean_inc(v_a_5625_);
                lean_dec_ref(v___x_5624_);
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
                    if lean_obj_tag(v___x_5629_) == 0 {
                        v_a_5630_ = lean_ctor_get(v___x_5629_, 0);
                        lean_inc(v_a_5630_);
                        lean_dec_ref_known(v___x_5629_, 1);
                        v___x_5631_ = l_Lean_addDecl(v_a_5630_, v___x_5627_, v_a_5500_, v_a_5501_);
                        if lean_obj_tag(v___x_5631_) == 0 {
                            lean_dec_ref_known(v___x_5631_, 1);
                            lean_inc(v_name_5506_);
                            v___x_5632_ =
                                l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(
                                    v_name_5506_,
                                    v_a_5498_,
                                    v_a_5499_,
                                    v_a_5500_,
                                    v_a_5501_,
                                );
                            lean_dec_ref(v___x_5632_);
                            v___x_5633_ = lean_st_ref_take(v_a_5501_);
                            v_env_5634_ = lean_ctor_get(v___x_5633_, 0);
                            v_nextMacroScope_5635_ = lean_ctor_get(v___x_5633_, 1);
                            v_ngen_5636_ = lean_ctor_get(v___x_5633_, 2);
                            v_auxDeclNGen_5637_ = lean_ctor_get(v___x_5633_, 3);
                            v_traceState_5638_ = lean_ctor_get(v___x_5633_, 4);
                            v_messages_5639_ = lean_ctor_get(v___x_5633_, 6);
                            v_infoState_5640_ = lean_ctor_get(v___x_5633_, 7);
                            v_snapshotTasks_5641_ = lean_ctor_get(v___x_5633_, 8);
                            v_isSharedCheck_5667_ = (!lean_is_exclusive(v___x_5633_)) as u8;
                            if v_isSharedCheck_5667_ == 0 {
                                v_unused_5668_ = lean_ctor_get(v___x_5633_, 5);
                                lean_dec(v_unused_5668_);
                                v___x_5643_ = v___x_5633_;
                                v_isShared_5644_ = v_isSharedCheck_5667_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_snapshotTasks_5641_);
                                lean_inc(v_infoState_5640_);
                                lean_inc(v_messages_5639_);
                                lean_inc(v_traceState_5638_);
                                lean_inc(v_auxDeclNGen_5637_);
                                lean_inc(v_ngen_5636_);
                                lean_inc(v_nextMacroScope_5635_);
                                lean_inc(v_env_5634_);
                                lean_dec(v___x_5633_);
                                v___x_5643_ = lean_box(0);
                                v_isShared_5644_ = v_isSharedCheck_5667_;
                                state = 18;
                                continue;
                            }
                        } else {
                            lean_dec(v_name_5506_);
                            v___y_5581_ = v___x_5628_;
                            v___y_5582_ = v_a_5625_;
                            v___y_5583_ = v___x_5631_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec(v_name_5506_);
                        v_a_5669_ = lean_ctor_get(v___x_5629_, 0);
                        lean_inc(v_a_5669_);
                        lean_dec_ref_known(v___x_5629_, 1);
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
                    if lean_obj_tag(v___x_5671_) == 0 {
                        v_a_5672_ = lean_ctor_get(v___x_5671_, 0);
                        lean_inc(v_a_5672_);
                        lean_dec_ref_known(v___x_5671_, 1);
                        v___x_5673_ = 0;
                        v___x_5674_ = l_Lean_addDecl(v_a_5672_, v___x_5673_, v_a_5500_, v_a_5501_);
                        if lean_obj_tag(v___x_5674_) == 0 {
                            lean_dec_ref_known(v___x_5674_, 1);
                            lean_inc(v_name_5506_);
                            v___x_5675_ =
                                l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(
                                    v_name_5506_,
                                    v_a_5498_,
                                    v_a_5499_,
                                    v_a_5500_,
                                    v_a_5501_,
                                );
                            lean_dec_ref(v___x_5675_);
                            v___x_5676_ = lean_st_ref_take(v_a_5501_);
                            v_env_5677_ = lean_ctor_get(v___x_5676_, 0);
                            v_nextMacroScope_5678_ = lean_ctor_get(v___x_5676_, 1);
                            v_ngen_5679_ = lean_ctor_get(v___x_5676_, 2);
                            v_auxDeclNGen_5680_ = lean_ctor_get(v___x_5676_, 3);
                            v_traceState_5681_ = lean_ctor_get(v___x_5676_, 4);
                            v_messages_5682_ = lean_ctor_get(v___x_5676_, 6);
                            v_infoState_5683_ = lean_ctor_get(v___x_5676_, 7);
                            v_snapshotTasks_5684_ = lean_ctor_get(v___x_5676_, 8);
                            v_isSharedCheck_5710_ = (!lean_is_exclusive(v___x_5676_)) as u8;
                            if v_isSharedCheck_5710_ == 0 {
                                v_unused_5711_ = lean_ctor_get(v___x_5676_, 5);
                                lean_dec(v_unused_5711_);
                                v___x_5686_ = v___x_5676_;
                                v_isShared_5687_ = v_isSharedCheck_5710_;
                                state = 22;
                                continue;
                            } else {
                                lean_inc(v_snapshotTasks_5684_);
                                lean_inc(v_infoState_5683_);
                                lean_inc(v_messages_5682_);
                                lean_inc(v_traceState_5681_);
                                lean_inc(v_auxDeclNGen_5680_);
                                lean_inc(v_ngen_5679_);
                                lean_inc(v_nextMacroScope_5678_);
                                lean_inc(v_env_5677_);
                                lean_dec(v___x_5676_);
                                v___x_5686_ = lean_box(0);
                                v_isShared_5687_ = v_isSharedCheck_5710_;
                                state = 22;
                                continue;
                            }
                        } else {
                            lean_dec(v_name_5506_);
                            v___y_5611_ = v_a_5625_;
                            v___y_5612_ = v___x_5670_;
                            v___y_5613_ = v___x_5674_;
                            state = 14;
                            continue;
                        }
                    } else {
                        lean_dec(v_name_5506_);
                        v_a_5712_ = lean_ctor_get(v___x_5671_, 0);
                        lean_inc(v_a_5712_);
                        lean_dec_ref_known(v___x_5671_, 1);
                        v___y_5606_ = v_a_5625_;
                        v___y_5607_ = v___x_5670_;
                        v_a_5608_ = v_a_5712_;
                        state = 13;
                        continue;
                    }
                }
            }
            18 => {
                lean_inc(v_name_5506_);
                v___x_5645_ = l_Lean_markAuxRecursor(v_env_5634_, v_name_5506_);
                v___x_5646_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
                if v_isShared_5644_ == 0 {
                    lean_ctor_set(v___x_5643_, 5, v___x_5646_);
                    lean_ctor_set(v___x_5643_, 0, v___x_5645_);
                    v___x_5648_ = v___x_5643_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5666_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5666_, 0, v___x_5645_);
                    lean_ctor_set(v_reuseFailAlloc_5666_, 1, v_nextMacroScope_5635_);
                    lean_ctor_set(v_reuseFailAlloc_5666_, 2, v_ngen_5636_);
                    lean_ctor_set(v_reuseFailAlloc_5666_, 3, v_auxDeclNGen_5637_);
                    lean_ctor_set(v_reuseFailAlloc_5666_, 4, v_traceState_5638_);
                    lean_ctor_set(v_reuseFailAlloc_5666_, 5, v___x_5646_);
                    lean_ctor_set(v_reuseFailAlloc_5666_, 6, v_messages_5639_);
                    lean_ctor_set(v_reuseFailAlloc_5666_, 7, v_infoState_5640_);
                    lean_ctor_set(v_reuseFailAlloc_5666_, 8, v_snapshotTasks_5641_);
                    v___x_5648_ = v_reuseFailAlloc_5666_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_5649_ = lean_st_ref_set(v_a_5501_, v___x_5648_);
                v___x_5650_ = lean_st_ref_take(v_a_5499_);
                v_mctx_5651_ = lean_ctor_get(v___x_5650_, 0);
                v_zetaDeltaFVarIds_5652_ = lean_ctor_get(v___x_5650_, 2);
                v_postponed_5653_ = lean_ctor_get(v___x_5650_, 3);
                v_diag_5654_ = lean_ctor_get(v___x_5650_, 4);
                v_isSharedCheck_5664_ = (!lean_is_exclusive(v___x_5650_)) as u8;
                if v_isSharedCheck_5664_ == 0 {
                    v_unused_5665_ = lean_ctor_get(v___x_5650_, 1);
                    lean_dec(v_unused_5665_);
                    v___x_5656_ = v___x_5650_;
                    v_isShared_5657_ = v_isSharedCheck_5664_;
                    state = 20;
                    continue;
                } else {
                    lean_inc(v_diag_5654_);
                    lean_inc(v_postponed_5653_);
                    lean_inc(v_zetaDeltaFVarIds_5652_);
                    lean_inc(v_mctx_5651_);
                    lean_dec(v___x_5650_);
                    v___x_5656_ = lean_box(0);
                    v_isShared_5657_ = v_isSharedCheck_5664_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_5658_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
                if v_isShared_5657_ == 0 {
                    lean_ctor_set(v___x_5656_, 1, v___x_5658_);
                    v___x_5660_ = v___x_5656_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5663_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_mctx_5651_);
                    lean_ctor_set(v_reuseFailAlloc_5663_, 1, v___x_5658_);
                    lean_ctor_set(v_reuseFailAlloc_5663_, 2, v_zetaDeltaFVarIds_5652_);
                    lean_ctor_set(v_reuseFailAlloc_5663_, 3, v_postponed_5653_);
                    lean_ctor_set(v_reuseFailAlloc_5663_, 4, v_diag_5654_);
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
                lean_inc(v_name_5506_);
                v___x_5688_ = l_Lean_markAuxRecursor(v_env_5677_, v_name_5506_);
                v___x_5689_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
                if v_isShared_5687_ == 0 {
                    lean_ctor_set(v___x_5686_, 5, v___x_5689_);
                    lean_ctor_set(v___x_5686_, 0, v___x_5688_);
                    v___x_5691_ = v___x_5686_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5709_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5709_, 0, v___x_5688_);
                    lean_ctor_set(v_reuseFailAlloc_5709_, 1, v_nextMacroScope_5678_);
                    lean_ctor_set(v_reuseFailAlloc_5709_, 2, v_ngen_5679_);
                    lean_ctor_set(v_reuseFailAlloc_5709_, 3, v_auxDeclNGen_5680_);
                    lean_ctor_set(v_reuseFailAlloc_5709_, 4, v_traceState_5681_);
                    lean_ctor_set(v_reuseFailAlloc_5709_, 5, v___x_5689_);
                    lean_ctor_set(v_reuseFailAlloc_5709_, 6, v_messages_5682_);
                    lean_ctor_set(v_reuseFailAlloc_5709_, 7, v_infoState_5683_);
                    lean_ctor_set(v_reuseFailAlloc_5709_, 8, v_snapshotTasks_5684_);
                    v___x_5691_ = v_reuseFailAlloc_5709_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_5692_ = lean_st_ref_set(v_a_5501_, v___x_5691_);
                v___x_5693_ = lean_st_ref_take(v_a_5499_);
                v_mctx_5694_ = lean_ctor_get(v___x_5693_, 0);
                v_zetaDeltaFVarIds_5695_ = lean_ctor_get(v___x_5693_, 2);
                v_postponed_5696_ = lean_ctor_get(v___x_5693_, 3);
                v_diag_5697_ = lean_ctor_get(v___x_5693_, 4);
                v_isSharedCheck_5707_ = (!lean_is_exclusive(v___x_5693_)) as u8;
                if v_isSharedCheck_5707_ == 0 {
                    v_unused_5708_ = lean_ctor_get(v___x_5693_, 1);
                    lean_dec(v_unused_5708_);
                    v___x_5699_ = v___x_5693_;
                    v_isShared_5700_ = v_isSharedCheck_5707_;
                    state = 24;
                    continue;
                } else {
                    lean_inc(v_diag_5697_);
                    lean_inc(v_postponed_5696_);
                    lean_inc(v_zetaDeltaFVarIds_5695_);
                    lean_inc(v_mctx_5694_);
                    lean_dec(v___x_5693_);
                    v___x_5699_ = lean_box(0);
                    v_isShared_5700_ = v_isSharedCheck_5707_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_5701_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
                if v_isShared_5700_ == 0 {
                    lean_ctor_set(v___x_5699_, 1, v___x_5701_);
                    v___x_5703_ = v___x_5699_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5706_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5706_, 0, v_mctx_5694_);
                    lean_ctor_set(v_reuseFailAlloc_5706_, 1, v___x_5701_);
                    lean_ctor_set(v_reuseFailAlloc_5706_, 2, v_zetaDeltaFVarIds_5695_);
                    lean_ctor_set(v_reuseFailAlloc_5706_, 3, v_postponed_5696_);
                    lean_ctor_set(v_reuseFailAlloc_5706_, 4, v_diag_5697_);
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
                lean_inc(v_name_5506_);
                v___x_5731_ = l_Lean_markAuxRecursor(v_env_5720_, v_name_5506_);
                v___x_5732_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
                if v_isShared_5730_ == 0 {
                    lean_ctor_set(v___x_5729_, 5, v___x_5732_);
                    lean_ctor_set(v___x_5729_, 0, v___x_5731_);
                    v___x_5734_ = v___x_5729_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 0, v___x_5731_);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 1, v_nextMacroScope_5721_);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 2, v_ngen_5722_);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 3, v_auxDeclNGen_5723_);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 4, v_traceState_5724_);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 5, v___x_5732_);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 6, v_messages_5725_);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 7, v_infoState_5726_);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 8, v_snapshotTasks_5727_);
                    v___x_5734_ = v_reuseFailAlloc_5752_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_5735_ = lean_st_ref_set(v_a_5501_, v___x_5734_);
                v___x_5736_ = lean_st_ref_take(v_a_5499_);
                v_mctx_5737_ = lean_ctor_get(v___x_5736_, 0);
                v_zetaDeltaFVarIds_5738_ = lean_ctor_get(v___x_5736_, 2);
                v_postponed_5739_ = lean_ctor_get(v___x_5736_, 3);
                v_diag_5740_ = lean_ctor_get(v___x_5736_, 4);
                v_isSharedCheck_5750_ = (!lean_is_exclusive(v___x_5736_)) as u8;
                if v_isSharedCheck_5750_ == 0 {
                    v_unused_5751_ = lean_ctor_get(v___x_5736_, 1);
                    lean_dec(v_unused_5751_);
                    v___x_5742_ = v___x_5736_;
                    v_isShared_5743_ = v_isSharedCheck_5750_;
                    state = 28;
                    continue;
                } else {
                    lean_inc(v_diag_5740_);
                    lean_inc(v_postponed_5739_);
                    lean_inc(v_zetaDeltaFVarIds_5738_);
                    lean_inc(v_mctx_5737_);
                    lean_dec(v___x_5736_);
                    v___x_5742_ = lean_box(0);
                    v_isShared_5743_ = v_isSharedCheck_5750_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_5744_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
                if v_isShared_5743_ == 0 {
                    lean_ctor_set(v___x_5742_, 1, v___x_5744_);
                    v___x_5746_ = v___x_5742_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5749_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_mctx_5737_);
                    lean_ctor_set(v_reuseFailAlloc_5749_, 1, v___x_5744_);
                    lean_ctor_set(v_reuseFailAlloc_5749_, 2, v_zetaDeltaFVarIds_5738_);
                    lean_ctor_set(v_reuseFailAlloc_5749_, 3, v_postponed_5739_);
                    lean_ctor_set(v_reuseFailAlloc_5749_, 4, v_diag_5740_);
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
                    v_reuseFailAlloc_5761_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5761_, 0, v_a_5755_);
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
    mut v_declName_5763_: *mut LeanObject,
    mut v_a_5764_: *mut LeanObject,
    mut v_a_5765_: *mut LeanObject,
    mut v_a_5766_: *mut LeanObject,
    mut v_a_5767_: *mut LeanObject,
    mut v_a_5768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5769_: *mut LeanObject = core::ptr::null_mut();
    v_res_5769_ = l_Lean_mkCasesOn(v_declName_5763_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_);
    lean_dec(v_a_5767_);
    lean_dec_ref(v_a_5766_);
    lean_dec(v_a_5765_);
    lean_dec_ref(v_a_5764_);
    return v_res_5769_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0(
    mut v_declName_5770_: *mut LeanObject,
    mut v_s_5771_: u8,
    mut v___y_5772_: *mut LeanObject,
    mut v___y_5773_: *mut LeanObject,
    mut v___y_5774_: *mut LeanObject,
    mut v___y_5775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    v___x_5777_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_declName_5770_, v_s_5771_, v___y_5773_, v___y_5775_);
    return v___x_5777_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___boxed(
    mut v_declName_5778_: *mut LeanObject,
    mut v_s_5779_: *mut LeanObject,
    mut v___y_5780_: *mut LeanObject,
    mut v___y_5781_: *mut LeanObject,
    mut v___y_5782_: *mut LeanObject,
    mut v___y_5783_: *mut LeanObject,
    mut v___y_5784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_5785_: u8 = 0;
    let mut v_res_5786_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_5785_ = (lean_unbox(v_s_5779_) as u8);
    v_res_5786_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0(v_declName_5778_, v_s_boxed_5785_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
    lean_dec(v___y_5783_);
    lean_dec_ref(v___y_5782_);
    lean_dec(v___y_5781_);
    lean_dec_ref(v___y_5780_);
    return v_res_5786_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6(
    mut v_00_u03b1_5787_: *mut LeanObject,
    mut v_x_5788_: *mut LeanObject,
    mut v___y_5789_: *mut LeanObject,
    mut v___y_5790_: *mut LeanObject,
    mut v___y_5791_: *mut LeanObject,
    mut v___y_5792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    v___x_5794_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6___redArg(v_x_5788_);
    return v___x_5794_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6___boxed(
    mut v_00_u03b1_5795_: *mut LeanObject,
    mut v_x_5796_: *mut LeanObject,
    mut v___y_5797_: *mut LeanObject,
    mut v___y_5798_: *mut LeanObject,
    mut v___y_5799_: *mut LeanObject,
    mut v___y_5800_: *mut LeanObject,
    mut v___y_5801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5802_: *mut LeanObject = core::ptr::null_mut();
    v_res_5802_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6(v_00_u03b1_5795_, v_x_5796_, v___y_5797_, v___y_5798_, v___y_5799_, v___y_5800_);
    lean_dec(v___y_5800_);
    lean_dec_ref(v___y_5799_);
    lean_dec(v___y_5798_);
    lean_dec_ref(v___y_5797_);
    return v_res_5802_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: u8 = 0;
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    v___x_5863_ = l_Lean_mkCasesOn___closed__2;
    v___x_5864_ = 0;
    v___x_5865_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_;
    v___x_5866_ = l_Lean_registerTraceClass(v___x_5863_, v___x_5864_, v___x_5865_);
    return v___x_5866_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2____boxed(
    mut v_a_5867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5868_: *mut LeanObject = core::ptr::null_mut();
    v_res_5868_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
    return v_res_5868_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Constructions_CasesOn(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Constructions_CasesOn(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Constructions_CasesOn(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CasesOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Constructions_CasesOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Constructions_CasesOn(builtin);
}
