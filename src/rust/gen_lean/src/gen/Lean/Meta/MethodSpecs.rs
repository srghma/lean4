// Lean compiler output
// Module: Lean.Meta.MethodSpecs
// Imports: Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Tactic.Simp.Main Lean.Structure
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_array_mk,
    lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_level_eq, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_string_dec_eq,
    lean_string_memcmp, lean_string_utf8_byte_size, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_isNat;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::Attributes::{
    l_Lean_ParametricAttribute_getParam_x3f___redArg, l_Lean_registerParametricAttribute___redArg,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_hasValue;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_contains,
    l_Lean_Environment_containsOnBranch, l_Lean_Environment_find_x3f,
    l_Lean_Environment_findAsync_x3f, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux,
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop, l_Lean_Expr_constLevels_x21,
    l_Lean_Expr_constName_x21, l_Lean_Expr_eta, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_isConst, l_Lean_Expr_sort___override, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_ofNat, l_Lean_mkLevelParam};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofLevel, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofName, l_Lean_MessageData_paren, l_Lean_indentExpr, l_Lean_inlineExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkEq;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_instantiateForall, l_Lean_Meta_isClass_x3f, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_realizeConst,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::l_Lean_Meta_isConstructorApp;
use crate::r#gen::Lean::Meta::Eqns::{l_Lean_Meta_getEqnsFor_x3f, l_Lean_Meta_getUnfoldEqnFor_x3f};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProof;
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::l_Lean_Meta_registerSimpAttr;
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{
    initialize_Lean_Meta_Tactic_Simp_Main, l_Lean_Meta_simp,
    runtime_initialize_Lean_Meta_Tactic_Simp_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    initialize_Lean_Meta_Tactic_Simp_SimpTheorems, l_Lean_Meta_SimpExtension_getTheorems___redArg,
    l_Lean_Meta_SimpTheorems_addSimpTheorem, l_Lean_Meta_mkDSimpTheorem,
    l_Lean_Meta_simpGlobalConfig, runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::l_Lean_Meta_Simp_getSimprocs___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    l_Lean_Meta_Simp_Result_getProof, l_Lean_Meta_Simp_mkContext___redArg,
};
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::{l_Lean_isPrivateName, l_Lean_privateToUserName};
use crate::r#gen::Lean::ReservedNameAction::{
    l_Lean_realizeGlobalConstNoOverloadCore, l_Lean_registerReservedNameAction,
};
use crate::r#gen::Lean::ResolveName::l_Lean_registerReservedNamePredicate;
use crate::r#gen::Lean::Structure::{
    initialize_Lean_Structure, l_Lean_getFieldInfo_x3f, l_Lean_getStructureFields,
    l_Lean_getStructureInfo_x3f, runtime_initialize_Lean_Structure,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 101, 113, 117, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3_value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 111, 108, 100, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 102, 105, 101, 108, 100, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [32, 105, 110, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [102, 117, 110, 99, 116, 105, 111, 110, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11_value: crate::leanh::LeanStringObject<64> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 64, m_capacity: 64, m_length: 63, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 116, 97, 107, 101, 32, 105, 116, 115, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 105, 110, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 111, 114, 100, 101, 114, 32, 97, 115, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [96, 32, 105, 115, 32, 99, 97, 108, 108, 101, 100, 32, 119, 105, 116, 104, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 10, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15_value: crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [10, 119, 104, 105, 99, 104, 32, 100, 105, 102, 102, 101, 114, 115, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 39, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 10, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [102, 105, 101, 108, 100, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 32, 111, 102, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 111, 102, 32, 97, 32, 99, 111, 110, 115, 116, 97, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [77, 101, 116, 104, 111, 100, 83, 112, 101, 99, 115, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,142734480563613395 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,16869473420000565890 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [77, 101, 116, 104, 111, 100, 83, 112, 101, 99, 115, 32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 10, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [10, 116, 104, 109, 115, 58, 32, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [10, 112, 114, 105, 118, 97, 116, 101, 83, 112, 101, 99, 115, 58, 32, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [116, 104, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 111, 102, 32, 96, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__19_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 104, 97, 112, 101, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__19_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__5_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 68, 101, 102, 110, 63, 0]};
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__1_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 115, 116, 114, 117, 99, 116, 117, 114,
        101, 0,
    ],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__3_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 0],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__5_value:
    crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        96, 32, 116, 111, 32, 98, 101, 32, 97, 32, 116, 121, 112, 101, 32, 99, 108, 97, 115, 115,
        32, 105, 110, 115, 116, 97, 110, 99, 101, 44, 32, 98, 117, 116, 32, 105, 116, 115, 32, 116,
        121, 112, 101, 0,
    ],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__7_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        100, 111, 101, 115, 32, 110, 111, 116, 32, 108, 111, 111, 107, 32, 108, 105, 107, 101, 32,
        97, 32, 99, 108, 97, 115, 115, 46, 0,
    ],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedMethodSpecsAttrData_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedMethodSpecsAttrData: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 24) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [
        282574488338432 as *mut crate::leanh::LeanObject,
        72621647814721793 as *mut crate::leanh::LeanObject,
        65793 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1: u64 = 0;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,16627468330847833091 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,5821782099191670350 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14012549361381910007 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [109, 101, 116, 104, 111, 100, 83, 112, 101, 99, 115, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3332304603237231731 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [109, 101, 116, 104, 111, 100, 95, 115, 112, 101, 99, 115, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14706946839582711653 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__13_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [103, 101, 110, 101, 114, 97, 116, 101, 32, 109, 101, 116, 104, 111, 100, 32, 115, 112, 101, 99, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 115, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__13_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__13_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__14_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__13_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__14_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__14_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__15_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__15_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__15_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__16_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__16_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__16_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__17_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 8) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__14_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__15_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__16_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__17_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__17_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__0_value: crate::leanh::LeanStringObject<566> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 566, m_capacity: 566, m_length: 565, m_data: [71, 101, 110, 101, 114, 97, 116, 101, 32, 109, 101, 116, 104, 111, 100, 32, 115, 112, 101, 99, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 102, 111, 114, 32, 116, 104, 101, 32, 109, 101, 116, 104, 111, 100, 115, 32, 111, 102, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 116, 121, 112, 101, 32, 99, 108, 97, 115, 115, 32, 105, 110, 115, 116, 97, 110, 99, 101, 46, 10, 10, 84, 104, 105, 115, 32, 101, 120, 112, 101, 99, 116, 115, 32, 97, 108, 108, 32, 40, 110, 111, 110, 45, 112, 114, 111, 111, 102, 41, 32, 109, 101, 116, 104, 111, 100, 115, 32, 111, 102, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 116, 111, 32, 98, 101, 32, 100, 101, 102, 105, 110, 101, 100, 32, 118, 105, 97, 32, 115, 101, 112, 97, 114, 97, 116, 101, 32, 104, 101, 108, 112, 101, 114, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 44, 10, 119, 104, 105, 99, 104, 32, 109, 117, 115, 116, 32, 116, 97, 107, 101, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 97, 115, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 105, 116, 115, 101, 108, 102, 44, 32, 105, 110, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 111, 114, 100, 101, 114, 46, 10, 10, 73, 102, 32, 105, 116, 32, 105, 115, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116, 111, 32, 97, 110, 32, 105, 110, 115, 116, 97, 110, 99, 101, 10, 96, 96, 96, 10, 105, 110, 115, 116, 97, 110, 99, 101, 32, 105, 110, 115, 116, 67, 108, 115, 84, 32, 58, 32, 67, 108, 115, 32, 84, 32, 119, 104, 101, 114, 101, 32, 111, 112, 32, 58, 61, 32, 111, 112, 73, 109, 112, 108, 10, 96, 96, 96, 10, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 116, 104, 101, 111, 114, 101, 109, 32, 96, 105, 110, 115, 116, 67, 108, 115, 84, 46, 111, 112, 95, 115, 112, 101, 99, 96, 32, 98, 97, 115, 101, 100, 32, 111, 110, 32, 96, 111, 112, 73, 109, 112, 108, 46, 101, 113, 95, 100, 101, 102, 96, 44, 32, 98, 117, 116, 32, 112, 104, 114, 97, 115, 101, 100, 32, 105, 110, 32, 116, 101, 114, 109, 115, 32, 111, 102, 32, 116, 104, 101, 10, 111, 118, 101, 114, 108, 111, 97, 100, 101, 100, 32, 96, 67, 108, 115, 46, 111, 112, 96, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 44, 32, 97, 110, 100, 32, 115, 105, 109, 105, 108, 97, 114, 108, 121, 32, 96, 105, 110, 115, 116, 67, 108, 115, 84, 46, 111, 112, 95, 115, 112, 101, 99, 95, 60, 110, 62, 96, 32, 98, 97, 115, 101, 100, 32, 111, 110, 32, 116, 104, 101, 32, 101, 113, 117, 97, 116, 105, 111, 110, 97, 108, 32, 116, 104, 101, 111, 114, 101, 109, 115, 10, 96, 111, 112, 73, 109, 112, 108, 46, 101, 113, 95, 60, 110, 62, 96, 46, 10, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 99 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 119 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 114 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 114 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [109, 101, 116, 104, 111, 100, 95, 115, 112, 101, 99, 115, 95, 115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12978546787041305861 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<74> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [115, 105, 109, 112, 32, 108, 101, 109, 109, 97, 32, 117, 115, 101, 100, 32, 116, 111, 32, 112, 111, 115, 116, 45, 112, 114, 111, 99, 101, 115, 115, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 32, 99, 114, 101, 97, 116, 101, 100, 32, 98, 121, 32, 96, 64, 91, 109, 101, 116, 104, 111, 100, 95, 115, 112, 101, 99, 115, 93, 96, 46, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [109, 101, 116, 104, 111, 100, 83, 112, 101, 99, 115, 83, 105, 109, 112, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3786670690208729641 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsSimpExtension:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [95, 115, 112, 101, 99, 0],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1_value:
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
    m_data: [95, 115, 112, 101, 99, 95, 0],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__7_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [69, 113, 0],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__8_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [109, 112, 0],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__7_value)
            as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__8_value)
            as *mut crate::leanh::LeanObject,
        5647098122476602039 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13_value:
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
    m_data: [116, 121, 112, 101, 32, 102, 111, 114, 32, 0],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [58, 0],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0_value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 117, 110, 102, 111, 108, 100, 105, 110, 103, 32, 116, 104, 101, 111, 114, 101, 109, 32, 102, 111, 114, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [97, 100, 100, 105, 110, 103, 32, 115, 105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 32, 102, 111, 114, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0_value: crate::leanh::LeanCtorObject<7> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 32) as u16, other: 3, tag: 0 }, m_objs: [((( 100000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,72058697861300480 as *mut crate::leanh::LeanObject,1103806595073 as *mut crate::leanh::LeanObject,72340172838076672 as *mut crate::leanh::LeanObject,257 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getMethodSpecTheorems___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_getMethodSpecTheorems___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getMethodSpecTheorems___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getMethodSpecTheorems___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_getMethodSpecTheorems___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_getMethodSpecTheorems___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getMethodSpecTheorems___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3909582110267790918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10411835254743274231 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1063899344436178826 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,11253650946146721326 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,17241205374711927315 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0(
    mut v_k_3026_: *mut crate::leanh::LeanObject,
    mut v_b_3027_: *mut crate::leanh::LeanObject,
    mut v_c_3028_: *mut crate::leanh::LeanObject,
    mut v___y_3029_: *mut crate::leanh::LeanObject,
    mut v___y_3030_: *mut crate::leanh::LeanObject,
    mut v___y_3031_: *mut crate::leanh::LeanObject,
    mut v___y_3032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3032_);
    crate::leanh::lean_inc_ref(v___y_3031_);
    crate::leanh::lean_inc(v___y_3030_);
    crate::leanh::lean_inc_ref(v___y_3029_);
    v___x_3034_ = crate::leanh::lean_apply_7(
        v_k_3026_,
        v_b_3027_,
        v_c_3028_,
        v___y_3029_,
        v___y_3030_,
        v___y_3031_,
        v___y_3032_,
        crate::leanh::lean_box(0),
    );
    return v___x_3034_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0___boxed(
    mut v_k_3035_: *mut crate::leanh::LeanObject,
    mut v_b_3036_: *mut crate::leanh::LeanObject,
    mut v_c_3037_: *mut crate::leanh::LeanObject,
    mut v___y_3038_: *mut crate::leanh::LeanObject,
    mut v___y_3039_: *mut crate::leanh::LeanObject,
    mut v___y_3040_: *mut crate::leanh::LeanObject,
    mut v___y_3041_: *mut crate::leanh::LeanObject,
    mut v___y_3042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3043_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0(v_k_3035_, v_b_3036_, v_c_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
    crate::leanh::lean_dec(v___y_3041_);
    crate::leanh::lean_dec_ref(v___y_3040_);
    crate::leanh::lean_dec(v___y_3039_);
    crate::leanh::lean_dec_ref(v___y_3038_);
    return v_res_3043_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(
    mut v_type_3044_: *mut crate::leanh::LeanObject,
    mut v_k_3045_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3046_: u8,
    mut v_whnfType_3047_: u8,
    mut v___y_3048_: *mut crate::leanh::LeanObject,
    mut v___y_3049_: *mut crate::leanh::LeanObject,
    mut v___y_3050_: *mut crate::leanh::LeanObject,
    mut v___y_3051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3058_: u8 = 0;
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3062_: u8 = 0;
    let mut v_a_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3070_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3053_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_3053_, 0, v_k_3045_);
                v___x_3054_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_3044_,
                    v___f_3053_,
                    v_cleanupAnnotations_3046_,
                    v_whnfType_3047_,
                    v___y_3048_,
                    v___y_3049_,
                    v___y_3050_,
                    v___y_3051_,
                );
                if crate::leanh::lean_obj_tag(v___x_3054_) == 0 {
                    v_a_3055_ = crate::leanh::lean_ctor_get(v___x_3054_, 0);
                    v_isSharedCheck_3062_ = (!crate::leanh::lean_is_exclusive(v___x_3054_)) as u8;
                    if v_isSharedCheck_3062_ == 0 {
                        v___x_3057_ = v___x_3054_;
                        v_isShared_3058_ = v_isSharedCheck_3062_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3055_);
                        crate::leanh::lean_dec(v___x_3054_);
                        v___x_3057_ = crate::leanh::lean_box(0);
                        v_isShared_3058_ = v_isSharedCheck_3062_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3063_ = crate::leanh::lean_ctor_get(v___x_3054_, 0);
                    v_isSharedCheck_3070_ = (!crate::leanh::lean_is_exclusive(v___x_3054_)) as u8;
                    if v_isSharedCheck_3070_ == 0 {
                        v___x_3065_ = v___x_3054_;
                        v_isShared_3066_ = v_isSharedCheck_3070_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3063_);
                        crate::leanh::lean_dec(v___x_3054_);
                        v___x_3065_ = crate::leanh::lean_box(0);
                        v_isShared_3066_ = v_isSharedCheck_3070_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3058_ == 0 {
                    v___x_3060_ = v___x_3057_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3061_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
                    v___x_3060_ = v_reuseFailAlloc_3061_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3060_;
            }
            3 => {
                if v_isShared_3066_ == 0 {
                    v___x_3068_ = v___x_3065_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
                    v___x_3068_ = v_reuseFailAlloc_3069_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___boxed(
    mut v_type_3071_: *mut crate::leanh::LeanObject,
    mut v_k_3072_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3073_: *mut crate::leanh::LeanObject,
    mut v_whnfType_3074_: *mut crate::leanh::LeanObject,
    mut v___y_3075_: *mut crate::leanh::LeanObject,
    mut v___y_3076_: *mut crate::leanh::LeanObject,
    mut v___y_3077_: *mut crate::leanh::LeanObject,
    mut v___y_3078_: *mut crate::leanh::LeanObject,
    mut v___y_3079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3080_: u8 = 0;
    let mut v_whnfType_boxed_3081_: u8 = 0;
    let mut v_res_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3080_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_3073_) as u8);
    v_whnfType_boxed_3081_ = (crate::leanh::lean_unbox(v_whnfType_3074_) as u8);
    v_res_3082_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(v_type_3071_, v_k_3072_, v_cleanupAnnotations_boxed_3080_, v_whnfType_boxed_3081_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
    crate::leanh::lean_dec(v___y_3078_);
    crate::leanh::lean_dec_ref(v___y_3077_);
    crate::leanh::lean_dec(v___y_3076_);
    crate::leanh::lean_dec_ref(v___y_3075_);
    return v_res_3082_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1(
    mut v_00_u03b1_3083_: *mut crate::leanh::LeanObject,
    mut v_type_3084_: *mut crate::leanh::LeanObject,
    mut v_k_3085_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3086_: u8,
    mut v_whnfType_3087_: u8,
    mut v___y_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
    mut v___y_3090_: *mut crate::leanh::LeanObject,
    mut v___y_3091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3093_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(v_type_3084_, v_k_3085_, v_cleanupAnnotations_3086_, v_whnfType_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___boxed(
    mut v_00_u03b1_3094_: *mut crate::leanh::LeanObject,
    mut v_type_3095_: *mut crate::leanh::LeanObject,
    mut v_k_3096_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3097_: *mut crate::leanh::LeanObject,
    mut v_whnfType_3098_: *mut crate::leanh::LeanObject,
    mut v___y_3099_: *mut crate::leanh::LeanObject,
    mut v___y_3100_: *mut crate::leanh::LeanObject,
    mut v___y_3101_: *mut crate::leanh::LeanObject,
    mut v___y_3102_: *mut crate::leanh::LeanObject,
    mut v___y_3103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3104_: u8 = 0;
    let mut v_whnfType_boxed_3105_: u8 = 0;
    let mut v_res_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3104_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_3097_) as u8);
    v_whnfType_boxed_3105_ = (crate::leanh::lean_unbox(v_whnfType_3098_) as u8);
    v_res_3106_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1(v_00_u03b1_3094_, v_type_3095_, v_k_3096_, v_cleanupAnnotations_boxed_3104_, v_whnfType_boxed_3105_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
    crate::leanh::lean_dec(v___y_3102_);
    crate::leanh::lean_dec_ref(v___y_3101_);
    crate::leanh::lean_dec(v___y_3100_);
    crate::leanh::lean_dec_ref(v___y_3099_);
    return v_res_3106_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(
    mut v_e_3107_: *mut crate::leanh::LeanObject,
    mut v_k_3108_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3109_: u8,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
    mut v___y_3111_: *mut crate::leanh::LeanObject,
    mut v___y_3112_: *mut crate::leanh::LeanObject,
    mut v___y_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: u8 = 0;
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3127_: u8 = 0;
    let mut v_a_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3115_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_3115_, 0, v_k_3108_);
                v___x_3116_ = 1;
                v___x_3117_ = 0;
                v___x_3118_ = crate::leanh::lean_box(0);
                v___x_3119_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    crate::leanh::lean_box(0),
                    v_e_3107_,
                    v___x_3116_,
                    v___x_3117_,
                    v___x_3116_,
                    v___x_3117_,
                    v___x_3118_,
                    v___f_3115_,
                    v_cleanupAnnotations_3109_,
                    v___y_3110_,
                    v___y_3111_,
                    v___y_3112_,
                    v___y_3113_,
                );
                if crate::leanh::lean_obj_tag(v___x_3119_) == 0 {
                    v_a_3120_ = crate::leanh::lean_ctor_get(v___x_3119_, 0);
                    v_isSharedCheck_3127_ = (!crate::leanh::lean_is_exclusive(v___x_3119_)) as u8;
                    if v_isSharedCheck_3127_ == 0 {
                        v___x_3122_ = v___x_3119_;
                        v_isShared_3123_ = v_isSharedCheck_3127_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3120_);
                        crate::leanh::lean_dec(v___x_3119_);
                        v___x_3122_ = crate::leanh::lean_box(0);
                        v_isShared_3123_ = v_isSharedCheck_3127_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3128_ = crate::leanh::lean_ctor_get(v___x_3119_, 0);
                    v_isSharedCheck_3135_ = (!crate::leanh::lean_is_exclusive(v___x_3119_)) as u8;
                    if v_isSharedCheck_3135_ == 0 {
                        v___x_3130_ = v___x_3119_;
                        v_isShared_3131_ = v_isSharedCheck_3135_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3128_);
                        crate::leanh::lean_dec(v___x_3119_);
                        v___x_3130_ = crate::leanh::lean_box(0);
                        v_isShared_3131_ = v_isSharedCheck_3135_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3123_ == 0 {
                    v___x_3125_ = v___x_3122_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3126_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
                    v___x_3125_ = v_reuseFailAlloc_3126_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3125_;
            }
            3 => {
                if v_isShared_3131_ == 0 {
                    v___x_3133_ = v___x_3130_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
                    v___x_3133_ = v_reuseFailAlloc_3134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg___boxed(
    mut v_e_3136_: *mut crate::leanh::LeanObject,
    mut v_k_3137_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3138_: *mut crate::leanh::LeanObject,
    mut v___y_3139_: *mut crate::leanh::LeanObject,
    mut v___y_3140_: *mut crate::leanh::LeanObject,
    mut v___y_3141_: *mut crate::leanh::LeanObject,
    mut v___y_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3144_: u8 = 0;
    let mut v_res_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3144_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_3138_) as u8);
    v_res_3145_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(v_e_3136_, v_k_3137_, v_cleanupAnnotations_boxed_3144_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
    crate::leanh::lean_dec(v___y_3142_);
    crate::leanh::lean_dec_ref(v___y_3141_);
    crate::leanh::lean_dec(v___y_3140_);
    crate::leanh::lean_dec_ref(v___y_3139_);
    return v_res_3145_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(
    mut v_00_u03b1_3146_: *mut crate::leanh::LeanObject,
    mut v_e_3147_: *mut crate::leanh::LeanObject,
    mut v_k_3148_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3149_: u8,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
    mut v___y_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3155_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(v_e_3147_, v_k_3148_, v_cleanupAnnotations_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
    return v___x_3155_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___boxed(
    mut v_00_u03b1_3156_: *mut crate::leanh::LeanObject,
    mut v_e_3157_: *mut crate::leanh::LeanObject,
    mut v_k_3158_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3159_: *mut crate::leanh::LeanObject,
    mut v___y_3160_: *mut crate::leanh::LeanObject,
    mut v___y_3161_: *mut crate::leanh::LeanObject,
    mut v___y_3162_: *mut crate::leanh::LeanObject,
    mut v___y_3163_: *mut crate::leanh::LeanObject,
    mut v___y_3164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3165_: u8 = 0;
    let mut v_res_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3165_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_3159_) as u8);
    v_res_3166_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(v_00_u03b1_3156_, v_e_3157_, v_k_3158_, v_cleanupAnnotations_boxed_3165_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
    crate::leanh::lean_dec(v___y_3163_);
    crate::leanh::lean_dec_ref(v___y_3162_);
    crate::leanh::lean_dec(v___y_3161_);
    crate::leanh::lean_dec_ref(v___y_3160_);
    return v_res_3166_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0(
    mut v_xs_3167_: *mut crate::leanh::LeanObject,
    mut v_x_3168_: *mut crate::leanh::LeanObject,
    mut v___y_3169_: *mut crate::leanh::LeanObject,
    mut v___y_3170_: *mut crate::leanh::LeanObject,
    mut v___y_3171_: *mut crate::leanh::LeanObject,
    mut v___y_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3174_ = lean_array_get_size(v_xs_3167_);
    v___x_3175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3175_, 0, v___x_3174_);
    return v___x_3175_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0___boxed(
    mut v_xs_3176_: *mut crate::leanh::LeanObject,
    mut v_x_3177_: *mut crate::leanh::LeanObject,
    mut v___y_3178_: *mut crate::leanh::LeanObject,
    mut v___y_3179_: *mut crate::leanh::LeanObject,
    mut v___y_3180_: *mut crate::leanh::LeanObject,
    mut v___y_3181_: *mut crate::leanh::LeanObject,
    mut v___y_3182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3183_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0(
        v_xs_3176_,
        v_x_3177_,
        v___y_3178_,
        v___y_3179_,
        v___y_3180_,
        v___y_3181_,
    );
    crate::leanh::lean_dec(v___y_3181_);
    crate::leanh::lean_dec_ref(v___y_3180_);
    crate::leanh::lean_dec(v___y_3179_);
    crate::leanh::lean_dec_ref(v___y_3178_);
    crate::leanh::lean_dec_ref(v_x_3177_);
    crate::leanh::lean_dec_ref(v_xs_3176_);
    return v_res_3183_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(
    mut v_msgData_3184_: *mut crate::leanh::LeanObject,
    mut v___y_3185_: *mut crate::leanh::LeanObject,
    mut v___y_3186_: *mut crate::leanh::LeanObject,
    mut v___y_3187_: *mut crate::leanh::LeanObject,
    mut v___y_3188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3190_ = lean_st_ref_get(v___y_3188_);
    v_env_3191_ = crate::leanh::lean_ctor_get(v___x_3190_, 0);
    crate::leanh::lean_inc_ref(v_env_3191_);
    crate::leanh::lean_dec(v___x_3190_);
    v___x_3192_ = lean_st_ref_get(v___y_3186_);
    v_mctx_3193_ = crate::leanh::lean_ctor_get(v___x_3192_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3193_);
    crate::leanh::lean_dec(v___x_3192_);
    v_lctx_3194_ = crate::leanh::lean_ctor_get(v___y_3185_, 2);
    v_options_3195_ = crate::leanh::lean_ctor_get(v___y_3187_, 2);
    crate::leanh::lean_inc_ref(v_options_3195_);
    crate::leanh::lean_inc_ref(v_lctx_3194_);
    v___x_3196_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3196_, 0, v_env_3191_);
    crate::leanh::lean_ctor_set(v___x_3196_, 1, v_mctx_3193_);
    crate::leanh::lean_ctor_set(v___x_3196_, 2, v_lctx_3194_);
    crate::leanh::lean_ctor_set(v___x_3196_, 3, v_options_3195_);
    v___x_3197_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3197_, 0, v___x_3196_);
    crate::leanh::lean_ctor_set(v___x_3197_, 1, v_msgData_3184_);
    v___x_3198_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3198_, 0, v___x_3197_);
    return v___x_3198_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4___boxed(
    mut v_msgData_3199_: *mut crate::leanh::LeanObject,
    mut v___y_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
    mut v___y_3202_: *mut crate::leanh::LeanObject,
    mut v___y_3203_: *mut crate::leanh::LeanObject,
    mut v___y_3204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3205_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(v_msgData_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
    crate::leanh::lean_dec(v___y_3203_);
    crate::leanh::lean_dec_ref(v___y_3202_);
    crate::leanh::lean_dec(v___y_3201_);
    crate::leanh::lean_dec_ref(v___y_3200_);
    return v_res_3205_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(
    mut v_msg_3206_: *mut crate::leanh::LeanObject,
    mut v___y_3207_: *mut crate::leanh::LeanObject,
    mut v___y_3208_: *mut crate::leanh::LeanObject,
    mut v___y_3209_: *mut crate::leanh::LeanObject,
    mut v___y_3210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3217_: u8 = 0;
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3212_ = crate::leanh::lean_ctor_get(v___y_3209_, 5);
                v___x_3213_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(v_msg_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
                v_a_3214_ = crate::leanh::lean_ctor_get(v___x_3213_, 0);
                v_isSharedCheck_3222_ = (!crate::leanh::lean_is_exclusive(v___x_3213_)) as u8;
                if v_isSharedCheck_3222_ == 0 {
                    v___x_3216_ = v___x_3213_;
                    v_isShared_3217_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3214_);
                    crate::leanh::lean_dec(v___x_3213_);
                    v___x_3216_ = crate::leanh::lean_box(0);
                    v_isShared_3217_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3212_);
                v___x_3218_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3218_, 0, v_ref_3212_);
                crate::leanh::lean_ctor_set(v___x_3218_, 1, v_a_3214_);
                if v_isShared_3217_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3216_, 1);
                    crate::leanh::lean_ctor_set(v___x_3216_, 0, v___x_3218_);
                    v___x_3220_ = v___x_3216_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
                    v___x_3220_ = v_reuseFailAlloc_3221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg___boxed(
    mut v_msg_3223_: *mut crate::leanh::LeanObject,
    mut v___y_3224_: *mut crate::leanh::LeanObject,
    mut v___y_3225_: *mut crate::leanh::LeanObject,
    mut v___y_3226_: *mut crate::leanh::LeanObject,
    mut v___y_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3229_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v_msg_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
    crate::leanh::lean_dec(v___y_3227_);
    crate::leanh::lean_dec_ref(v___y_3226_);
    crate::leanh::lean_dec(v___y_3225_);
    crate::leanh::lean_dec_ref(v___y_3224_);
    return v_res_3229_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0()
-> f64 {
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: f64 = 0.0;
    v___x_3230_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3231_ = lean_float_of_nat(v___x_3230_);
    return v___x_3231_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(
    mut v_cls_3235_: *mut crate::leanh::LeanObject,
    mut v_msg_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3247_: u8 = 0;
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v_tid_3261_: u64 = 0;
    let mut v_traces_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: f64 = 0.0;
    let mut v___x_3268_: u8 = 0;
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3242_ = crate::leanh::lean_ctor_get(v___y_3239_, 5);
                v___x_3243_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(v_msg_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
                v_a_3244_ = crate::leanh::lean_ctor_get(v___x_3243_, 0);
                v_isSharedCheck_3288_ = (!crate::leanh::lean_is_exclusive(v___x_3243_)) as u8;
                if v_isSharedCheck_3288_ == 0 {
                    v___x_3246_ = v___x_3243_;
                    v_isShared_3247_ = v_isSharedCheck_3288_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3244_);
                    crate::leanh::lean_dec(v___x_3243_);
                    v___x_3246_ = crate::leanh::lean_box(0);
                    v_isShared_3247_ = v_isSharedCheck_3288_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3248_ = lean_st_ref_take(v___y_3240_);
                v_traceState_3249_ = crate::leanh::lean_ctor_get(v___x_3248_, 4);
                v_env_3250_ = crate::leanh::lean_ctor_get(v___x_3248_, 0);
                v_nextMacroScope_3251_ = crate::leanh::lean_ctor_get(v___x_3248_, 1);
                v_ngen_3252_ = crate::leanh::lean_ctor_get(v___x_3248_, 2);
                v_auxDeclNGen_3253_ = crate::leanh::lean_ctor_get(v___x_3248_, 3);
                v_cache_3254_ = crate::leanh::lean_ctor_get(v___x_3248_, 5);
                v_messages_3255_ = crate::leanh::lean_ctor_get(v___x_3248_, 6);
                v_infoState_3256_ = crate::leanh::lean_ctor_get(v___x_3248_, 7);
                v_snapshotTasks_3257_ = crate::leanh::lean_ctor_get(v___x_3248_, 8);
                v_isSharedCheck_3287_ = (!crate::leanh::lean_is_exclusive(v___x_3248_)) as u8;
                if v_isSharedCheck_3287_ == 0 {
                    v___x_3259_ = v___x_3248_;
                    v_isShared_3260_ = v_isSharedCheck_3287_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3257_);
                    crate::leanh::lean_inc(v_infoState_3256_);
                    crate::leanh::lean_inc(v_messages_3255_);
                    crate::leanh::lean_inc(v_cache_3254_);
                    crate::leanh::lean_inc(v_traceState_3249_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3253_);
                    crate::leanh::lean_inc(v_ngen_3252_);
                    crate::leanh::lean_inc(v_nextMacroScope_3251_);
                    crate::leanh::lean_inc(v_env_3250_);
                    crate::leanh::lean_dec(v___x_3248_);
                    v___x_3259_ = crate::leanh::lean_box(0);
                    v_isShared_3260_ = v_isSharedCheck_3287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3261_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3249_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3262_ = crate::leanh::lean_ctor_get(v_traceState_3249_, 0);
                v_isSharedCheck_3286_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3249_)) as u8;
                if v_isSharedCheck_3286_ == 0 {
                    v___x_3264_ = v_traceState_3249_;
                    v_isShared_3265_ = v_isSharedCheck_3286_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3262_);
                    crate::leanh::lean_dec(v_traceState_3249_);
                    v___x_3264_ = crate::leanh::lean_box(0);
                    v_isShared_3265_ = v_isSharedCheck_3286_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3266_ = crate::leanh::lean_box(0);
                v___x_3267_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0);
                v___x_3268_ = 0;
                v___x_3269_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__1;
                v___x_3270_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3270_, 0, v_cls_3235_);
                crate::leanh::lean_ctor_set(v___x_3270_, 1, v___x_3266_);
                crate::leanh::lean_ctor_set(v___x_3270_, 2, v___x_3269_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3270_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3267_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3270_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3267_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3270_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3268_,
                );
                v___x_3271_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__2;
                v___x_3272_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3272_, 0, v___x_3270_);
                crate::leanh::lean_ctor_set(v___x_3272_, 1, v_a_3244_);
                crate::leanh::lean_ctor_set(v___x_3272_, 2, v___x_3271_);
                crate::leanh::lean_inc(v_ref_3242_);
                v___x_3273_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3273_, 0, v_ref_3242_);
                crate::leanh::lean_ctor_set(v___x_3273_, 1, v___x_3272_);
                v___x_3274_ = l_Lean_PersistentArray_push___redArg(v_traces_3262_, v___x_3273_);
                if v_isShared_3265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3264_, 0, v___x_3274_);
                    v___x_3276_ = v___x_3264_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3274_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3285_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3261_,
                    );
                    v___x_3276_ = v_reuseFailAlloc_3285_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3259_, 4, v___x_3276_);
                    v___x_3278_ = v___x_3259_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_env_3250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_nextMacroScope_3251_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 2, v_ngen_3252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 3, v_auxDeclNGen_3253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 4, v___x_3276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 5, v_cache_3254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 6, v_messages_3255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 7, v_infoState_3256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 8, v_snapshotTasks_3257_);
                    v___x_3278_ = v_reuseFailAlloc_3284_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3279_ = lean_st_ref_set(v___y_3240_, v___x_3278_);
                v___x_3280_ = crate::leanh::lean_box(0);
                if v_isShared_3247_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3246_, 0, v___x_3280_);
                    v___x_3282_ = v___x_3246_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
                    v___x_3282_ = v_reuseFailAlloc_3283_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___boxed(
    mut v_cls_3289_: *mut crate::leanh::LeanObject,
    mut v_msg_3290_: *mut crate::leanh::LeanObject,
    mut v___y_3291_: *mut crate::leanh::LeanObject,
    mut v___y_3292_: *mut crate::leanh::LeanObject,
    mut v___y_3293_: *mut crate::leanh::LeanObject,
    mut v___y_3294_: *mut crate::leanh::LeanObject,
    mut v___y_3295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3296_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v_cls_3289_, v_msg_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
    crate::leanh::lean_dec(v___y_3294_);
    crate::leanh::lean_dec_ref(v___y_3293_);
    crate::leanh::lean_dec(v___y_3292_);
    crate::leanh::lean_dec_ref(v___y_3291_);
    return v_res_3296_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10(
    mut v_a_3297_: *mut crate::leanh::LeanObject,
    mut v_a_3298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3297_) == 0 {
                    v___x_3299_ = l_List_reverse___redArg(v_a_3298_);
                    return v___x_3299_;
                } else {
                    v_head_3300_ = crate::leanh::lean_ctor_get(v_a_3297_, 0);
                    v_tail_3301_ = crate::leanh::lean_ctor_get(v_a_3297_, 1);
                    v_isSharedCheck_3310_ = (!crate::leanh::lean_is_exclusive(v_a_3297_)) as u8;
                    if v_isSharedCheck_3310_ == 0 {
                        v___x_3303_ = v_a_3297_;
                        v_isShared_3304_ = v_isSharedCheck_3310_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3301_);
                        crate::leanh::lean_inc(v_head_3300_);
                        crate::leanh::lean_dec(v_a_3297_);
                        v___x_3303_ = crate::leanh::lean_box(0);
                        v_isShared_3304_ = v_isSharedCheck_3310_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3305_ = l_Lean_MessageData_ofExpr(v_head_3300_);
                if v_isShared_3304_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3303_, 1, v_a_3298_);
                    crate::leanh::lean_ctor_set(v___x_3303_, 0, v___x_3305_);
                    v___x_3307_ = v___x_3303_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3309_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3305_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3309_, 1, v_a_3298_);
                    v___x_3307_ = v_reuseFailAlloc_3309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3297_ = v_tail_3301_;
                v_a_3298_ = v___x_3307_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9(
    mut v_sz_3311_: usize,
    mut v_i_3312_: usize,
    mut v_bs_3313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3314_: u8 = 0;
    let mut v_v_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: usize = 0;
    let mut v___x_3320_: usize = 0;
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3314_ = lean_usize_dec_lt(v_i_3312_, v_sz_3311_);
                if v___x_3314_ == 0 {
                    return v_bs_3313_;
                } else {
                    v_v_3315_ = lean_array_uget_borrowed(v_bs_3313_, v_i_3312_);
                    v_type_3316_ = crate::leanh::lean_ctor_get(v_v_3315_, 2);
                    crate::leanh::lean_inc_ref(v_type_3316_);
                    v___x_3317_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3318_ = lean_array_uset(v_bs_3313_, v_i_3312_, v___x_3317_);
                    v___x_3319_ = 1usize;
                    v___x_3320_ = lean_usize_add(v_i_3312_, v___x_3319_);
                    v___x_3321_ = lean_array_uset(v_bs_x27_3318_, v_i_3312_, v_type_3316_);
                    v_i_3312_ = v___x_3320_;
                    v_bs_3313_ = v___x_3321_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___boxed(
    mut v_sz_3323_: *mut crate::leanh::LeanObject,
    mut v_i_3324_: *mut crate::leanh::LeanObject,
    mut v_bs_3325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3326_: usize = 0;
    let mut v_i_boxed_3327_: usize = 0;
    let mut v_res_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3326_ = crate::leanh::lean_unbox_usize(v_sz_3323_);
    crate::leanh::lean_dec(v_sz_3323_);
    v_i_boxed_3327_ = crate::leanh::lean_unbox_usize(v_i_3324_);
    crate::leanh::lean_dec(v_i_3324_);
    v_res_3328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9(v_sz_boxed_3326_, v_i_boxed_3327_, v_bs_3325_);
    return v_res_3328_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3332_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__1;
    v___x_3333_ = l_Lean_MessageData_ofFormat(v___x_3332_);
    return v___x_3333_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3334_ = crate::leanh::lean_box(1);
    v___x_3335_ = l_Lean_MessageData_ofFormat(v___x_3334_);
    return v___x_3335_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(
    mut v_a_3336_: *mut crate::leanh::LeanObject,
    mut v_a_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3343_: u8 = 0;
    let mut v_fst_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3348_: u8 = 0;
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3363_: u8 = 0;
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3336_) == 0 {
                    v___x_3338_ = l_List_reverse___redArg(v_a_3337_);
                    return v___x_3338_;
                } else {
                    v_head_3339_ = crate::leanh::lean_ctor_get(v_a_3336_, 0);
                    v_tail_3340_ = crate::leanh::lean_ctor_get(v_a_3336_, 1);
                    v_isSharedCheck_3364_ = (!crate::leanh::lean_is_exclusive(v_a_3336_)) as u8;
                    if v_isSharedCheck_3364_ == 0 {
                        v___x_3342_ = v_a_3336_;
                        v_isShared_3343_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3340_);
                        crate::leanh::lean_inc(v_head_3339_);
                        crate::leanh::lean_dec(v_a_3336_);
                        v___x_3342_ = crate::leanh::lean_box(0);
                        v_isShared_3343_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3344_ = crate::leanh::lean_ctor_get(v_head_3339_, 0);
                v_snd_3345_ = crate::leanh::lean_ctor_get(v_head_3339_, 1);
                v_isSharedCheck_3363_ = (!crate::leanh::lean_is_exclusive(v_head_3339_)) as u8;
                if v_isSharedCheck_3363_ == 0 {
                    v___x_3347_ = v_head_3339_;
                    v_isShared_3348_ = v_isSharedCheck_3363_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3345_);
                    crate::leanh::lean_inc(v_fst_3344_);
                    crate::leanh::lean_dec(v_head_3339_);
                    v___x_3347_ = crate::leanh::lean_box(0);
                    v_isShared_3348_ = v_isSharedCheck_3363_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3349_ = l_Lean_MessageData_ofName(v_fst_3344_);
                v___x_3350_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2_once), _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2);
                if v_isShared_3348_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3347_, 7);
                    crate::leanh::lean_ctor_set(v___x_3347_, 1, v___x_3350_);
                    crate::leanh::lean_ctor_set(v___x_3347_, 0, v___x_3349_);
                    v___x_3352_ = v___x_3347_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3362_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 1, v___x_3350_);
                    v___x_3352_ = v_reuseFailAlloc_3362_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3353_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3_once), _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3);
                v___x_3354_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3354_, 0, v___x_3352_);
                crate::leanh::lean_ctor_set(v___x_3354_, 1, v___x_3353_);
                v___x_3355_ = l_Lean_MessageData_ofName(v_snd_3345_);
                v___x_3356_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3356_, 0, v___x_3354_);
                crate::leanh::lean_ctor_set(v___x_3356_, 1, v___x_3355_);
                v___x_3357_ = l_Lean_MessageData_paren(v___x_3356_);
                if v_isShared_3343_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3342_, 1, v_a_3337_);
                    crate::leanh::lean_ctor_set(v___x_3342_, 0, v___x_3357_);
                    v___x_3359_ = v___x_3342_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3361_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_a_3337_);
                    v___x_3359_ = v_reuseFailAlloc_3361_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_3336_ = v_tail_3340_;
                v_a_3337_ = v___x_3359_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__2(
    mut v_a_3365_: *mut crate::leanh::LeanObject,
    mut v_a_3366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3372_: u8 = 0;
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3365_) == 0 {
                    v___x_3367_ = l_List_reverse___redArg(v_a_3366_);
                    return v___x_3367_;
                } else {
                    v_head_3368_ = crate::leanh::lean_ctor_get(v_a_3365_, 0);
                    v_tail_3369_ = crate::leanh::lean_ctor_get(v_a_3365_, 1);
                    v_isSharedCheck_3378_ = (!crate::leanh::lean_is_exclusive(v_a_3365_)) as u8;
                    if v_isSharedCheck_3378_ == 0 {
                        v___x_3371_ = v_a_3365_;
                        v_isShared_3372_ = v_isSharedCheck_3378_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3369_);
                        crate::leanh::lean_inc(v_head_3368_);
                        crate::leanh::lean_dec(v_a_3365_);
                        v___x_3371_ = crate::leanh::lean_box(0);
                        v_isShared_3372_ = v_isSharedCheck_3378_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3373_ = l_Lean_mkLevelParam(v_head_3368_);
                if v_isShared_3372_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3371_, 1, v_a_3366_);
                    crate::leanh::lean_ctor_set(v___x_3371_, 0, v___x_3373_);
                    v___x_3375_ = v___x_3371_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3377_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3373_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3377_, 1, v_a_3366_);
                    v___x_3375_ = v_reuseFailAlloc_3377_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3365_ = v_tail_3369_;
                v_a_3366_ = v___x_3375_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(
    mut v_xs_3379_: *mut crate::leanh::LeanObject,
    mut v_ys_3380_: *mut crate::leanh::LeanObject,
    mut v_x_3381_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3383_: u8 = 0;
    let mut v_one_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3382_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3383_ = lean_nat_dec_eq(v_x_3381_, v_zero_3382_);
                if v_isZero_3383_ == 1 {
                    crate::leanh::lean_dec(v_x_3381_);
                    return v_isZero_3383_;
                } else {
                    v_one_3384_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3385_ = lean_nat_sub(v_x_3381_, v_one_3384_);
                    crate::leanh::lean_dec(v_x_3381_);
                    v___x_3386_ = lean_array_fget_borrowed(v_xs_3379_, v_n_3385_);
                    v___x_3387_ = lean_array_fget_borrowed(v_ys_3380_, v_n_3385_);
                    v___x_3388_ = lean_expr_eqv(v___x_3386_, v___x_3387_);
                    if v___x_3388_ == 0 {
                        crate::leanh::lean_dec(v_n_3385_);
                        return v___x_3388_;
                    } else {
                        v_x_3381_ = v_n_3385_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg___boxed(
    mut v_xs_3390_: *mut crate::leanh::LeanObject,
    mut v_ys_3391_: *mut crate::leanh::LeanObject,
    mut v_x_3392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3393_: u8 = 0;
    let mut v_r_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3393_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(v_xs_3390_, v_ys_3391_, v_x_3392_);
    crate::leanh::lean_dec_ref(v_ys_3391_);
    crate::leanh::lean_dec_ref(v_xs_3390_);
    v_r_3394_ = crate::leanh::lean_box((v_res_3393_) as usize);
    return v_r_3394_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(
    mut v_a_3395_: *mut crate::leanh::LeanObject,
    mut v_a_3396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3402_: u8 = 0;
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3408_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3395_) == 0 {
                    v___x_3397_ = l_List_reverse___redArg(v_a_3396_);
                    return v___x_3397_;
                } else {
                    v_head_3398_ = crate::leanh::lean_ctor_get(v_a_3395_, 0);
                    v_tail_3399_ = crate::leanh::lean_ctor_get(v_a_3395_, 1);
                    v_isSharedCheck_3408_ = (!crate::leanh::lean_is_exclusive(v_a_3395_)) as u8;
                    if v_isSharedCheck_3408_ == 0 {
                        v___x_3401_ = v_a_3395_;
                        v_isShared_3402_ = v_isSharedCheck_3408_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3399_);
                        crate::leanh::lean_inc(v_head_3398_);
                        crate::leanh::lean_dec(v_a_3395_);
                        v___x_3401_ = crate::leanh::lean_box(0);
                        v_isShared_3402_ = v_isSharedCheck_3408_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3403_ = l_Lean_MessageData_ofLevel(v_head_3398_);
                if v_isShared_3402_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3401_, 1, v_a_3396_);
                    crate::leanh::lean_ctor_set(v___x_3401_, 0, v___x_3403_);
                    v___x_3405_ = v___x_3401_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3407_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_a_3396_);
                    v___x_3405_ = v_reuseFailAlloc_3407_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3395_ = v_tail_3399_;
                v_a_3396_ = v___x_3405_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5(
    mut v_x_3409_: *mut crate::leanh::LeanObject,
    mut v_x_3410_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3411_: u8 = 0;
    let mut v___x_3412_: u8 = 0;
    let mut v___x_3413_: u8 = 0;
    let mut v_head_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3409_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_3410_) == 0 {
                        v___x_3411_ = 1;
                        return v___x_3411_;
                    } else {
                        v___x_3412_ = 0;
                        return v___x_3412_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_3410_) == 0 {
                        v___x_3413_ = 0;
                        return v___x_3413_;
                    } else {
                        v_head_3414_ = crate::leanh::lean_ctor_get(v_x_3409_, 0);
                        v_tail_3415_ = crate::leanh::lean_ctor_get(v_x_3409_, 1);
                        v_head_3416_ = crate::leanh::lean_ctor_get(v_x_3410_, 0);
                        v_tail_3417_ = crate::leanh::lean_ctor_get(v_x_3410_, 1);
                        v___x_3418_ = lean_level_eq(v_head_3414_, v_head_3416_);
                        if v___x_3418_ == 0 {
                            return v___x_3418_;
                        } else {
                            v_x_3409_ = v_tail_3415_;
                            v_x_3410_ = v_tail_3417_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5___boxed(
    mut v_x_3420_: *mut crate::leanh::LeanObject,
    mut v_x_3421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3422_: u8 = 0;
    let mut v_r_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3422_ =
        l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5(
            v_x_3420_, v_x_3421_,
        );
    crate::leanh::lean_dec(v_x_3421_);
    crate::leanh::lean_dec(v_x_3420_);
    v_r_3423_ = crate::leanh::lean_box((v_res_3422_) as usize);
    return v_r_3423_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3424_ = crate::leanh::lean_box(0);
    v_dummy_3425_ = l_Lean_Expr_sort___override(v___x_3424_);
    return v_dummy_3425_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1;
    v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
    return v___x_3428_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3;
    v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
    return v___x_3431_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5;
    v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
    return v___x_3434_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7;
    v___x_3437_ = l_Lean_stringToMessageData(v___x_3436_);
    return v___x_3437_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9;
    v___x_3440_ = l_Lean_stringToMessageData(v___x_3439_);
    return v___x_3440_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11;
    v___x_3443_ = l_Lean_stringToMessageData(v___x_3442_);
    return v___x_3443_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13;
    v___x_3446_ = l_Lean_stringToMessageData(v___x_3445_);
    return v___x_3446_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15;
    v___x_3449_ = l_Lean_stringToMessageData(v___x_3448_);
    return v___x_3449_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17;
    v___x_3452_ = l_Lean_stringToMessageData(v___x_3451_);
    return v___x_3452_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19;
    v___x_3455_ = l_Lean_stringToMessageData(v___x_3454_);
    return v___x_3455_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(
    mut v_val_3456_: *mut crate::leanh::LeanObject,
    mut v_a_3457_: *mut crate::leanh::LeanObject,
    mut v___x_3458_: *mut crate::leanh::LeanObject,
    mut v_xs_3459_: *mut crate::leanh::LeanObject,
    mut v___x_3460_: *mut crate::leanh::LeanObject,
    mut v___x_3461_: *mut crate::leanh::LeanObject,
    mut v_as_3462_: *mut crate::leanh::LeanObject,
    mut v_sz_3463_: usize,
    mut v_i_3464_: usize,
    mut v_b_3465_: *mut crate::leanh::LeanObject,
    mut v___y_3466_: *mut crate::leanh::LeanObject,
    mut v___y_3467_: *mut crate::leanh::LeanObject,
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: usize = 0;
    let mut v___x_3474_: usize = 0;
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v_fst_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3488_: u8 = 0;
    let mut v_fst_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3492_: u8 = 0;
    let mut v_array_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: u8 = 0;
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3509_: u8 = 0;
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: u8 = 0;
    let mut v_a_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3522_: u8 = 0;
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_privateSpecs_3540_: u8 = 0;
    let mut v___y_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_projFn_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: u8 = 0;
    let mut v___x_3565_: u8 = 0;
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: u8 = 0;
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3580_: u8 = 0;
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3584_: u8 = 0;
    let mut v_a_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3588_: u8 = 0;
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3592_: u8 = 0;
    let mut v_a_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3596_: u8 = 0;
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3600_: u8 = 0;
    let mut v_a_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3604_: u8 = 0;
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_3640_: u8 = 0;
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: u8 = 0;
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: u8 = 0;
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: u8 = 0;
    let mut v___x_3648_: u8 = 0;
    let mut v___x_3649_: u8 = 0;
    let mut v___y_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3664_: u8 = 0;
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3668_: u8 = 0;
    let mut v_dummy_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u8 = 0;
    let mut v___x_3682_: u8 = 0;
    let mut v___y_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: u8 = 0;
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3708_: u8 = 0;
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3712_: u8 = 0;
    let mut v___x_3713_: u8 = 0;
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3727_: u8 = 0;
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3741_: u8 = 0;
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3745_: u8 = 0;
    let mut v_isSharedCheck_3746_: u8 = 0;
    let mut v_unused_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3750_: u8 = 0;
    let mut v_unused_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3752_: u8 = 0;
    let mut v_unused_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut v_unused_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3476_ = lean_usize_dec_lt(v_i_3464_, v_sz_3463_);
                if v___x_3476_ == 0 {
                    crate::leanh::lean_dec(v___x_3461_);
                    crate::leanh::lean_dec(v___x_3460_);
                    crate::leanh::lean_dec_ref(v___x_3458_);
                    crate::leanh::lean_dec_ref(v_a_3457_);
                    crate::leanh::lean_dec(v_val_3456_);
                    v___x_3477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3477_, 0, v_b_3465_);
                    return v___x_3477_;
                } else {
                    v_snd_3478_ = crate::leanh::lean_ctor_get(v_b_3465_, 1);
                    crate::leanh::lean_inc(v_snd_3478_);
                    v_snd_3479_ = crate::leanh::lean_ctor_get(v_snd_3478_, 1);
                    crate::leanh::lean_inc(v_snd_3479_);
                    v_snd_3480_ = crate::leanh::lean_ctor_get(v_snd_3479_, 1);
                    crate::leanh::lean_inc(v_snd_3480_);
                    v_fst_3481_ = crate::leanh::lean_ctor_get(v_b_3465_, 0);
                    v_isSharedCheck_3754_ = (!crate::leanh::lean_is_exclusive(v_b_3465_)) as u8;
                    if v_isSharedCheck_3754_ == 0 {
                        v_unused_3755_ = crate::leanh::lean_ctor_get(v_b_3465_, 1);
                        crate::leanh::lean_dec(v_unused_3755_);
                        v___x_3483_ = v_b_3465_;
                        v_isShared_3484_ = v_isSharedCheck_3754_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_3481_);
                        crate::leanh::lean_dec(v_b_3465_);
                        v___x_3483_ = crate::leanh::lean_box(0);
                        v_isShared_3484_ = v_isSharedCheck_3754_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3473_ = 1usize;
                v___x_3474_ = lean_usize_add(v_i_3464_, v___x_3473_);
                v_i_3464_ = v___x_3474_;
                v_b_3465_ = v_a_3472_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_3485_ = crate::leanh::lean_ctor_get(v_snd_3478_, 0);
                v_isSharedCheck_3752_ = (!crate::leanh::lean_is_exclusive(v_snd_3478_)) as u8;
                if v_isSharedCheck_3752_ == 0 {
                    v_unused_3753_ = crate::leanh::lean_ctor_get(v_snd_3478_, 1);
                    crate::leanh::lean_dec(v_unused_3753_);
                    v___x_3487_ = v_snd_3478_;
                    v_isShared_3488_ = v_isSharedCheck_3752_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3485_);
                    crate::leanh::lean_dec(v_snd_3478_);
                    v___x_3487_ = crate::leanh::lean_box(0);
                    v_isShared_3488_ = v_isSharedCheck_3752_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_3489_ = crate::leanh::lean_ctor_get(v_snd_3479_, 0);
                v_isSharedCheck_3750_ = (!crate::leanh::lean_is_exclusive(v_snd_3479_)) as u8;
                if v_isSharedCheck_3750_ == 0 {
                    v_unused_3751_ = crate::leanh::lean_ctor_get(v_snd_3479_, 1);
                    crate::leanh::lean_dec(v_unused_3751_);
                    v___x_3491_ = v_snd_3479_;
                    v_isShared_3492_ = v_isSharedCheck_3750_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3489_);
                    crate::leanh::lean_dec(v_snd_3479_);
                    v___x_3491_ = crate::leanh::lean_box(0);
                    v_isShared_3492_ = v_isSharedCheck_3750_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_array_3493_ = crate::leanh::lean_ctor_get(v_snd_3480_, 0);
                v_start_3494_ = crate::leanh::lean_ctor_get(v_snd_3480_, 1);
                v_stop_3495_ = crate::leanh::lean_ctor_get(v_snd_3480_, 2);
                v___x_3496_ = lean_nat_dec_lt(v_start_3494_, v_stop_3495_);
                if v___x_3496_ == 0 {
                    crate::leanh::lean_dec(v___x_3461_);
                    crate::leanh::lean_dec(v___x_3460_);
                    crate::leanh::lean_dec_ref(v___x_3458_);
                    crate::leanh::lean_dec_ref(v_a_3457_);
                    crate::leanh::lean_dec(v_val_3456_);
                    if v_isShared_3492_ == 0 {
                        v___x_3498_ = v___x_3491_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3506_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_fst_3489_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_snd_3480_);
                        v___x_3498_ = v_reuseFailAlloc_3506_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_3495_);
                    crate::leanh::lean_inc(v_start_3494_);
                    crate::leanh::lean_inc_ref(v_array_3493_);
                    v_isSharedCheck_3746_ = (!crate::leanh::lean_is_exclusive(v_snd_3480_)) as u8;
                    if v_isSharedCheck_3746_ == 0 {
                        v_unused_3747_ = crate::leanh::lean_ctor_get(v_snd_3480_, 2);
                        crate::leanh::lean_dec(v_unused_3747_);
                        v_unused_3748_ = crate::leanh::lean_ctor_get(v_snd_3480_, 1);
                        crate::leanh::lean_dec(v_unused_3748_);
                        v_unused_3749_ = crate::leanh::lean_ctor_get(v_snd_3480_, 0);
                        crate::leanh::lean_dec(v_unused_3749_);
                        v___x_3508_ = v_snd_3480_;
                        v_isShared_3509_ = v_isSharedCheck_3746_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_3480_);
                        v___x_3508_ = crate::leanh::lean_box(0);
                        v_isShared_3509_ = v_isSharedCheck_3746_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3487_, 1, v___x_3498_);
                    v___x_3500_ = v___x_3487_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_fst_3485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 1, v___x_3498_);
                    v___x_3500_ = v_reuseFailAlloc_3505_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3484_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3483_, 1, v___x_3500_);
                    v___x_3502_ = v___x_3483_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3504_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_fst_3481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3500_);
                    v___x_3502_ = v_reuseFailAlloc_3504_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3503_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3503_, 0, v___x_3502_);
                return v___x_3503_;
            }
            8 => {
                v___x_3510_ = lean_array_fget(v_array_3493_, v_start_3494_);
                crate::leanh::lean_inc(v___x_3510_);
                v___x_3511_ = l_Lean_Meta_isProof(
                    v___x_3510_,
                    v___y_3466_,
                    v___y_3467_,
                    v___y_3468_,
                    v___y_3469_,
                );
                if crate::leanh::lean_obj_tag(v___x_3511_) == 0 {
                    v_a_3512_ = crate::leanh::lean_ctor_get(v___x_3511_, 0);
                    crate::leanh::lean_inc(v_a_3512_);
                    crate::leanh::lean_dec_ref_known(v___x_3511_, 1);
                    v___x_3513_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3514_ = lean_nat_add(v_start_3494_, v___x_3513_);
                    crate::leanh::lean_dec(v_start_3494_);
                    if v_isShared_3509_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3508_, 1, v___x_3514_);
                        v___x_3516_ = v___x_3508_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3737_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_array_3493_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 1, v___x_3514_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 2, v_stop_3495_);
                        v___x_3516_ = v_reuseFailAlloc_3737_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3510_);
                    crate::leanh::lean_del_object(v___x_3508_);
                    crate::leanh::lean_dec(v_stop_3495_);
                    crate::leanh::lean_dec(v_start_3494_);
                    crate::leanh::lean_dec_ref(v_array_3493_);
                    crate::leanh::lean_del_object(v___x_3491_);
                    crate::leanh::lean_dec(v_fst_3489_);
                    crate::leanh::lean_del_object(v___x_3487_);
                    crate::leanh::lean_dec(v_fst_3485_);
                    crate::leanh::lean_del_object(v___x_3483_);
                    crate::leanh::lean_dec(v_fst_3481_);
                    crate::leanh::lean_dec(v___x_3461_);
                    crate::leanh::lean_dec(v___x_3460_);
                    crate::leanh::lean_dec_ref(v___x_3458_);
                    crate::leanh::lean_dec_ref(v_a_3457_);
                    crate::leanh::lean_dec(v_val_3456_);
                    v_a_3738_ = crate::leanh::lean_ctor_get(v___x_3511_, 0);
                    v_isSharedCheck_3745_ = (!crate::leanh::lean_is_exclusive(v___x_3511_)) as u8;
                    if v_isSharedCheck_3745_ == 0 {
                        v___x_3740_ = v___x_3511_;
                        v_isShared_3741_ = v_isSharedCheck_3745_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3738_);
                        crate::leanh::lean_dec(v___x_3511_);
                        v___x_3740_ = crate::leanh::lean_box(0);
                        v_isShared_3741_ = v_isSharedCheck_3745_;
                        state = 38;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3517_ = (crate::leanh::lean_unbox(v_a_3512_) as u8);
                if v___x_3517_ == 0 {
                    v_a_3518_ = lean_array_uget_borrowed(v_as_3462_, v_i_3464_);
                    v___x_3537_ = l_Lean_Expr_eta(v___x_3510_);
                    v___x_3629_ = l_Lean_Expr_getAppFn(v___x_3537_);
                    v_dummy_3669_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0);
                    v_nargs_3670_ = l_Lean_Expr_getAppNumArgs(v___x_3537_);
                    crate::leanh::lean_inc(v_nargs_3670_);
                    v___x_3671_ = lean_mk_array(v_nargs_3670_, v_dummy_3669_);
                    v___x_3672_ = lean_nat_sub(v_nargs_3670_, v___x_3513_);
                    crate::leanh::lean_dec(v_nargs_3670_);
                    crate::leanh::lean_inc_ref(v___x_3537_);
                    v___x_3673_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v___x_3537_,
                        v___x_3671_,
                        v___x_3672_,
                    );
                    v___x_3713_ = l_Lean_Expr_isConst(v___x_3629_);
                    if v___x_3713_ == 0 {
                        v___x_3714_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18);
                        crate::leanh::lean_inc(v_a_3518_);
                        v___x_3715_ = l_Lean_MessageData_ofName(v_a_3518_);
                        v___x_3716_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3716_, 0, v___x_3714_);
                        crate::leanh::lean_ctor_set(v___x_3716_, 1, v___x_3715_);
                        v___x_3717_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20);
                        v___x_3718_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3718_, 0, v___x_3716_);
                        crate::leanh::lean_ctor_set(v___x_3718_, 1, v___x_3717_);
                        v___x_3719_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_3718_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
                        if crate::leanh::lean_obj_tag(v___x_3719_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3719_, 1);
                            v___y_3684_ = v___y_3466_;
                            v___y_3685_ = v___y_3467_;
                            v___y_3686_ = v___y_3468_;
                            v___y_3687_ = v___y_3469_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3673_);
                            crate::leanh::lean_dec_ref(v___x_3629_);
                            crate::leanh::lean_dec_ref(v___x_3537_);
                            crate::leanh::lean_dec_ref(v___x_3516_);
                            crate::leanh::lean_dec(v_a_3512_);
                            crate::leanh::lean_del_object(v___x_3491_);
                            crate::leanh::lean_dec(v_fst_3489_);
                            crate::leanh::lean_del_object(v___x_3487_);
                            crate::leanh::lean_dec(v_fst_3485_);
                            crate::leanh::lean_del_object(v___x_3483_);
                            crate::leanh::lean_dec(v_fst_3481_);
                            crate::leanh::lean_dec(v___x_3461_);
                            crate::leanh::lean_dec(v___x_3460_);
                            crate::leanh::lean_dec_ref(v___x_3458_);
                            crate::leanh::lean_dec_ref(v_a_3457_);
                            crate::leanh::lean_dec(v_val_3456_);
                            v_a_3720_ = crate::leanh::lean_ctor_get(v___x_3719_, 0);
                            v_isSharedCheck_3727_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3719_)) as u8;
                            if v_isSharedCheck_3727_ == 0 {
                                v___x_3722_ = v___x_3719_;
                                v_isShared_3723_ = v_isSharedCheck_3727_;
                                state = 33;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3720_);
                                crate::leanh::lean_dec(v___x_3719_);
                                v___x_3722_ = crate::leanh::lean_box(0);
                                v_isShared_3723_ = v_isSharedCheck_3727_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        v___y_3684_ = v___y_3466_;
                        v___y_3685_ = v___y_3467_;
                        v___y_3686_ = v___y_3468_;
                        v___y_3687_ = v___y_3469_;
                        state = 30;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3512_);
                    crate::leanh::lean_dec(v___x_3510_);
                    if v_isShared_3492_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3491_, 1, v___x_3516_);
                        v___x_3729_ = v___x_3491_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_3736_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_fst_3489_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3736_, 1, v___x_3516_);
                        v___x_3729_ = v_reuseFailAlloc_3736_;
                        state = 35;
                        continue;
                    }
                }
            }
            10 => {
                crate::leanh::lean_inc(v___y_3521_);
                crate::leanh::lean_inc(v_a_3518_);
                if v_isShared_3492_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3491_, 1, v___y_3521_);
                    crate::leanh::lean_ctor_set(v___x_3491_, 0, v_a_3518_);
                    v___x_3524_ = v___x_3491_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3536_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3518_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3536_, 1, v___y_3521_);
                    v___x_3524_ = v_reuseFailAlloc_3536_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3525_ = lean_array_push(v_fst_3481_, v___x_3524_);
                crate::leanh::lean_inc(v___x_3460_);
                v___x_3526_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3526_, 0, v___y_3521_);
                crate::leanh::lean_ctor_set(v___x_3526_, 1, v___x_3460_);
                crate::leanh::lean_ctor_set(v___x_3526_, 2, v___y_3520_);
                v___x_3527_ = lean_array_push(v_fst_3485_, v___x_3526_);
                v___x_3528_ = crate::leanh::lean_box((v___y_3522_) as usize);
                if v_isShared_3488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3487_, 1, v___x_3516_);
                    crate::leanh::lean_ctor_set(v___x_3487_, 0, v___x_3528_);
                    v___x_3530_ = v___x_3487_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3535_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___x_3516_);
                    v___x_3530_ = v_reuseFailAlloc_3535_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3484_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3483_, 1, v___x_3530_);
                    crate::leanh::lean_ctor_set(v___x_3483_, 0, v___x_3527_);
                    v___x_3532_ = v___x_3483_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3534_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3530_);
                    v___x_3532_ = v_reuseFailAlloc_3534_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_3533_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3533_, 0, v___x_3525_);
                crate::leanh::lean_ctor_set(v___x_3533_, 1, v___x_3532_);
                v_a_3472_ = v___x_3533_;
                state = 1;
                continue;
            }
            14 => {
                v___x_3545_ = lean_st_ref_get(v___y_3544_);
                v_env_3546_ = crate::leanh::lean_ctor_get(v___x_3545_, 0);
                crate::leanh::lean_inc_ref(v_env_3546_);
                crate::leanh::lean_dec(v___x_3545_);
                crate::leanh::lean_inc(v_a_3518_);
                crate::leanh::lean_inc(v_val_3456_);
                v___x_3547_ = l_Lean_getFieldInfo_x3f(v_env_3546_, v_val_3456_, v_a_3518_);
                if crate::leanh::lean_obj_tag(v___x_3547_) == 1 {
                    v_val_3548_ = crate::leanh::lean_ctor_get(v___x_3547_, 0);
                    crate::leanh::lean_inc(v_val_3548_);
                    crate::leanh::lean_dec_ref_known(v___x_3547_, 1);
                    v_projFn_3549_ = crate::leanh::lean_ctor_get(v_val_3548_, 1);
                    crate::leanh::lean_inc(v_projFn_3549_);
                    crate::leanh::lean_dec(v_val_3548_);
                    v___x_3550_ = l_Lean_Expr_getAppFn(v_a_3457_);
                    v___x_3551_ = l_Lean_Expr_constLevels_x21(v___x_3550_);
                    crate::leanh::lean_dec_ref(v___x_3550_);
                    v___x_3552_ = l_Lean_mkConst(v_projFn_3549_, v___x_3551_);
                    v_dummy_3553_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0);
                    v_nargs_3554_ = l_Lean_Expr_getAppNumArgs(v_a_3457_);
                    crate::leanh::lean_inc(v_nargs_3554_);
                    v___x_3555_ = lean_mk_array(v_nargs_3554_, v_dummy_3553_);
                    v___x_3556_ = lean_nat_sub(v_nargs_3554_, v___x_3513_);
                    crate::leanh::lean_dec(v_nargs_3554_);
                    crate::leanh::lean_inc_ref(v_a_3457_);
                    v___x_3557_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_a_3457_,
                        v___x_3555_,
                        v___x_3556_,
                    );
                    v___x_3558_ = lean_mk_empty_array_with_capacity(v___x_3513_);
                    crate::leanh::lean_inc_ref(v___x_3458_);
                    v___x_3559_ = lean_array_push(v___x_3558_, v___x_3458_);
                    v___x_3560_ = l_Array_append___redArg(v___x_3557_, v___x_3559_);
                    crate::leanh::lean_dec_ref(v___x_3559_);
                    v___x_3561_ = l_Lean_mkAppN(v___x_3552_, v___x_3560_);
                    crate::leanh::lean_dec_ref(v___x_3560_);
                    crate::leanh::lean_inc_ref(v___x_3561_);
                    crate::leanh::lean_inc_ref(v___x_3537_);
                    v___x_3562_ = l_Lean_Meta_mkEq(
                        v___x_3537_,
                        v___x_3561_,
                        v___y_3541_,
                        v___y_3542_,
                        v___y_3543_,
                        v___y_3544_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3562_) == 0 {
                        v_a_3563_ = crate::leanh::lean_ctor_get(v___x_3562_, 0);
                        crate::leanh::lean_inc_n(v_a_3563_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3562_, 1);
                        v___x_3564_ = 1;
                        v___x_3565_ = (crate::leanh::lean_unbox(v_a_3512_) as u8);
                        crate::leanh::lean_dec(v_a_3512_);
                        v___x_3566_ = l_Lean_Meta_mkForallFVars(
                            v_xs_3459_,
                            v_a_3563_,
                            v___x_3565_,
                            v___x_3496_,
                            v___x_3496_,
                            v___x_3564_,
                            v___y_3541_,
                            v___y_3542_,
                            v___y_3543_,
                            v___y_3544_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3566_) == 0 {
                            v_a_3567_ = crate::leanh::lean_ctor_get(v___x_3566_, 0);
                            crate::leanh::lean_inc(v_a_3567_);
                            crate::leanh::lean_dec_ref_known(v___x_3566_, 1);
                            v___x_3568_ = l_Lean_Meta_isExprDefEq(
                                v___x_3537_,
                                v___x_3561_,
                                v___y_3541_,
                                v___y_3542_,
                                v___y_3543_,
                                v___y_3544_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3568_) == 0 {
                                v_a_3569_ = crate::leanh::lean_ctor_get(v___x_3568_, 0);
                                crate::leanh::lean_inc(v_a_3569_);
                                crate::leanh::lean_dec_ref_known(v___x_3568_, 1);
                                v___x_3570_ = (crate::leanh::lean_unbox(v_a_3569_) as u8);
                                crate::leanh::lean_dec(v_a_3569_);
                                if v___x_3570_ == 0 {
                                    v___x_3571_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2);
                                    v___x_3572_ = l_Lean_MessageData_ofExpr(v_a_3563_);
                                    v___x_3573_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3573_, 0, v___x_3571_);
                                    crate::leanh::lean_ctor_set(v___x_3573_, 1, v___x_3572_);
                                    v___x_3574_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4);
                                    v___x_3575_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3575_, 0, v___x_3573_);
                                    crate::leanh::lean_ctor_set(v___x_3575_, 1, v___x_3574_);
                                    v___x_3576_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_3575_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
                                    if crate::leanh::lean_obj_tag(v___x_3576_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3576_, 1);
                                        v___y_3520_ = v_a_3567_;
                                        v___y_3521_ = v___y_3539_;
                                        v___y_3522_ = v_privateSpecs_3540_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_3567_);
                                        crate::leanh::lean_dec(v___y_3539_);
                                        crate::leanh::lean_dec_ref(v___x_3516_);
                                        crate::leanh::lean_del_object(v___x_3491_);
                                        crate::leanh::lean_del_object(v___x_3487_);
                                        crate::leanh::lean_dec(v_fst_3485_);
                                        crate::leanh::lean_del_object(v___x_3483_);
                                        crate::leanh::lean_dec(v_fst_3481_);
                                        crate::leanh::lean_dec(v___x_3461_);
                                        crate::leanh::lean_dec(v___x_3460_);
                                        crate::leanh::lean_dec_ref(v___x_3458_);
                                        crate::leanh::lean_dec_ref(v_a_3457_);
                                        crate::leanh::lean_dec(v_val_3456_);
                                        v_a_3577_ = crate::leanh::lean_ctor_get(v___x_3576_, 0);
                                        v_isSharedCheck_3584_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3576_)) as u8;
                                        if v_isSharedCheck_3584_ == 0 {
                                            v___x_3579_ = v___x_3576_;
                                            v_isShared_3580_ = v_isSharedCheck_3584_;
                                            state = 15;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3577_);
                                            crate::leanh::lean_dec(v___x_3576_);
                                            v___x_3579_ = crate::leanh::lean_box(0);
                                            v_isShared_3580_ = v_isSharedCheck_3584_;
                                            state = 15;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3563_);
                                    v___y_3520_ = v_a_3567_;
                                    v___y_3521_ = v___y_3539_;
                                    v___y_3522_ = v_privateSpecs_3540_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3567_);
                                crate::leanh::lean_dec(v_a_3563_);
                                crate::leanh::lean_dec(v___y_3539_);
                                crate::leanh::lean_dec_ref(v___x_3516_);
                                crate::leanh::lean_del_object(v___x_3491_);
                                crate::leanh::lean_del_object(v___x_3487_);
                                crate::leanh::lean_dec(v_fst_3485_);
                                crate::leanh::lean_del_object(v___x_3483_);
                                crate::leanh::lean_dec(v_fst_3481_);
                                crate::leanh::lean_dec(v___x_3461_);
                                crate::leanh::lean_dec(v___x_3460_);
                                crate::leanh::lean_dec_ref(v___x_3458_);
                                crate::leanh::lean_dec_ref(v_a_3457_);
                                crate::leanh::lean_dec(v_val_3456_);
                                v_a_3585_ = crate::leanh::lean_ctor_get(v___x_3568_, 0);
                                v_isSharedCheck_3592_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3568_)) as u8;
                                if v_isSharedCheck_3592_ == 0 {
                                    v___x_3587_ = v___x_3568_;
                                    v_isShared_3588_ = v_isSharedCheck_3592_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3585_);
                                    crate::leanh::lean_dec(v___x_3568_);
                                    v___x_3587_ = crate::leanh::lean_box(0);
                                    v_isShared_3588_ = v_isSharedCheck_3592_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3563_);
                            crate::leanh::lean_dec_ref(v___x_3561_);
                            crate::leanh::lean_dec(v___y_3539_);
                            crate::leanh::lean_dec_ref(v___x_3537_);
                            crate::leanh::lean_dec_ref(v___x_3516_);
                            crate::leanh::lean_del_object(v___x_3491_);
                            crate::leanh::lean_del_object(v___x_3487_);
                            crate::leanh::lean_dec(v_fst_3485_);
                            crate::leanh::lean_del_object(v___x_3483_);
                            crate::leanh::lean_dec(v_fst_3481_);
                            crate::leanh::lean_dec(v___x_3461_);
                            crate::leanh::lean_dec(v___x_3460_);
                            crate::leanh::lean_dec_ref(v___x_3458_);
                            crate::leanh::lean_dec_ref(v_a_3457_);
                            crate::leanh::lean_dec(v_val_3456_);
                            v_a_3593_ = crate::leanh::lean_ctor_get(v___x_3566_, 0);
                            v_isSharedCheck_3600_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3566_)) as u8;
                            if v_isSharedCheck_3600_ == 0 {
                                v___x_3595_ = v___x_3566_;
                                v_isShared_3596_ = v_isSharedCheck_3600_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3593_);
                                crate::leanh::lean_dec(v___x_3566_);
                                v___x_3595_ = crate::leanh::lean_box(0);
                                v_isShared_3596_ = v_isSharedCheck_3600_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3561_);
                        crate::leanh::lean_dec(v___y_3539_);
                        crate::leanh::lean_dec_ref(v___x_3537_);
                        crate::leanh::lean_dec_ref(v___x_3516_);
                        crate::leanh::lean_dec(v_a_3512_);
                        crate::leanh::lean_del_object(v___x_3491_);
                        crate::leanh::lean_del_object(v___x_3487_);
                        crate::leanh::lean_dec(v_fst_3485_);
                        crate::leanh::lean_del_object(v___x_3483_);
                        crate::leanh::lean_dec(v_fst_3481_);
                        crate::leanh::lean_dec(v___x_3461_);
                        crate::leanh::lean_dec(v___x_3460_);
                        crate::leanh::lean_dec_ref(v___x_3458_);
                        crate::leanh::lean_dec_ref(v_a_3457_);
                        crate::leanh::lean_dec(v_val_3456_);
                        v_a_3601_ = crate::leanh::lean_ctor_get(v___x_3562_, 0);
                        v_isSharedCheck_3608_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3562_)) as u8;
                        if v_isSharedCheck_3608_ == 0 {
                            v___x_3603_ = v___x_3562_;
                            v_isShared_3604_ = v_isSharedCheck_3608_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3601_);
                            crate::leanh::lean_dec(v___x_3562_);
                            v___x_3603_ = crate::leanh::lean_box(0);
                            v_isShared_3604_ = v_isSharedCheck_3608_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3547_);
                    crate::leanh::lean_dec(v___y_3539_);
                    crate::leanh::lean_dec_ref(v___x_3537_);
                    crate::leanh::lean_dec(v_a_3512_);
                    crate::leanh::lean_del_object(v___x_3491_);
                    crate::leanh::lean_del_object(v___x_3487_);
                    crate::leanh::lean_del_object(v___x_3483_);
                    v___x_3609_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6);
                    crate::leanh::lean_inc(v_a_3518_);
                    v___x_3610_ = l_Lean_MessageData_ofName(v_a_3518_);
                    v___x_3611_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3611_, 0, v___x_3609_);
                    crate::leanh::lean_ctor_set(v___x_3611_, 1, v___x_3610_);
                    v___x_3612_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8);
                    v___x_3613_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3613_, 0, v___x_3611_);
                    crate::leanh::lean_ctor_set(v___x_3613_, 1, v___x_3612_);
                    crate::leanh::lean_inc(v_val_3456_);
                    v___x_3614_ = l_Lean_MessageData_ofName(v_val_3456_);
                    v___x_3615_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3615_, 0, v___x_3613_);
                    crate::leanh::lean_ctor_set(v___x_3615_, 1, v___x_3614_);
                    v___x_3616_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_3615_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
                    if crate::leanh::lean_obj_tag(v___x_3616_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3616_, 1);
                        v___x_3617_ = crate::leanh::lean_box((v_privateSpecs_3540_) as usize);
                        v___x_3618_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3618_, 0, v___x_3617_);
                        crate::leanh::lean_ctor_set(v___x_3618_, 1, v___x_3516_);
                        v___x_3619_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3619_, 0, v_fst_3485_);
                        crate::leanh::lean_ctor_set(v___x_3619_, 1, v___x_3618_);
                        v___x_3620_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3620_, 0, v_fst_3481_);
                        crate::leanh::lean_ctor_set(v___x_3620_, 1, v___x_3619_);
                        v_a_3472_ = v___x_3620_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3516_);
                        crate::leanh::lean_dec(v_fst_3485_);
                        crate::leanh::lean_dec(v_fst_3481_);
                        crate::leanh::lean_dec(v___x_3461_);
                        crate::leanh::lean_dec(v___x_3460_);
                        crate::leanh::lean_dec_ref(v___x_3458_);
                        crate::leanh::lean_dec_ref(v_a_3457_);
                        crate::leanh::lean_dec(v_val_3456_);
                        v_a_3621_ = crate::leanh::lean_ctor_get(v___x_3616_, 0);
                        v_isSharedCheck_3628_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3616_)) as u8;
                        if v_isSharedCheck_3628_ == 0 {
                            v___x_3623_ = v___x_3616_;
                            v_isShared_3624_ = v_isSharedCheck_3628_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3621_);
                            crate::leanh::lean_dec(v___x_3616_);
                            v___x_3623_ = crate::leanh::lean_box(0);
                            v_isShared_3624_ = v_isSharedCheck_3628_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            15 => {
                if v_isShared_3580_ == 0 {
                    v___x_3582_ = v___x_3579_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
                    v___x_3582_ = v_reuseFailAlloc_3583_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3582_;
            }
            17 => {
                if v_isShared_3588_ == 0 {
                    v___x_3590_ = v___x_3587_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3591_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
                    v___x_3590_ = v_reuseFailAlloc_3591_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3590_;
            }
            19 => {
                if v_isShared_3596_ == 0 {
                    v___x_3598_ = v___x_3595_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3599_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
                    v___x_3598_ = v_reuseFailAlloc_3599_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3598_;
            }
            21 => {
                if v_isShared_3604_ == 0 {
                    v___x_3606_ = v___x_3603_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3607_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
                    v___x_3606_ = v_reuseFailAlloc_3607_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3606_;
            }
            23 => {
                if v_isShared_3624_ == 0 {
                    v___x_3626_ = v___x_3623_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
                    v___x_3626_ = v_reuseFailAlloc_3627_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3626_;
            }
            25 => {
                v___x_3635_ = lean_st_ref_get(v___y_3634_);
                v___x_3636_ = lean_st_ref_get(v___y_3634_);
                v_env_3637_ = crate::leanh::lean_ctor_get(v___x_3635_, 0);
                crate::leanh::lean_inc_ref(v_env_3637_);
                crate::leanh::lean_dec(v___x_3635_);
                v_env_3638_ = crate::leanh::lean_ctor_get(v___x_3636_, 0);
                crate::leanh::lean_inc_ref(v_env_3638_);
                crate::leanh::lean_dec(v___x_3636_);
                v___x_3639_ = l_Lean_Environment_header(v_env_3637_);
                crate::leanh::lean_dec_ref(v_env_3637_);
                v_isModule_3640_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3639_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 4) as u32,
                );
                crate::leanh::lean_dec_ref(v___x_3639_);
                v___x_3641_ = l_Lean_Expr_constName_x21(v___x_3629_);
                crate::leanh::lean_dec_ref(v___x_3629_);
                if v_isModule_3640_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_3638_);
                    v___x_3642_ = (crate::leanh::lean_unbox(v_fst_3489_) as u8);
                    crate::leanh::lean_dec(v_fst_3489_);
                    v___y_3539_ = v___x_3641_;
                    v_privateSpecs_3540_ = v___x_3642_;
                    v___y_3541_ = v___y_3631_;
                    v___y_3542_ = v___y_3632_;
                    v___y_3543_ = v___y_3633_;
                    v___y_3544_ = v___y_3634_;
                    state = 14;
                    continue;
                } else {
                    v___x_3643_ = l_Lean_Environment_setExporting(v_env_3638_, v___x_3496_);
                    v___x_3644_ = (crate::leanh::lean_unbox(v_a_3512_) as u8);
                    crate::leanh::lean_inc(v___x_3641_);
                    v___x_3645_ =
                        l_Lean_Environment_find_x3f(v___x_3643_, v___x_3641_, v___x_3644_);
                    if crate::leanh::lean_obj_tag(v___x_3645_) == 0 {
                        crate::leanh::lean_dec(v_fst_3489_);
                        v___y_3539_ = v___x_3641_;
                        v_privateSpecs_3540_ = v___x_3496_;
                        v___y_3541_ = v___y_3631_;
                        v___y_3542_ = v___y_3632_;
                        v___y_3543_ = v___y_3633_;
                        v___y_3544_ = v___y_3634_;
                        state = 14;
                        continue;
                    } else {
                        v_val_3646_ = crate::leanh::lean_ctor_get(v___x_3645_, 0);
                        crate::leanh::lean_inc(v_val_3646_);
                        crate::leanh::lean_dec_ref_known(v___x_3645_, 1);
                        v___x_3647_ = (crate::leanh::lean_unbox(v_a_3512_) as u8);
                        v___x_3648_ = l_Lean_ConstantInfo_hasValue(v_val_3646_, v___x_3647_);
                        crate::leanh::lean_dec(v_val_3646_);
                        if v___x_3648_ == 0 {
                            crate::leanh::lean_dec(v_fst_3489_);
                            v___y_3539_ = v___x_3641_;
                            v_privateSpecs_3540_ = v___x_3496_;
                            v___y_3541_ = v___y_3631_;
                            v___y_3542_ = v___y_3632_;
                            v___y_3543_ = v___y_3633_;
                            v___y_3544_ = v___y_3634_;
                            state = 14;
                            continue;
                        } else {
                            v___x_3649_ = (crate::leanh::lean_unbox(v_fst_3489_) as u8);
                            crate::leanh::lean_dec(v_fst_3489_);
                            v___y_3539_ = v___x_3641_;
                            v_privateSpecs_3540_ = v___x_3649_;
                            v___y_3541_ = v___y_3631_;
                            v___y_3542_ = v___y_3632_;
                            v___y_3543_ = v___y_3633_;
                            v___y_3544_ = v___y_3634_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            26 => {
                v___x_3655_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10);
                crate::leanh::lean_inc_ref(v___x_3629_);
                v___x_3656_ = l_Lean_MessageData_ofExpr(v___x_3629_);
                v___x_3657_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3657_, 0, v___x_3655_);
                crate::leanh::lean_ctor_set(v___x_3657_, 1, v___x_3656_);
                v___x_3658_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12);
                v___x_3659_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3659_, 0, v___x_3657_);
                crate::leanh::lean_ctor_set(v___x_3659_, 1, v___x_3658_);
                v___x_3660_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_3659_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3651_);
                if crate::leanh::lean_obj_tag(v___x_3660_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3660_, 1);
                    v___y_3631_ = v___y_3652_;
                    v___y_3632_ = v___y_3653_;
                    v___y_3633_ = v___y_3654_;
                    v___y_3634_ = v___y_3651_;
                    state = 25;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_3629_);
                    crate::leanh::lean_dec_ref(v___x_3537_);
                    crate::leanh::lean_dec_ref(v___x_3516_);
                    crate::leanh::lean_dec(v_a_3512_);
                    crate::leanh::lean_del_object(v___x_3491_);
                    crate::leanh::lean_dec(v_fst_3489_);
                    crate::leanh::lean_del_object(v___x_3487_);
                    crate::leanh::lean_dec(v_fst_3485_);
                    crate::leanh::lean_del_object(v___x_3483_);
                    crate::leanh::lean_dec(v_fst_3481_);
                    crate::leanh::lean_dec(v___x_3461_);
                    crate::leanh::lean_dec(v___x_3460_);
                    crate::leanh::lean_dec_ref(v___x_3458_);
                    crate::leanh::lean_dec_ref(v_a_3457_);
                    crate::leanh::lean_dec(v_val_3456_);
                    v_a_3661_ = crate::leanh::lean_ctor_get(v___x_3660_, 0);
                    v_isSharedCheck_3668_ = (!crate::leanh::lean_is_exclusive(v___x_3660_)) as u8;
                    if v_isSharedCheck_3668_ == 0 {
                        v___x_3663_ = v___x_3660_;
                        v_isShared_3664_ = v_isSharedCheck_3668_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3661_);
                        crate::leanh::lean_dec(v___x_3660_);
                        v___x_3663_ = crate::leanh::lean_box(0);
                        v_isShared_3664_ = v_isSharedCheck_3668_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_3664_ == 0 {
                    v___x_3666_ = v___x_3663_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3667_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
                    v___x_3666_ = v_reuseFailAlloc_3667_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3666_;
            }
            29 => {
                v___x_3679_ = lean_array_get_size(v_xs_3459_);
                v___x_3680_ = lean_array_get_size(v___x_3673_);
                v___x_3681_ = lean_nat_dec_eq(v___x_3679_, v___x_3680_);
                if v___x_3681_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3673_);
                    v___y_3651_ = v___y_3678_;
                    v___y_3652_ = v___y_3675_;
                    v___y_3653_ = v___y_3676_;
                    v___y_3654_ = v___y_3677_;
                    state = 26;
                    continue;
                } else {
                    v___x_3682_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(v_xs_3459_, v___x_3673_, v___x_3679_);
                    crate::leanh::lean_dec_ref(v___x_3673_);
                    if v___x_3682_ == 0 {
                        v___y_3651_ = v___y_3678_;
                        v___y_3652_ = v___y_3675_;
                        v___y_3653_ = v___y_3676_;
                        v___y_3654_ = v___y_3677_;
                        state = 26;
                        continue;
                    } else {
                        v___y_3631_ = v___y_3675_;
                        v___y_3632_ = v___y_3676_;
                        v___y_3633_ = v___y_3677_;
                        v___y_3634_ = v___y_3678_;
                        state = 25;
                        continue;
                    }
                }
            }
            30 => {
                v___x_3688_ = l_Lean_Expr_constLevels_x21(v___x_3629_);
                v___x_3689_ = l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5(v___x_3688_, v___x_3461_);
                if v___x_3689_ == 0 {
                    v___x_3690_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10);
                    crate::leanh::lean_inc_ref(v___x_3629_);
                    v___x_3691_ = l_Lean_MessageData_ofExpr(v___x_3629_);
                    v___x_3692_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3692_, 0, v___x_3690_);
                    crate::leanh::lean_ctor_set(v___x_3692_, 1, v___x_3691_);
                    v___x_3693_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14);
                    v___x_3694_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3694_, 0, v___x_3692_);
                    crate::leanh::lean_ctor_set(v___x_3694_, 1, v___x_3693_);
                    v___x_3695_ = crate::leanh::lean_box(0);
                    v___x_3696_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(v___x_3688_, v___x_3695_);
                    v___x_3697_ = l_Lean_MessageData_ofList(v___x_3696_);
                    v___x_3698_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3698_, 0, v___x_3694_);
                    crate::leanh::lean_ctor_set(v___x_3698_, 1, v___x_3697_);
                    v___x_3699_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16);
                    v___x_3700_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3700_, 0, v___x_3698_);
                    crate::leanh::lean_ctor_set(v___x_3700_, 1, v___x_3699_);
                    crate::leanh::lean_inc(v___x_3461_);
                    v___x_3701_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(v___x_3461_, v___x_3695_);
                    v___x_3702_ = l_Lean_MessageData_ofList(v___x_3701_);
                    v___x_3703_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3703_, 0, v___x_3700_);
                    crate::leanh::lean_ctor_set(v___x_3703_, 1, v___x_3702_);
                    v___x_3704_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_3703_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
                    if crate::leanh::lean_obj_tag(v___x_3704_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3704_, 1);
                        v___y_3675_ = v___y_3684_;
                        v___y_3676_ = v___y_3685_;
                        v___y_3677_ = v___y_3686_;
                        v___y_3678_ = v___y_3687_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3673_);
                        crate::leanh::lean_dec_ref(v___x_3629_);
                        crate::leanh::lean_dec_ref(v___x_3537_);
                        crate::leanh::lean_dec_ref(v___x_3516_);
                        crate::leanh::lean_dec(v_a_3512_);
                        crate::leanh::lean_del_object(v___x_3491_);
                        crate::leanh::lean_dec(v_fst_3489_);
                        crate::leanh::lean_del_object(v___x_3487_);
                        crate::leanh::lean_dec(v_fst_3485_);
                        crate::leanh::lean_del_object(v___x_3483_);
                        crate::leanh::lean_dec(v_fst_3481_);
                        crate::leanh::lean_dec(v___x_3461_);
                        crate::leanh::lean_dec(v___x_3460_);
                        crate::leanh::lean_dec_ref(v___x_3458_);
                        crate::leanh::lean_dec_ref(v_a_3457_);
                        crate::leanh::lean_dec(v_val_3456_);
                        v_a_3705_ = crate::leanh::lean_ctor_get(v___x_3704_, 0);
                        v_isSharedCheck_3712_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3704_)) as u8;
                        if v_isSharedCheck_3712_ == 0 {
                            v___x_3707_ = v___x_3704_;
                            v_isShared_3708_ = v_isSharedCheck_3712_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3705_);
                            crate::leanh::lean_dec(v___x_3704_);
                            v___x_3707_ = crate::leanh::lean_box(0);
                            v_isShared_3708_ = v_isSharedCheck_3712_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3688_);
                    v___y_3675_ = v___y_3684_;
                    v___y_3676_ = v___y_3685_;
                    v___y_3677_ = v___y_3686_;
                    v___y_3678_ = v___y_3687_;
                    state = 29;
                    continue;
                }
            }
            31 => {
                if v_isShared_3708_ == 0 {
                    v___x_3710_ = v___x_3707_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
                    v___x_3710_ = v_reuseFailAlloc_3711_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3710_;
            }
            33 => {
                if v_isShared_3723_ == 0 {
                    v___x_3725_ = v___x_3722_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3726_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
                    v___x_3725_ = v_reuseFailAlloc_3726_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3725_;
            }
            35 => {
                if v_isShared_3488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3487_, 1, v___x_3729_);
                    v___x_3731_ = v___x_3487_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3735_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_fst_3485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___x_3729_);
                    v___x_3731_ = v_reuseFailAlloc_3735_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_3484_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3483_, 1, v___x_3731_);
                    v___x_3733_ = v___x_3483_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_fst_3481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___x_3731_);
                    v___x_3733_ = v_reuseFailAlloc_3734_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v_a_3472_ = v___x_3733_;
                state = 1;
                continue;
            }
            38 => {
                if v_isShared_3741_ == 0 {
                    v___x_3743_ = v___x_3740_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3744_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
                    v___x_3743_ = v_reuseFailAlloc_3744_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_3743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___boxed(
    mut v_val_3756_: *mut crate::leanh::LeanObject,
    mut v_a_3757_: *mut crate::leanh::LeanObject,
    mut v___x_3758_: *mut crate::leanh::LeanObject,
    mut v_xs_3759_: *mut crate::leanh::LeanObject,
    mut v___x_3760_: *mut crate::leanh::LeanObject,
    mut v___x_3761_: *mut crate::leanh::LeanObject,
    mut v_as_3762_: *mut crate::leanh::LeanObject,
    mut v_sz_3763_: *mut crate::leanh::LeanObject,
    mut v_i_3764_: *mut crate::leanh::LeanObject,
    mut v_b_3765_: *mut crate::leanh::LeanObject,
    mut v___y_3766_: *mut crate::leanh::LeanObject,
    mut v___y_3767_: *mut crate::leanh::LeanObject,
    mut v___y_3768_: *mut crate::leanh::LeanObject,
    mut v___y_3769_: *mut crate::leanh::LeanObject,
    mut v___y_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3771_: usize = 0;
    let mut v_i_boxed_3772_: usize = 0;
    let mut v_res_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3771_ = crate::leanh::lean_unbox_usize(v_sz_3763_);
    crate::leanh::lean_dec(v_sz_3763_);
    v_i_boxed_3772_ = crate::leanh::lean_unbox_usize(v_i_3764_);
    crate::leanh::lean_dec(v_i_3764_);
    v_res_3773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(v_val_3756_, v_a_3757_, v___x_3758_, v_xs_3759_, v___x_3760_, v___x_3761_, v_as_3762_, v_sz_boxed_3771_, v_i_boxed_3772_, v_b_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
    crate::leanh::lean_dec(v___y_3769_);
    crate::leanh::lean_dec_ref(v___y_3768_);
    crate::leanh::lean_dec(v___y_3767_);
    crate::leanh::lean_dec_ref(v___y_3766_);
    crate::leanh::lean_dec_ref(v_as_3762_);
    crate::leanh::lean_dec_ref(v_xs_3759_);
    return v_res_3773_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3784_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3;
    v___x_3785_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5;
    v___x_3786_ = l_Lean_Name_append(v___x_3785_, v___x_3784_);
    return v___x_3786_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3788_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7;
    v___x_3789_ = l_Lean_stringToMessageData(v___x_3788_);
    return v___x_3789_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3791_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9;
    v___x_3792_ = l_Lean_stringToMessageData(v___x_3791_);
    return v___x_3792_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11;
    v___x_3795_ = l_Lean_stringToMessageData(v___x_3794_);
    return v___x_3795_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3797_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13;
    v___x_3798_ = l_Lean_stringToMessageData(v___x_3797_);
    return v___x_3798_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3802_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17;
    v___x_3803_ = l_Lean_stringToMessageData(v___x_3802_);
    return v___x_3803_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3805_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__19;
    v___x_3806_ = l_Lean_stringToMessageData(v___x_3805_);
    return v___x_3806_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1(
    mut v_type_3807_: *mut crate::leanh::LeanObject,
    mut v_val_3808_: *mut crate::leanh::LeanObject,
    mut v_levelParams_3809_: *mut crate::leanh::LeanObject,
    mut v_name_3810_: *mut crate::leanh::LeanObject,
    mut v_val_3811_: *mut crate::leanh::LeanObject,
    mut v___x_3812_: u8,
    mut v_instName_3813_: *mut crate::leanh::LeanObject,
    mut v_a_3814_: *mut crate::leanh::LeanObject,
    mut v_xs_3815_: *mut crate::leanh::LeanObject,
    mut v_body_3816_: *mut crate::leanh::LeanObject,
    mut v___y_3817_: *mut crate::leanh::LeanObject,
    mut v___y_3818_: *mut crate::leanh::LeanObject,
    mut v___y_3819_: *mut crate::leanh::LeanObject,
    mut v___y_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: u8 = 0;
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldNames_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3878_: usize = 0;
    let mut v___x_3879_: usize = 0;
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3885_: u8 = 0;
    let mut v_fst_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v_fst_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3896_: u8 = 0;
    let mut v_fst_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3900_: u8 = 0;
    let mut v_inheritedTraceOptions_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3919_: usize = 0;
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3933_: u8 = 0;
    let mut v_unused_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_unused_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut v_unused_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3942_: u8 = 0;
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3957_: u8 = 0;
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3961_: u8 = 0;
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: u8 = 0;
    let mut v___x_3964_: u8 = 0;
    let mut v_a_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3968_: u8 = 0;
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut v_a_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3976_: u8 = 0;
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3852_ = l_Lean_Meta_instantiateForall(
                    v_type_3807_,
                    v_xs_3815_,
                    v___y_3817_,
                    v___y_3818_,
                    v___y_3819_,
                    v___y_3820_,
                );
                if crate::leanh::lean_obj_tag(v___x_3852_) == 0 {
                    v_a_3853_ = crate::leanh::lean_ctor_get(v___x_3852_, 0);
                    crate::leanh::lean_inc(v_a_3853_);
                    crate::leanh::lean_dec_ref_known(v___x_3852_, 1);
                    crate::leanh::lean_inc_ref(v_body_3816_);
                    v___x_3854_ = l_Lean_Meta_isConstructorApp(
                        v_body_3816_,
                        v___y_3817_,
                        v___y_3818_,
                        v___y_3819_,
                        v___y_3820_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3854_) == 0 {
                        v_a_3855_ = crate::leanh::lean_ctor_get(v___x_3854_, 0);
                        crate::leanh::lean_inc(v_a_3855_);
                        crate::leanh::lean_dec_ref_known(v___x_3854_, 1);
                        v___x_3856_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_levelParams_3809_);
                        v___x_3857_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__2(v_levelParams_3809_, v___x_3856_);
                        crate::leanh::lean_inc(v___x_3857_);
                        v___x_3858_ = l_Lean_mkConst(v_name_3810_, v___x_3857_);
                        v___x_3859_ = l_Lean_mkAppN(v___x_3858_, v_xs_3815_);
                        v___x_3962_ = lean_array_get_size(v_xs_3815_);
                        v___x_3963_ = lean_nat_dec_eq(v___x_3962_, v_a_3814_);
                        if v___x_3963_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3859_);
                            crate::leanh::lean_dec(v___x_3857_);
                            crate::leanh::lean_dec(v_a_3855_);
                            crate::leanh::lean_dec(v_a_3853_);
                            crate::leanh::lean_dec_ref(v_body_3816_);
                            crate::leanh::lean_dec(v_levelParams_3809_);
                            crate::leanh::lean_dec(v_val_3808_);
                            state = 14;
                            continue;
                        } else {
                            v___x_3964_ = (crate::leanh::lean_unbox(v_a_3855_) as u8);
                            crate::leanh::lean_dec(v_a_3855_);
                            if v___x_3964_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3859_);
                                crate::leanh::lean_dec(v___x_3857_);
                                crate::leanh::lean_dec(v_a_3853_);
                                crate::leanh::lean_dec_ref(v_body_3816_);
                                crate::leanh::lean_dec(v_levelParams_3809_);
                                crate::leanh::lean_dec(v_val_3808_);
                                state = 14;
                                continue;
                            } else {
                                v___y_3861_ = v___y_3817_;
                                v___y_3862_ = v___y_3818_;
                                v___y_3863_ = v___y_3819_;
                                v___y_3864_ = v___y_3820_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3853_);
                        crate::leanh::lean_dec_ref(v_body_3816_);
                        crate::leanh::lean_dec(v_instName_3813_);
                        crate::leanh::lean_dec(v_name_3810_);
                        crate::leanh::lean_dec(v_levelParams_3809_);
                        crate::leanh::lean_dec(v_val_3808_);
                        v_a_3965_ = crate::leanh::lean_ctor_get(v___x_3854_, 0);
                        v_isSharedCheck_3972_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3854_)) as u8;
                        if v_isSharedCheck_3972_ == 0 {
                            v___x_3967_ = v___x_3854_;
                            v_isShared_3968_ = v_isSharedCheck_3972_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3965_);
                            crate::leanh::lean_dec(v___x_3854_);
                            v___x_3967_ = crate::leanh::lean_box(0);
                            v_isShared_3968_ = v_isSharedCheck_3972_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_body_3816_);
                    crate::leanh::lean_dec(v_instName_3813_);
                    crate::leanh::lean_dec(v_name_3810_);
                    crate::leanh::lean_dec(v_levelParams_3809_);
                    crate::leanh::lean_dec(v_val_3808_);
                    v_a_3973_ = crate::leanh::lean_ctor_get(v___x_3852_, 0);
                    v_isSharedCheck_3980_ = (!crate::leanh::lean_is_exclusive(v___x_3852_)) as u8;
                    if v_isSharedCheck_3980_ == 0 {
                        v___x_3975_ = v___x_3852_;
                        v_isShared_3976_ = v_isSharedCheck_3980_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3973_);
                        crate::leanh::lean_dec(v___x_3852_);
                        v___x_3975_ = crate::leanh::lean_box(0);
                        v_isShared_3976_ = v_isSharedCheck_3980_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3826_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3826_, 0, v_val_3808_);
                crate::leanh::lean_ctor_set(v___x_3826_, 1, v___y_3824_);
                crate::leanh::lean_ctor_set(v___x_3826_, 2, v___y_3825_);
                v___x_3827_ = (crate::leanh::lean_unbox(v___y_3823_) as u8);
                crate::leanh::lean_dec(v___y_3823_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3826_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3827_,
                );
                v___x_3828_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3828_, 0, v___x_3826_);
                return v___x_3828_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_3839_);
                v___x_3840_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3840_, 0, v___y_3839_);
                v___x_3841_ = l_Lean_MessageData_ofFormat(v___x_3840_);
                v___x_3842_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3842_, 0, v___y_3834_);
                crate::leanh::lean_ctor_set(v___x_3842_, 1, v___x_3841_);
                crate::leanh::lean_inc(v___y_3833_);
                v___x_3843_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v___y_3833_, v___x_3842_, v___y_3835_, v___y_3830_, v___y_3837_, v___y_3831_);
                if crate::leanh::lean_obj_tag(v___x_3843_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3843_, 1);
                    v___y_3823_ = v___y_3832_;
                    v___y_3824_ = v___y_3836_;
                    v___y_3825_ = v___y_3838_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3838_);
                    crate::leanh::lean_dec(v___y_3836_);
                    crate::leanh::lean_dec(v___y_3832_);
                    crate::leanh::lean_dec(v_val_3808_);
                    v_a_3844_ = crate::leanh::lean_ctor_get(v___x_3843_, 0);
                    v_isSharedCheck_3851_ = (!crate::leanh::lean_is_exclusive(v___x_3843_)) as u8;
                    if v_isSharedCheck_3851_ == 0 {
                        v___x_3846_ = v___x_3843_;
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3844_);
                        crate::leanh::lean_dec(v___x_3843_);
                        v___x_3846_ = crate::leanh::lean_box(0);
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3847_ == 0 {
                    v___x_3849_ = v___x_3846_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3850_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
                    v___x_3849_ = v_reuseFailAlloc_3850_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3849_;
            }
            5 => {
                v_fieldNames_3865_ = crate::leanh::lean_ctor_get(v_val_3811_, 1);
                v___x_3866_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3867_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0;
                v___x_3868_ = lean_array_get_size(v_fieldNames_3865_);
                v_dummy_3869_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0);
                v___x_3870_ = lean_mk_array(v___x_3868_, v_dummy_3869_);
                v___x_3871_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(
                    v___x_3868_,
                    v_body_3816_,
                    v___x_3870_,
                );
                v___x_3872_ = lean_array_get_size(v___x_3871_);
                v___x_3873_ = l_Array_toSubarray___redArg(v___x_3871_, v___x_3866_, v___x_3872_);
                v___x_3874_ = crate::leanh::lean_box((v___x_3812_) as usize);
                v___x_3875_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3875_, 0, v___x_3874_);
                crate::leanh::lean_ctor_set(v___x_3875_, 1, v___x_3873_);
                v___x_3876_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3876_, 0, v___x_3867_);
                crate::leanh::lean_ctor_set(v___x_3876_, 1, v___x_3875_);
                v___x_3877_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3877_, 0, v___x_3867_);
                crate::leanh::lean_ctor_set(v___x_3877_, 1, v___x_3876_);
                v_sz_3878_ = lean_array_size(v_fieldNames_3865_);
                v___x_3879_ = 0usize;
                crate::leanh::lean_inc(v_val_3808_);
                v___x_3880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(v_val_3808_, v_a_3853_, v___x_3859_, v_xs_3815_, v_levelParams_3809_, v___x_3857_, v_fieldNames_3865_, v_sz_3878_, v___x_3879_, v___x_3877_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
                if crate::leanh::lean_obj_tag(v___x_3880_) == 0 {
                    v_a_3881_ = crate::leanh::lean_ctor_get(v___x_3880_, 0);
                    crate::leanh::lean_inc(v_a_3881_);
                    crate::leanh::lean_dec_ref_known(v___x_3880_, 1);
                    v_snd_3882_ = crate::leanh::lean_ctor_get(v_a_3881_, 1);
                    crate::leanh::lean_inc(v_snd_3882_);
                    v_snd_3883_ = crate::leanh::lean_ctor_get(v_snd_3882_, 1);
                    crate::leanh::lean_inc(v_snd_3883_);
                    v_options_3884_ = crate::leanh::lean_ctor_get(v___y_3863_, 2);
                    v_hasTrace_3885_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_3884_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3885_ == 0 {
                        crate::leanh::lean_dec(v_instName_3813_);
                        v_fst_3886_ = crate::leanh::lean_ctor_get(v_a_3881_, 0);
                        crate::leanh::lean_inc(v_fst_3886_);
                        crate::leanh::lean_dec(v_a_3881_);
                        v_fst_3887_ = crate::leanh::lean_ctor_get(v_snd_3882_, 0);
                        crate::leanh::lean_inc(v_fst_3887_);
                        crate::leanh::lean_dec(v_snd_3882_);
                        v_fst_3888_ = crate::leanh::lean_ctor_get(v_snd_3883_, 0);
                        crate::leanh::lean_inc(v_fst_3888_);
                        crate::leanh::lean_dec(v_snd_3883_);
                        v___y_3823_ = v_fst_3888_;
                        v___y_3824_ = v_fst_3886_;
                        v___y_3825_ = v_fst_3887_;
                        state = 1;
                        continue;
                    } else {
                        v_fst_3889_ = crate::leanh::lean_ctor_get(v_a_3881_, 0);
                        v_isSharedCheck_3937_ = (!crate::leanh::lean_is_exclusive(v_a_3881_)) as u8;
                        if v_isSharedCheck_3937_ == 0 {
                            v_unused_3938_ = crate::leanh::lean_ctor_get(v_a_3881_, 1);
                            crate::leanh::lean_dec(v_unused_3938_);
                            v___x_3891_ = v_a_3881_;
                            v_isShared_3892_ = v_isSharedCheck_3937_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fst_3889_);
                            crate::leanh::lean_dec(v_a_3881_);
                            v___x_3891_ = crate::leanh::lean_box(0);
                            v_isShared_3892_ = v_isSharedCheck_3937_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_instName_3813_);
                    crate::leanh::lean_dec(v_val_3808_);
                    v_a_3939_ = crate::leanh::lean_ctor_get(v___x_3880_, 0);
                    v_isSharedCheck_3946_ = (!crate::leanh::lean_is_exclusive(v___x_3880_)) as u8;
                    if v_isSharedCheck_3946_ == 0 {
                        v___x_3941_ = v___x_3880_;
                        v_isShared_3942_ = v_isSharedCheck_3946_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3939_);
                        crate::leanh::lean_dec(v___x_3880_);
                        v___x_3941_ = crate::leanh::lean_box(0);
                        v_isShared_3942_ = v_isSharedCheck_3946_;
                        state = 12;
                        continue;
                    }
                }
            }
            6 => {
                v_fst_3893_ = crate::leanh::lean_ctor_get(v_snd_3882_, 0);
                v_isSharedCheck_3935_ = (!crate::leanh::lean_is_exclusive(v_snd_3882_)) as u8;
                if v_isSharedCheck_3935_ == 0 {
                    v_unused_3936_ = crate::leanh::lean_ctor_get(v_snd_3882_, 1);
                    crate::leanh::lean_dec(v_unused_3936_);
                    v___x_3895_ = v_snd_3882_;
                    v_isShared_3896_ = v_isSharedCheck_3935_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3893_);
                    crate::leanh::lean_dec(v_snd_3882_);
                    v___x_3895_ = crate::leanh::lean_box(0);
                    v_isShared_3896_ = v_isSharedCheck_3935_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_3897_ = crate::leanh::lean_ctor_get(v_snd_3883_, 0);
                v_isSharedCheck_3933_ = (!crate::leanh::lean_is_exclusive(v_snd_3883_)) as u8;
                if v_isSharedCheck_3933_ == 0 {
                    v_unused_3934_ = crate::leanh::lean_ctor_get(v_snd_3883_, 1);
                    crate::leanh::lean_dec(v_unused_3934_);
                    v___x_3899_ = v_snd_3883_;
                    v_isShared_3900_ = v_isSharedCheck_3933_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3897_);
                    crate::leanh::lean_dec(v_snd_3883_);
                    v___x_3899_ = crate::leanh::lean_box(0);
                    v_isShared_3900_ = v_isSharedCheck_3933_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_inheritedTraceOptions_3901_ = crate::leanh::lean_ctor_get(v___y_3863_, 13);
                v___x_3902_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3;
                v___x_3903_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6);
                v___x_3904_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_3901_,
                    v_options_3884_,
                    v___x_3903_,
                );
                if v___x_3904_ == 0 {
                    crate::leanh::lean_del_object(v___x_3899_);
                    crate::leanh::lean_del_object(v___x_3895_);
                    crate::leanh::lean_del_object(v___x_3891_);
                    crate::leanh::lean_dec(v_instName_3813_);
                    v___y_3823_ = v_fst_3897_;
                    v___y_3824_ = v_fst_3889_;
                    v___y_3825_ = v_fst_3893_;
                    state = 1;
                    continue;
                } else {
                    v___x_3905_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8);
                    v___x_3906_ = l_Lean_MessageData_ofName(v_instName_3813_);
                    if v_isShared_3900_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3899_, 7);
                        crate::leanh::lean_ctor_set(v___x_3899_, 1, v___x_3906_);
                        crate::leanh::lean_ctor_set(v___x_3899_, 0, v___x_3905_);
                        v___x_3908_ = v___x_3899_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3932_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3905_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 1, v___x_3906_);
                        v___x_3908_ = v_reuseFailAlloc_3932_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3909_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10);
                if v_isShared_3896_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3895_, 7);
                    crate::leanh::lean_ctor_set(v___x_3895_, 1, v___x_3909_);
                    crate::leanh::lean_ctor_set(v___x_3895_, 0, v___x_3908_);
                    v___x_3911_ = v___x_3895_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 1, v___x_3909_);
                    v___x_3911_ = v_reuseFailAlloc_3931_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                crate::leanh::lean_inc(v_fst_3889_);
                v___x_3912_ = lean_array_to_list(v_fst_3889_);
                v___x_3913_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(v___x_3912_, v___x_3856_);
                v___x_3914_ = l_Lean_MessageData_ofList(v___x_3913_);
                if v_isShared_3892_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3891_, 7);
                    crate::leanh::lean_ctor_set(v___x_3891_, 1, v___x_3914_);
                    crate::leanh::lean_ctor_set(v___x_3891_, 0, v___x_3911_);
                    v___x_3916_ = v___x_3891_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3911_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 1, v___x_3914_);
                    v___x_3916_ = v_reuseFailAlloc_3930_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3917_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12);
                v___x_3918_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3918_, 0, v___x_3916_);
                crate::leanh::lean_ctor_set(v___x_3918_, 1, v___x_3917_);
                v_sz_3919_ = lean_array_size(v_fst_3893_);
                crate::leanh::lean_inc(v_fst_3893_);
                v___x_3920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9(v_sz_3919_, v___x_3879_, v_fst_3893_);
                v___x_3921_ = lean_array_to_list(v___x_3920_);
                v___x_3922_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10(v___x_3921_, v___x_3856_);
                v___x_3923_ = l_Lean_MessageData_ofList(v___x_3922_);
                v___x_3924_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3924_, 0, v___x_3918_);
                crate::leanh::lean_ctor_set(v___x_3924_, 1, v___x_3923_);
                v___x_3925_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14);
                v___x_3926_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3926_, 0, v___x_3924_);
                crate::leanh::lean_ctor_set(v___x_3926_, 1, v___x_3925_);
                v___x_3927_ = (crate::leanh::lean_unbox(v_fst_3897_) as u8);
                if v___x_3927_ == 0 {
                    v___x_3928_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15;
                    v___y_3830_ = v___y_3862_;
                    v___y_3831_ = v___y_3864_;
                    v___y_3832_ = v_fst_3897_;
                    v___y_3833_ = v___x_3902_;
                    v___y_3834_ = v___x_3926_;
                    v___y_3835_ = v___y_3861_;
                    v___y_3836_ = v_fst_3889_;
                    v___y_3837_ = v___y_3863_;
                    v___y_3838_ = v_fst_3893_;
                    v___y_3839_ = v___x_3928_;
                    state = 2;
                    continue;
                } else {
                    v___x_3929_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16;
                    v___y_3830_ = v___y_3862_;
                    v___y_3831_ = v___y_3864_;
                    v___y_3832_ = v_fst_3897_;
                    v___y_3833_ = v___x_3902_;
                    v___y_3834_ = v___x_3926_;
                    v___y_3835_ = v___y_3861_;
                    v___y_3836_ = v_fst_3889_;
                    v___y_3837_ = v___y_3863_;
                    v___y_3838_ = v_fst_3893_;
                    v___y_3839_ = v___x_3929_;
                    state = 2;
                    continue;
                }
            }
            12 => {
                if v_isShared_3942_ == 0 {
                    v___x_3944_ = v___x_3941_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3945_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
                    v___x_3944_ = v_reuseFailAlloc_3945_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3944_;
            }
            14 => {
                v___x_3948_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18);
                v___x_3949_ = l_Lean_MessageData_ofConstName(v_instName_3813_, v___x_3812_);
                v___x_3950_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                crate::leanh::lean_ctor_set(v___x_3950_, 1, v___x_3949_);
                v___x_3951_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20);
                v___x_3952_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3952_, 0, v___x_3950_);
                crate::leanh::lean_ctor_set(v___x_3952_, 1, v___x_3951_);
                v___x_3953_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_3952_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
                v_a_3954_ = crate::leanh::lean_ctor_get(v___x_3953_, 0);
                v_isSharedCheck_3961_ = (!crate::leanh::lean_is_exclusive(v___x_3953_)) as u8;
                if v_isSharedCheck_3961_ == 0 {
                    v___x_3956_ = v___x_3953_;
                    v_isShared_3957_ = v_isSharedCheck_3961_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3954_);
                    crate::leanh::lean_dec(v___x_3953_);
                    v___x_3956_ = crate::leanh::lean_box(0);
                    v_isShared_3957_ = v_isSharedCheck_3961_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3957_ == 0 {
                    v___x_3959_ = v___x_3956_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3960_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
                    v___x_3959_ = v_reuseFailAlloc_3960_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3959_;
            }
            17 => {
                if v_isShared_3968_ == 0 {
                    v___x_3970_ = v___x_3967_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3971_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
                    v___x_3970_ = v_reuseFailAlloc_3971_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3970_;
            }
            19 => {
                if v_isShared_3976_ == 0 {
                    v___x_3978_ = v___x_3975_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3979_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
                    v___x_3978_ = v_reuseFailAlloc_3979_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___boxed(
    mut v_type_3981_: *mut crate::leanh::LeanObject,
    mut v_val_3982_: *mut crate::leanh::LeanObject,
    mut v_levelParams_3983_: *mut crate::leanh::LeanObject,
    mut v_name_3984_: *mut crate::leanh::LeanObject,
    mut v_val_3985_: *mut crate::leanh::LeanObject,
    mut v___x_3986_: *mut crate::leanh::LeanObject,
    mut v_instName_3987_: *mut crate::leanh::LeanObject,
    mut v_a_3988_: *mut crate::leanh::LeanObject,
    mut v_xs_3989_: *mut crate::leanh::LeanObject,
    mut v_body_3990_: *mut crate::leanh::LeanObject,
    mut v___y_3991_: *mut crate::leanh::LeanObject,
    mut v___y_3992_: *mut crate::leanh::LeanObject,
    mut v___y_3993_: *mut crate::leanh::LeanObject,
    mut v___y_3994_: *mut crate::leanh::LeanObject,
    mut v___y_3995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_20080__boxed_3996_: u8 = 0;
    let mut v_res_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_20080__boxed_3996_ = (crate::leanh::lean_unbox(v___x_3986_) as u8);
    v_res_3997_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1(
        v_type_3981_,
        v_val_3982_,
        v_levelParams_3983_,
        v_name_3984_,
        v_val_3985_,
        v___x_20080__boxed_3996_,
        v_instName_3987_,
        v_a_3988_,
        v_xs_3989_,
        v_body_3990_,
        v___y_3991_,
        v___y_3992_,
        v___y_3993_,
        v___y_3994_,
    );
    crate::leanh::lean_dec(v___y_3994_);
    crate::leanh::lean_dec_ref(v___y_3993_);
    crate::leanh::lean_dec(v___y_3992_);
    crate::leanh::lean_dec_ref(v___y_3991_);
    crate::leanh::lean_dec_ref(v_xs_3989_);
    crate::leanh::lean_dec(v_a_3988_);
    crate::leanh::lean_dec_ref(v_val_3985_);
    return v_res_3997_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3998_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3998_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(
    mut v_msg_4003_: *mut crate::leanh::LeanObject,
    mut v___y_4004_: *mut crate::leanh::LeanObject,
    mut v___y_4005_: *mut crate::leanh::LeanObject,
    mut v___y_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v_toFunctor_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4021_: u8 = 0;
    let mut v___f_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4038_: u8 = 0;
    let mut v_toFunctor_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4045_: u8 = 0;
    let mut v___f_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_17799__overap_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4064_: u8 = 0;
    let mut v_unused_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4066_: u8 = 0;
    let mut v_unused_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4070_: u8 = 0;
    let mut v_unused_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4072_: u8 = 0;
    let mut v_unused_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4009_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0_once), _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0);
                v___x_4010_ = l_StateRefT_x27_instMonad___redArg(v___x_4009_);
                v_toApplicative_4011_ = crate::leanh::lean_ctor_get(v___x_4010_, 0);
                v_isSharedCheck_4072_ = (!crate::leanh::lean_is_exclusive(v___x_4010_)) as u8;
                if v_isSharedCheck_4072_ == 0 {
                    v_unused_4073_ = crate::leanh::lean_ctor_get(v___x_4010_, 1);
                    crate::leanh::lean_dec(v_unused_4073_);
                    v___x_4013_ = v___x_4010_;
                    v_isShared_4014_ = v_isSharedCheck_4072_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4011_);
                    crate::leanh::lean_dec(v___x_4010_);
                    v___x_4013_ = crate::leanh::lean_box(0);
                    v_isShared_4014_ = v_isSharedCheck_4072_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4015_ = crate::leanh::lean_ctor_get(v_toApplicative_4011_, 0);
                v_toSeq_4016_ = crate::leanh::lean_ctor_get(v_toApplicative_4011_, 2);
                v_toSeqLeft_4017_ = crate::leanh::lean_ctor_get(v_toApplicative_4011_, 3);
                v_toSeqRight_4018_ = crate::leanh::lean_ctor_get(v_toApplicative_4011_, 4);
                v_isSharedCheck_4070_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4011_)) as u8;
                if v_isSharedCheck_4070_ == 0 {
                    v_unused_4071_ = crate::leanh::lean_ctor_get(v_toApplicative_4011_, 1);
                    crate::leanh::lean_dec(v_unused_4071_);
                    v___x_4020_ = v_toApplicative_4011_;
                    v_isShared_4021_ = v_isSharedCheck_4070_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4018_);
                    crate::leanh::lean_inc(v_toSeqLeft_4017_);
                    crate::leanh::lean_inc(v_toSeq_4016_);
                    crate::leanh::lean_inc(v_toFunctor_4015_);
                    crate::leanh::lean_dec(v_toApplicative_4011_);
                    v___x_4020_ = crate::leanh::lean_box(0);
                    v_isShared_4021_ = v_isSharedCheck_4070_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4022_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1;
                v___f_4023_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_4015_);
                v___f_4024_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4024_, 0, v_toFunctor_4015_);
                v___f_4025_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4025_, 0, v_toFunctor_4015_);
                v___x_4026_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4026_, 0, v___f_4024_);
                crate::leanh::lean_ctor_set(v___x_4026_, 1, v___f_4025_);
                v___f_4027_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4027_, 0, v_toSeqRight_4018_);
                v___f_4028_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4028_, 0, v_toSeqLeft_4017_);
                v___f_4029_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4029_, 0, v_toSeq_4016_);
                if v_isShared_4021_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4020_, 4, v___f_4027_);
                    crate::leanh::lean_ctor_set(v___x_4020_, 3, v___f_4028_);
                    crate::leanh::lean_ctor_set(v___x_4020_, 2, v___f_4029_);
                    crate::leanh::lean_ctor_set(v___x_4020_, 1, v___f_4022_);
                    crate::leanh::lean_ctor_set(v___x_4020_, 0, v___x_4026_);
                    v___x_4031_ = v___x_4020_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4069_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4026_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 1, v___f_4022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 2, v___f_4029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 3, v___f_4028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 4, v___f_4027_);
                    v___x_4031_ = v_reuseFailAlloc_4069_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4013_, 1, v___f_4023_);
                    crate::leanh::lean_ctor_set(v___x_4013_, 0, v___x_4031_);
                    v___x_4033_ = v___x_4013_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4068_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 1, v___f_4023_);
                    v___x_4033_ = v_reuseFailAlloc_4068_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4034_ = l_StateRefT_x27_instMonad___redArg(v___x_4033_);
                v_toApplicative_4035_ = crate::leanh::lean_ctor_get(v___x_4034_, 0);
                v_isSharedCheck_4066_ = (!crate::leanh::lean_is_exclusive(v___x_4034_)) as u8;
                if v_isSharedCheck_4066_ == 0 {
                    v_unused_4067_ = crate::leanh::lean_ctor_get(v___x_4034_, 1);
                    crate::leanh::lean_dec(v_unused_4067_);
                    v___x_4037_ = v___x_4034_;
                    v_isShared_4038_ = v_isSharedCheck_4066_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4035_);
                    crate::leanh::lean_dec(v___x_4034_);
                    v___x_4037_ = crate::leanh::lean_box(0);
                    v_isShared_4038_ = v_isSharedCheck_4066_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4039_ = crate::leanh::lean_ctor_get(v_toApplicative_4035_, 0);
                v_toSeq_4040_ = crate::leanh::lean_ctor_get(v_toApplicative_4035_, 2);
                v_toSeqLeft_4041_ = crate::leanh::lean_ctor_get(v_toApplicative_4035_, 3);
                v_toSeqRight_4042_ = crate::leanh::lean_ctor_get(v_toApplicative_4035_, 4);
                v_isSharedCheck_4064_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4035_)) as u8;
                if v_isSharedCheck_4064_ == 0 {
                    v_unused_4065_ = crate::leanh::lean_ctor_get(v_toApplicative_4035_, 1);
                    crate::leanh::lean_dec(v_unused_4065_);
                    v___x_4044_ = v_toApplicative_4035_;
                    v_isShared_4045_ = v_isSharedCheck_4064_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4042_);
                    crate::leanh::lean_inc(v_toSeqLeft_4041_);
                    crate::leanh::lean_inc(v_toSeq_4040_);
                    crate::leanh::lean_inc(v_toFunctor_4039_);
                    crate::leanh::lean_dec(v_toApplicative_4035_);
                    v___x_4044_ = crate::leanh::lean_box(0);
                    v_isShared_4045_ = v_isSharedCheck_4064_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4046_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3;
                v___f_4047_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_4039_);
                v___f_4048_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4048_, 0, v_toFunctor_4039_);
                v___f_4049_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4049_, 0, v_toFunctor_4039_);
                v___x_4050_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4050_, 0, v___f_4048_);
                crate::leanh::lean_ctor_set(v___x_4050_, 1, v___f_4049_);
                v___f_4051_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4051_, 0, v_toSeqRight_4042_);
                v___f_4052_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4052_, 0, v_toSeqLeft_4041_);
                v___f_4053_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4053_, 0, v_toSeq_4040_);
                if v_isShared_4045_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4044_, 4, v___f_4051_);
                    crate::leanh::lean_ctor_set(v___x_4044_, 3, v___f_4052_);
                    crate::leanh::lean_ctor_set(v___x_4044_, 2, v___f_4053_);
                    crate::leanh::lean_ctor_set(v___x_4044_, 1, v___f_4046_);
                    crate::leanh::lean_ctor_set(v___x_4044_, 0, v___x_4050_);
                    v___x_4055_ = v___x_4044_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 1, v___f_4046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 2, v___f_4053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 3, v___f_4052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 4, v___f_4051_);
                    v___x_4055_ = v_reuseFailAlloc_4063_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4037_, 1, v___f_4047_);
                    crate::leanh::lean_ctor_set(v___x_4037_, 0, v___x_4055_);
                    v___x_4057_ = v___x_4037_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___f_4047_);
                    v___x_4057_ = v_reuseFailAlloc_4062_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4058_ = crate::leanh::lean_box(0);
                v___x_4059_ = l_instInhabitedOfMonad___redArg(v___x_4057_, v___x_4058_);
                v___x_17799__overap_4060_ = lean_panic_fn_borrowed(v___x_4059_, v_msg_4003_);
                crate::leanh::lean_dec(v___x_4059_);
                crate::leanh::lean_inc(v___y_4007_);
                crate::leanh::lean_inc_ref(v___y_4006_);
                crate::leanh::lean_inc(v___y_4005_);
                crate::leanh::lean_inc_ref(v___y_4004_);
                v___x_4061_ = crate::leanh::lean_apply_5(
                    v___x_17799__overap_4060_,
                    v___y_4004_,
                    v___y_4005_,
                    v___y_4006_,
                    v___y_4007_,
                    crate::leanh::lean_box(0),
                );
                return v___x_4061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___boxed(
    mut v_msg_4074_: *mut crate::leanh::LeanObject,
    mut v___y_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
    mut v___y_4077_: *mut crate::leanh::LeanObject,
    mut v___y_4078_: *mut crate::leanh::LeanObject,
    mut v___y_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4080_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(v_msg_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
    crate::leanh::lean_dec(v___y_4078_);
    crate::leanh::lean_dec_ref(v___y_4077_);
    crate::leanh::lean_dec(v___y_4076_);
    crate::leanh::lean_dec_ref(v___y_4075_);
    return v_res_4080_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4082_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0;
    v___x_4083_ = l_Lean_stringToMessageData(v___x_4082_);
    return v___x_4083_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4085_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2;
    v___x_4086_ = l_Lean_stringToMessageData(v___x_4085_);
    return v___x_4086_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4090_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6;
    v___x_4091_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_4092_ = crate::leanh::lean_unsigned_to_nat(115);
    v___x_4093_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__5;
    v___x_4094_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__4;
    v___x_4095_ = l_mkPanicMessageWithDecl(
        v___x_4094_,
        v___x_4093_,
        v___x_4092_,
        v___x_4091_,
        v___x_4090_,
    );
    return v___x_4095_;
}
pub unsafe fn l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0(
    mut v_constName_4096_: *mut crate::leanh::LeanObject,
    mut v___y_4097_: *mut crate::leanh::LeanObject,
    mut v___y_4098_: *mut crate::leanh::LeanObject,
    mut v___y_4099_: *mut crate::leanh::LeanObject,
    mut v___y_4100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: u8 = 0;
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: u8 = 0;
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4115_: u8 = 0;
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4120_: u8 = 0;
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4124_: u8 = 0;
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4130_: u8 = 0;
    let mut v_val_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4135_: u8 = 0;
    let mut v_a_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4139_: u8 = 0;
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4143_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4110_ = lean_st_ref_get(v___y_4100_);
                v_env_4111_ = crate::leanh::lean_ctor_get(v___x_4110_, 0);
                crate::leanh::lean_inc_ref(v_env_4111_);
                crate::leanh::lean_dec(v___x_4110_);
                v___x_4112_ = 0;
                crate::leanh::lean_inc(v_constName_4096_);
                v___x_4113_ =
                    l_Lean_Environment_findAsync_x3f(v_env_4111_, v_constName_4096_, v___x_4112_);
                if crate::leanh::lean_obj_tag(v___x_4113_) == 1 {
                    v_val_4114_ = crate::leanh::lean_ctor_get(v___x_4113_, 0);
                    crate::leanh::lean_inc(v_val_4114_);
                    crate::leanh::lean_dec_ref_known(v___x_4113_, 1);
                    v_kind_4115_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_4114_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_4115_ == 0 {
                        v___x_4116_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4114_);
                        if crate::leanh::lean_obj_tag(v___x_4116_) == 1 {
                            crate::leanh::lean_dec(v_constName_4096_);
                            v_val_4117_ = crate::leanh::lean_ctor_get(v___x_4116_, 0);
                            v_isSharedCheck_4124_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4116_)) as u8;
                            if v_isSharedCheck_4124_ == 0 {
                                v___x_4119_ = v___x_4116_;
                                v_isShared_4120_ = v_isSharedCheck_4124_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_4117_);
                                crate::leanh::lean_dec(v___x_4116_);
                                v___x_4119_ = crate::leanh::lean_box(0);
                                v_isShared_4120_ = v_isSharedCheck_4124_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4116_);
                            v___x_4125_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7_once), _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7);
                            v___x_4126_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(v___x_4125_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
                            if crate::leanh::lean_obj_tag(v___x_4126_) == 0 {
                                v_a_4127_ = crate::leanh::lean_ctor_get(v___x_4126_, 0);
                                v_isSharedCheck_4135_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4126_)) as u8;
                                if v_isSharedCheck_4135_ == 0 {
                                    v___x_4129_ = v___x_4126_;
                                    v_isShared_4130_ = v_isSharedCheck_4135_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4127_);
                                    crate::leanh::lean_dec(v___x_4126_);
                                    v___x_4129_ = crate::leanh::lean_box(0);
                                    v_isShared_4130_ = v_isSharedCheck_4135_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_4096_);
                                v_a_4136_ = crate::leanh::lean_ctor_get(v___x_4126_, 0);
                                v_isSharedCheck_4143_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4126_)) as u8;
                                if v_isSharedCheck_4143_ == 0 {
                                    v___x_4138_ = v___x_4126_;
                                    v_isShared_4139_ = v_isSharedCheck_4143_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4136_);
                                    crate::leanh::lean_dec(v___x_4126_);
                                    v___x_4138_ = crate::leanh::lean_box(0);
                                    v_isShared_4139_ = v_isSharedCheck_4143_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4114_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4113_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4103_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once), _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1);
                v___x_4104_ = 0;
                v___x_4105_ = l_Lean_MessageData_ofConstName(v_constName_4096_, v___x_4104_);
                v___x_4106_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4106_, 0, v___x_4103_);
                crate::leanh::lean_ctor_set(v___x_4106_, 1, v___x_4105_);
                v___x_4107_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3_once), _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3);
                v___x_4108_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4108_, 0, v___x_4106_);
                crate::leanh::lean_ctor_set(v___x_4108_, 1, v___x_4107_);
                v___x_4109_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_4108_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
                return v___x_4109_;
            }
            2 => {
                if v_isShared_4120_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4119_, 0);
                    v___x_4122_ = v___x_4119_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4123_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_val_4117_);
                    v___x_4122_ = v_reuseFailAlloc_4123_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4122_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_4127_) == 0 {
                    crate::leanh::lean_del_object(v___x_4129_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_4096_);
                    v_val_4131_ = crate::leanh::lean_ctor_get(v_a_4127_, 0);
                    crate::leanh::lean_inc(v_val_4131_);
                    crate::leanh::lean_dec_ref_known(v_a_4127_, 1);
                    if v_isShared_4130_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4129_, 0, v_val_4131_);
                        v___x_4133_ = v___x_4129_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_val_4131_);
                        v___x_4133_ = v_reuseFailAlloc_4134_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4133_;
            }
            6 => {
                if v_isShared_4139_ == 0 {
                    v___x_4141_ = v___x_4138_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4142_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
                    v___x_4141_ = v_reuseFailAlloc_4142_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___boxed(
    mut v_constName_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
    mut v___y_4148_: *mut crate::leanh::LeanObject,
    mut v___y_4149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4150_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0(v_constName_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
    crate::leanh::lean_dec(v___y_4148_);
    crate::leanh::lean_dec_ref(v___y_4147_);
    crate::leanh::lean_dec(v___y_4146_);
    crate::leanh::lean_dec_ref(v___y_4145_);
    return v_res_4150_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4153_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__1;
    v___x_4154_ = l_Lean_stringToMessageData(v___x_4153_);
    return v___x_4154_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__3;
    v___x_4157_ = l_Lean_stringToMessageData(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__5;
    v___x_4160_ = l_Lean_stringToMessageData(v___x_4159_);
    return v___x_4160_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4162_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__7;
    v___x_4163_ = l_Lean_stringToMessageData(v___x_4162_);
    return v___x_4163_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(
    mut v_instName_4164_: *mut crate::leanh::LeanObject,
    mut v_a_4165_: *mut crate::leanh::LeanObject,
    mut v_a_4166_: *mut crate::leanh::LeanObject,
    mut v_a_4167_: *mut crate::leanh::LeanObject,
    mut v_a_4168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: u8 = 0;
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4200_: u8 = 0;
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: u8 = 0;
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4220_: u8 = 0;
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4224_: u8 = 0;
    let mut v_a_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4228_: u8 = 0;
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4232_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_instName_4164_);
                v___x_4170_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0(v_instName_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
                if crate::leanh::lean_obj_tag(v___x_4170_) == 0 {
                    v_a_4171_ = crate::leanh::lean_ctor_get(v___x_4170_, 0);
                    crate::leanh::lean_inc(v_a_4171_);
                    crate::leanh::lean_dec_ref_known(v___x_4170_, 1);
                    v_toConstantVal_4172_ = crate::leanh::lean_ctor_get(v_a_4171_, 0);
                    crate::leanh::lean_inc_ref(v_toConstantVal_4172_);
                    v_value_4173_ = crate::leanh::lean_ctor_get(v_a_4171_, 1);
                    crate::leanh::lean_inc_ref(v_value_4173_);
                    crate::leanh::lean_dec(v_a_4171_);
                    v_name_4174_ = crate::leanh::lean_ctor_get(v_toConstantVal_4172_, 0);
                    crate::leanh::lean_inc(v_name_4174_);
                    v_levelParams_4175_ = crate::leanh::lean_ctor_get(v_toConstantVal_4172_, 1);
                    crate::leanh::lean_inc(v_levelParams_4175_);
                    v_type_4176_ = crate::leanh::lean_ctor_get(v_toConstantVal_4172_, 2);
                    crate::leanh::lean_inc_ref_n(v_type_4176_, 2);
                    crate::leanh::lean_dec_ref(v_toConstantVal_4172_);
                    v___x_4177_ = l_Lean_Meta_isClass_x3f(
                        v_type_4176_,
                        v_a_4165_,
                        v_a_4166_,
                        v_a_4167_,
                        v_a_4168_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4177_) == 0 {
                        v_a_4178_ = crate::leanh::lean_ctor_get(v___x_4177_, 0);
                        crate::leanh::lean_inc(v_a_4178_);
                        crate::leanh::lean_dec_ref_known(v___x_4177_, 1);
                        if crate::leanh::lean_obj_tag(v_a_4178_) == 1 {
                            v_val_4179_ = crate::leanh::lean_ctor_get(v_a_4178_, 0);
                            crate::leanh::lean_inc(v_val_4179_);
                            crate::leanh::lean_dec_ref_known(v_a_4178_, 1);
                            v___f_4180_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__0;
                            v___x_4181_ = 0;
                            crate::leanh::lean_inc_ref(v_type_4176_);
                            v___x_4182_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(v_type_4176_, v___f_4180_, v___x_4181_, v___x_4181_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
                            if crate::leanh::lean_obj_tag(v___x_4182_) == 0 {
                                v_a_4183_ = crate::leanh::lean_ctor_get(v___x_4182_, 0);
                                crate::leanh::lean_inc(v_a_4183_);
                                crate::leanh::lean_dec_ref_known(v___x_4182_, 1);
                                v___x_4184_ = lean_st_ref_get(v_a_4168_);
                                v_env_4185_ = crate::leanh::lean_ctor_get(v___x_4184_, 0);
                                crate::leanh::lean_inc_ref(v_env_4185_);
                                crate::leanh::lean_dec(v___x_4184_);
                                crate::leanh::lean_inc(v_val_4179_);
                                v___x_4186_ = l_Lean_getStructureInfo_x3f(v_env_4185_, v_val_4179_);
                                if crate::leanh::lean_obj_tag(v___x_4186_) == 1 {
                                    v_val_4187_ = crate::leanh::lean_ctor_get(v___x_4186_, 0);
                                    crate::leanh::lean_inc(v_val_4187_);
                                    crate::leanh::lean_dec_ref_known(v___x_4186_, 1);
                                    v___x_4188_ = crate::leanh::lean_box((v___x_4181_) as usize);
                                    v___f_4189_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___boxed as *mut core::ffi::c_void, 15, 8);
                                    crate::leanh::lean_closure_set(v___f_4189_, 0, v_type_4176_);
                                    crate::leanh::lean_closure_set(v___f_4189_, 1, v_val_4179_);
                                    crate::leanh::lean_closure_set(
                                        v___f_4189_,
                                        2,
                                        v_levelParams_4175_,
                                    );
                                    crate::leanh::lean_closure_set(v___f_4189_, 3, v_name_4174_);
                                    crate::leanh::lean_closure_set(v___f_4189_, 4, v_val_4187_);
                                    crate::leanh::lean_closure_set(v___f_4189_, 5, v___x_4188_);
                                    crate::leanh::lean_closure_set(
                                        v___f_4189_,
                                        6,
                                        v_instName_4164_,
                                    );
                                    crate::leanh::lean_closure_set(v___f_4189_, 7, v_a_4183_);
                                    v___x_4190_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(v_value_4173_, v___f_4189_, v___x_4181_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
                                    return v___x_4190_;
                                } else {
                                    crate::leanh::lean_dec(v___x_4186_);
                                    crate::leanh::lean_dec(v_a_4183_);
                                    crate::leanh::lean_dec_ref(v_type_4176_);
                                    crate::leanh::lean_dec(v_levelParams_4175_);
                                    crate::leanh::lean_dec(v_name_4174_);
                                    crate::leanh::lean_dec_ref(v_value_4173_);
                                    crate::leanh::lean_dec(v_instName_4164_);
                                    v___x_4191_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once), _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1);
                                    v___x_4192_ =
                                        l_Lean_MessageData_ofConstName(v_val_4179_, v___x_4181_);
                                    v___x_4193_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4193_, 0, v___x_4191_);
                                    crate::leanh::lean_ctor_set(v___x_4193_, 1, v___x_4192_);
                                    v___x_4194_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2);
                                    v___x_4195_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4195_, 0, v___x_4193_);
                                    crate::leanh::lean_ctor_set(v___x_4195_, 1, v___x_4194_);
                                    v___x_4196_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_4195_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
                                    return v___x_4196_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_4179_);
                                crate::leanh::lean_dec_ref(v_type_4176_);
                                crate::leanh::lean_dec(v_levelParams_4175_);
                                crate::leanh::lean_dec(v_name_4174_);
                                crate::leanh::lean_dec_ref(v_value_4173_);
                                crate::leanh::lean_dec(v_instName_4164_);
                                v_a_4197_ = crate::leanh::lean_ctor_get(v___x_4182_, 0);
                                v_isSharedCheck_4204_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4182_)) as u8;
                                if v_isSharedCheck_4204_ == 0 {
                                    v___x_4199_ = v___x_4182_;
                                    v_isShared_4200_ = v_isSharedCheck_4204_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4197_);
                                    crate::leanh::lean_dec(v___x_4182_);
                                    v___x_4199_ = crate::leanh::lean_box(0);
                                    v_isShared_4200_ = v_isSharedCheck_4204_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4178_);
                            crate::leanh::lean_dec(v_levelParams_4175_);
                            crate::leanh::lean_dec(v_name_4174_);
                            crate::leanh::lean_dec_ref(v_value_4173_);
                            v___x_4205_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4);
                            v___x_4206_ = 0;
                            v___x_4207_ =
                                l_Lean_MessageData_ofConstName(v_instName_4164_, v___x_4206_);
                            v___x_4208_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4208_, 0, v___x_4205_);
                            crate::leanh::lean_ctor_set(v___x_4208_, 1, v___x_4207_);
                            v___x_4209_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6);
                            v___x_4210_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4210_, 0, v___x_4208_);
                            crate::leanh::lean_ctor_set(v___x_4210_, 1, v___x_4209_);
                            v___x_4211_ = crate::leanh::lean_unsigned_to_nat(30);
                            v___x_4212_ = l_Lean_inlineExpr(v_type_4176_, v___x_4211_);
                            v___x_4213_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4213_, 0, v___x_4210_);
                            crate::leanh::lean_ctor_set(v___x_4213_, 1, v___x_4212_);
                            v___x_4214_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8);
                            v___x_4215_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4215_, 0, v___x_4213_);
                            crate::leanh::lean_ctor_set(v___x_4215_, 1, v___x_4214_);
                            v___x_4216_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_4215_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
                            return v___x_4216_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_4176_);
                        crate::leanh::lean_dec(v_levelParams_4175_);
                        crate::leanh::lean_dec(v_name_4174_);
                        crate::leanh::lean_dec_ref(v_value_4173_);
                        crate::leanh::lean_dec(v_instName_4164_);
                        v_a_4217_ = crate::leanh::lean_ctor_get(v___x_4177_, 0);
                        v_isSharedCheck_4224_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4177_)) as u8;
                        if v_isSharedCheck_4224_ == 0 {
                            v___x_4219_ = v___x_4177_;
                            v_isShared_4220_ = v_isSharedCheck_4224_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4217_);
                            crate::leanh::lean_dec(v___x_4177_);
                            v___x_4219_ = crate::leanh::lean_box(0);
                            v_isShared_4220_ = v_isSharedCheck_4224_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_instName_4164_);
                    v_a_4225_ = crate::leanh::lean_ctor_get(v___x_4170_, 0);
                    v_isSharedCheck_4232_ = (!crate::leanh::lean_is_exclusive(v___x_4170_)) as u8;
                    if v_isSharedCheck_4232_ == 0 {
                        v___x_4227_ = v___x_4170_;
                        v_isShared_4228_ = v_isSharedCheck_4232_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4225_);
                        crate::leanh::lean_dec(v___x_4170_);
                        v___x_4227_ = crate::leanh::lean_box(0);
                        v_isShared_4228_ = v_isSharedCheck_4232_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4200_ == 0 {
                    v___x_4202_ = v___x_4199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4203_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
                    v___x_4202_ = v_reuseFailAlloc_4203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4202_;
            }
            3 => {
                if v_isShared_4220_ == 0 {
                    v___x_4222_ = v___x_4219_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4223_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
                    v___x_4222_ = v_reuseFailAlloc_4223_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4222_;
            }
            5 => {
                if v_isShared_4228_ == 0 {
                    v___x_4230_ = v___x_4227_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4231_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
                    v___x_4230_ = v_reuseFailAlloc_4231_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___boxed(
    mut v_instName_4233_: *mut crate::leanh::LeanObject,
    mut v_a_4234_: *mut crate::leanh::LeanObject,
    mut v_a_4235_: *mut crate::leanh::LeanObject,
    mut v_a_4236_: *mut crate::leanh::LeanObject,
    mut v_a_4237_: *mut crate::leanh::LeanObject,
    mut v_a_4238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4239_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(
        v_instName_4233_,
        v_a_4234_,
        v_a_4235_,
        v_a_4236_,
        v_a_4237_,
    );
    crate::leanh::lean_dec(v_a_4237_);
    crate::leanh::lean_dec_ref(v_a_4236_);
    crate::leanh::lean_dec(v_a_4235_);
    crate::leanh::lean_dec_ref(v_a_4234_);
    return v_res_4239_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3(
    mut v_00_u03b1_4240_: *mut crate::leanh::LeanObject,
    mut v_msg_4241_: *mut crate::leanh::LeanObject,
    mut v___y_4242_: *mut crate::leanh::LeanObject,
    mut v___y_4243_: *mut crate::leanh::LeanObject,
    mut v___y_4244_: *mut crate::leanh::LeanObject,
    mut v___y_4245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4247_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v_msg_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
    return v___x_4247_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___boxed(
    mut v_00_u03b1_4248_: *mut crate::leanh::LeanObject,
    mut v_msg_4249_: *mut crate::leanh::LeanObject,
    mut v___y_4250_: *mut crate::leanh::LeanObject,
    mut v___y_4251_: *mut crate::leanh::LeanObject,
    mut v___y_4252_: *mut crate::leanh::LeanObject,
    mut v___y_4253_: *mut crate::leanh::LeanObject,
    mut v___y_4254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4255_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3(v_00_u03b1_4248_, v_msg_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
    crate::leanh::lean_dec(v___y_4253_);
    crate::leanh::lean_dec_ref(v___y_4252_);
    crate::leanh::lean_dec(v___y_4251_);
    crate::leanh::lean_dec_ref(v___y_4250_);
    return v_res_4255_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4(
    mut v_xs_4256_: *mut crate::leanh::LeanObject,
    mut v_ys_4257_: *mut crate::leanh::LeanObject,
    mut v_hsz_4258_: *mut crate::leanh::LeanObject,
    mut v_x_4259_: *mut crate::leanh::LeanObject,
    mut v_x_4260_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4261_: u8 = 0;
    v___x_4261_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(v_xs_4256_, v_ys_4257_, v_x_4259_);
    return v___x_4261_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___boxed(
    mut v_xs_4262_: *mut crate::leanh::LeanObject,
    mut v_ys_4263_: *mut crate::leanh::LeanObject,
    mut v_hsz_4264_: *mut crate::leanh::LeanObject,
    mut v_x_4265_: *mut crate::leanh::LeanObject,
    mut v_x_4266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4267_: u8 = 0;
    let mut v_r_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4267_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4(v_xs_4262_, v_ys_4263_, v_hsz_4264_, v_x_4265_, v_x_4266_);
    crate::leanh::lean_dec_ref(v_ys_4263_);
    crate::leanh::lean_dec_ref(v_xs_4262_);
    v_r_4268_ = crate::leanh::lean_box((v_res_4267_) as usize);
    return v_r_4268_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1() -> u64
{
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: u64 = 0;
    v___x_4280_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0;
    v___x_4281_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4280_);
    return v___x_4281_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4282_: u64 = 0;
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4282_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1,
    );
    v___x_4283_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0;
    v___x_4284_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_4284_, 0, v___x_4283_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_4284_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4282_,
    );
    return v___x_4284_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4285_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4285_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3,
    );
    v___x_4287_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4287_, 0, v___x_4286_);
    return v___x_4287_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4288_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4289_ = lean_mk_empty_array_with_capacity(v___x_4288_);
    v___x_4290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4290_, 0, v___x_4289_);
    return v___x_4290_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4291_: usize = 0;
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4291_ = 5usize;
    v___x_4292_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4293_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4294_ = lean_mk_empty_array_with_capacity(v___x_4293_);
    v___x_4295_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5,
    );
    v___x_4296_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4296_, 0, v___x_4295_);
    crate::leanh::lean_ctor_set(v___x_4296_, 1, v___x_4294_);
    crate::leanh::lean_ctor_set(v___x_4296_, 2, v___x_4292_);
    crate::leanh::lean_ctor_set(v___x_4296_, 3, v___x_4292_);
    crate::leanh::lean_ctor_set_usize(v___x_4296_, 4, v___x_4291_);
    return v___x_4296_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4297_ = crate::leanh::lean_box(1);
    v___x_4298_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6,
    );
    v___x_4299_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4,
    );
    v___x_4300_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4300_, 0, v___x_4299_);
    crate::leanh::lean_ctor_set(v___x_4300_, 1, v___x_4298_);
    crate::leanh::lean_ctor_set(v___x_4300_, 2, v___x_4297_);
    return v___x_4300_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4303_: u8 = 0;
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: u8 = 0;
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4303_ = 1;
    v___x_4304_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4305_ = crate::leanh::lean_box(0);
    v___x_4306_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8;
    v___x_4307_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7,
    );
    v___x_4308_ = crate::leanh::lean_box(1);
    v___x_4309_ = 0;
    v___x_4310_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2,
    );
    v___x_4311_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
    crate::leanh::lean_ctor_set(v___x_4311_, 0, v___x_4310_);
    crate::leanh::lean_ctor_set(v___x_4311_, 1, v___x_4308_);
    crate::leanh::lean_ctor_set(v___x_4311_, 2, v___x_4307_);
    crate::leanh::lean_ctor_set(v___x_4311_, 3, v___x_4306_);
    crate::leanh::lean_ctor_set(v___x_4311_, 4, v___x_4305_);
    crate::leanh::lean_ctor_set(v___x_4311_, 5, v___x_4304_);
    crate::leanh::lean_ctor_set(v___x_4311_, 6, v___x_4305_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4311_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v___x_4309_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4311_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
        v___x_4309_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4311_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
        v___x_4309_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4311_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
        v___x_4303_,
    );
    return v___x_4311_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4312_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4,
    );
    v___x_4313_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4314_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4314_, 0, v___x_4313_);
    crate::leanh::lean_ctor_set(v___x_4314_, 1, v___x_4313_);
    crate::leanh::lean_ctor_set(v___x_4314_, 2, v___x_4313_);
    crate::leanh::lean_ctor_set(v___x_4314_, 3, v___x_4313_);
    crate::leanh::lean_ctor_set(v___x_4314_, 4, v___x_4312_);
    crate::leanh::lean_ctor_set(v___x_4314_, 5, v___x_4312_);
    crate::leanh::lean_ctor_set(v___x_4314_, 6, v___x_4312_);
    crate::leanh::lean_ctor_set(v___x_4314_, 7, v___x_4312_);
    crate::leanh::lean_ctor_set(v___x_4314_, 8, v___x_4312_);
    crate::leanh::lean_ctor_set(v___x_4314_, 9, v___x_4312_);
    return v___x_4314_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4315_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4,
    );
    v___x_4316_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4316_, 0, v___x_4315_);
    crate::leanh::lean_ctor_set(v___x_4316_, 1, v___x_4315_);
    crate::leanh::lean_ctor_set(v___x_4316_, 2, v___x_4315_);
    crate::leanh::lean_ctor_set(v___x_4316_, 3, v___x_4315_);
    crate::leanh::lean_ctor_set(v___x_4316_, 4, v___x_4315_);
    crate::leanh::lean_ctor_set(v___x_4316_, 5, v___x_4315_);
    return v___x_4316_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4317_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4,
    );
    v___x_4318_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4318_, 0, v___x_4317_);
    crate::leanh::lean_ctor_set(v___x_4318_, 1, v___x_4317_);
    crate::leanh::lean_ctor_set(v___x_4318_, 2, v___x_4317_);
    crate::leanh::lean_ctor_set(v___x_4318_, 3, v___x_4317_);
    crate::leanh::lean_ctor_set(v___x_4318_, 4, v___x_4317_);
    return v___x_4318_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4319_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12,
    );
    v___x_4320_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6,
    );
    v___x_4321_ = crate::leanh::lean_box(1);
    v___x_4322_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11,
    );
    v___x_4323_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10,
    );
    v___x_4324_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4324_, 0, v___x_4323_);
    crate::leanh::lean_ctor_set(v___x_4324_, 1, v___x_4322_);
    crate::leanh::lean_ctor_set(v___x_4324_, 2, v___x_4321_);
    crate::leanh::lean_ctor_set(v___x_4324_, 3, v___x_4320_);
    crate::leanh::lean_ctor_set(v___x_4324_, 4, v___x_4319_);
    return v___x_4324_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(
    mut v_instName_4325_: *mut crate::leanh::LeanObject,
    mut v_a_4326_: *mut crate::leanh::LeanObject,
    mut v_a_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clsName_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_privateSpecs_4332_: u8 = 0;
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4345_: u8 = 0;
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4349_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4335_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9);
                v___x_4336_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13);
                v___x_4337_ = lean_st_mk_ref(v___x_4336_);
                v___x_4338_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(
                    v_instName_4325_,
                    v___x_4335_,
                    v___x_4337_,
                    v_a_4326_,
                    v_a_4327_,
                );
                if crate::leanh::lean_obj_tag(v___x_4338_) == 0 {
                    v_a_4339_ = crate::leanh::lean_ctor_get(v___x_4338_, 0);
                    crate::leanh::lean_inc(v_a_4339_);
                    crate::leanh::lean_dec_ref_known(v___x_4338_, 1);
                    v___x_4340_ = lean_st_ref_get(v___x_4337_);
                    crate::leanh::lean_dec(v___x_4337_);
                    crate::leanh::lean_dec(v___x_4340_);
                    v_a_4330_ = v_a_4339_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4337_);
                    if crate::leanh::lean_obj_tag(v___x_4338_) == 0 {
                        v_a_4341_ = crate::leanh::lean_ctor_get(v___x_4338_, 0);
                        crate::leanh::lean_inc(v_a_4341_);
                        crate::leanh::lean_dec_ref_known(v___x_4338_, 1);
                        v_a_4330_ = v_a_4341_;
                        state = 1;
                        continue;
                    } else {
                        v_a_4342_ = crate::leanh::lean_ctor_get(v___x_4338_, 0);
                        v_isSharedCheck_4349_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4338_)) as u8;
                        if v_isSharedCheck_4349_ == 0 {
                            v___x_4344_ = v___x_4338_;
                            v_isShared_4345_ = v_isSharedCheck_4349_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4342_);
                            crate::leanh::lean_dec(v___x_4338_);
                            v___x_4344_ = crate::leanh::lean_box(0);
                            v_isShared_4345_ = v_isSharedCheck_4349_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_clsName_4331_ = crate::leanh::lean_ctor_get(v_a_4330_, 0);
                crate::leanh::lean_inc(v_clsName_4331_);
                v_privateSpecs_4332_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4330_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_a_4330_);
                v___x_4333_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4333_, 0, v_clsName_4331_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4333_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_privateSpecs_4332_,
                );
                v___x_4334_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4334_, 0, v___x_4333_);
                return v___x_4334_;
            }
            2 => {
                if v_isShared_4345_ == 0 {
                    v___x_4347_ = v___x_4344_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4348_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
                    v___x_4347_ = v_reuseFailAlloc_4348_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4347_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___boxed(
    mut v_instName_4350_: *mut crate::leanh::LeanObject,
    mut v_a_4351_: *mut crate::leanh::LeanObject,
    mut v_a_4352_: *mut crate::leanh::LeanObject,
    mut v_a_4353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4354_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(
        v_instName_4350_,
        v_a_4351_,
        v_a_4352_,
    );
    crate::leanh::lean_dec(v_a_4352_);
    crate::leanh::lean_dec_ref(v_a_4351_);
    return v_res_4354_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getParam(
    mut v_instName_4355_: *mut crate::leanh::LeanObject,
    mut v___stx_4356_: *mut crate::leanh::LeanObject,
    mut v_a_4357_: *mut crate::leanh::LeanObject,
    mut v_a_4358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4360_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(
        v_instName_4355_,
        v_a_4357_,
        v_a_4358_,
    );
    return v___x_4360_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___boxed(
    mut v_instName_4361_: *mut crate::leanh::LeanObject,
    mut v___stx_4362_: *mut crate::leanh::LeanObject,
    mut v_a_4363_: *mut crate::leanh::LeanObject,
    mut v_a_4364_: *mut crate::leanh::LeanObject,
    mut v_a_4365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4366_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam(
        v_instName_4361_,
        v___stx_4362_,
        v_a_4363_,
        v_a_4364_,
    );
    crate::leanh::lean_dec(v_a_4364_);
    crate::leanh::lean_dec_ref(v_a_4363_);
    crate::leanh::lean_dec(v___stx_4362_);
    return v_res_4366_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(
    mut v_x_4367_: *mut crate::leanh::LeanObject,
    mut v_x_4368_: *mut crate::leanh::LeanObject,
    mut v_x_4369_: *mut crate::leanh::LeanObject,
    mut v___y_4370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4372_ = crate::leanh::lean_box(0);
    v___x_4373_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4373_, 0, v___x_4372_);
    return v___x_4373_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(
    mut v_x_4374_: *mut crate::leanh::LeanObject,
    mut v_x_4375_: *mut crate::leanh::LeanObject,
    mut v_x_4376_: *mut crate::leanh::LeanObject,
    mut v___y_4377_: *mut crate::leanh::LeanObject,
    mut v___y_4378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4379_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(v_x_4374_, v_x_4375_, v_x_4376_, v___y_4377_);
    crate::leanh::lean_dec(v___y_4377_);
    crate::leanh::lean_dec_ref(v_x_4376_);
    crate::leanh::lean_dec_ref(v_x_4375_);
    crate::leanh::lean_dec(v_x_4374_);
    return v_res_4379_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(
    mut v___x_4380_: u8,
    mut v_env_4381_: *mut crate::leanh::LeanObject,
    mut v_n_4382_: *mut crate::leanh::LeanObject,
    mut v_x_4383_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4384_: u8 = 0;
    v___x_4384_ = l_Lean_Environment_contains(v_env_4381_, v_n_4382_, v___x_4380_);
    return v___x_4384_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(
    mut v___x_4385_: *mut crate::leanh::LeanObject,
    mut v_env_4386_: *mut crate::leanh::LeanObject,
    mut v_n_4387_: *mut crate::leanh::LeanObject,
    mut v_x_4388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_120__boxed_4389_: u8 = 0;
    let mut v_res_4390_: u8 = 0;
    let mut v_r_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_120__boxed_4389_ = (crate::leanh::lean_unbox(v___x_4385_) as u8);
    v_res_4390_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(v___x_120__boxed_4389_, v_env_4386_, v_n_4387_, v_x_4388_);
    crate::leanh::lean_dec_ref(v_x_4388_);
    v_r_4391_ = crate::leanh::lean_box((v_res_4390_) as usize);
    return v_r_4391_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4437_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__17_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_;
    v___x_4438_ = l_Lean_registerParametricAttribute___redArg(v___x_4437_);
    return v___x_4438_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(
    mut v_a_4439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4440_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_();
    return v_res_4440_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4443_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_;
    v___x_4444_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__0;
    v___x_4445_ = l_Lean_addBuiltinDocString(v___x_4443_, v___x_4444_);
    return v___x_4445_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___boxed(
    mut v_a_4446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4447_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1();
    return v_res_4447_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4474_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_;
    v___x_4475_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__6;
    v___x_4476_ = l_Lean_addBuiltinDeclarationRanges(v___x_4474_, v___x_4475_);
    return v___x_4476_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___boxed(
    mut v_a_4477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4478_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3();
    return v_res_4478_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4488_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_;
    v___x_4489_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_;
    v___x_4490_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_;
    v___x_4491_ = l_Lean_Meta_registerSimpAttr(v___x_4488_, v___x_4489_, v___x_4490_);
    return v___x_4491_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2____boxed(
    mut v_a_4492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4493_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_();
    return v_res_4493_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
    mut v_env_4494_: *mut crate::leanh::LeanObject,
    mut v_instName_4495_: *mut crate::leanh::LeanObject,
    mut v_privateSpecs_4496_: u8,
    mut v_suffix_4497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_thmName_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_thmName_4498_ = l_Lean_Name_str___override(v_instName_4495_, v_suffix_4497_);
    if v_privateSpecs_4496_ == 0 {
        return v_thmName_4498_;
    } else {
        let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4499_ = l_Lean_mkPrivateName(v_env_4494_, v_thmName_4498_);
        return v___x_4499_;
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName___boxed(
    mut v_env_4500_: *mut crate::leanh::LeanObject,
    mut v_instName_4501_: *mut crate::leanh::LeanObject,
    mut v_privateSpecs_4502_: *mut crate::leanh::LeanObject,
    mut v_suffix_4503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_privateSpecs_boxed_4504_: u8 = 0;
    let mut v_res_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_privateSpecs_boxed_4504_ = (crate::leanh::lean_unbox(v_privateSpecs_4502_) as u8);
    v_res_4505_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
        v_env_4500_,
        v_instName_4501_,
        v_privateSpecs_boxed_4504_,
        v_suffix_4503_,
    );
    crate::leanh::lean_dec_ref(v_env_4500_);
    return v_res_4505_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0___redArg(
    mut v_p_4506_: *mut crate::leanh::LeanObject,
    mut v_s_4507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: u8 = 0;
    v___x_4508_ = lean_string_utf8_byte_size(v_s_4507_);
    v___x_4509_ = lean_string_utf8_byte_size(v_p_4506_);
    v___x_4510_ = lean_nat_dec_le(v___x_4509_, v___x_4508_);
    if v___x_4510_ == 0 {
        let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_4507_);
        v___x_4511_ = crate::leanh::lean_box(0);
        return v___x_4511_;
    } else {
        let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4513_: u8 = 0;
        v___x_4512_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4513_ =
            lean_string_memcmp(v_s_4507_, v_p_4506_, v___x_4512_, v___x_4512_, v___x_4509_);
        if v___x_4513_ == 0 {
            let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_s_4507_);
            v___x_4514_ = crate::leanh::lean_box(0);
            return v___x_4514_;
        } else {
            let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_s_4507_);
            v___x_4515_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4515_, 0, v_s_4507_);
            crate::leanh::lean_ctor_set(v___x_4515_, 1, v___x_4512_);
            crate::leanh::lean_ctor_set(v___x_4515_, 2, v___x_4508_);
            v___x_4516_ = l_String_Slice_pos_x21(v___x_4515_, v___x_4509_);
            crate::leanh::lean_dec_ref_known(v___x_4515_, 3);
            v___x_4517_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4517_, 0, v_s_4507_);
            crate::leanh::lean_ctor_set(v___x_4517_, 1, v___x_4516_);
            crate::leanh::lean_ctor_set(v___x_4517_, 2, v___x_4508_);
            v___x_4518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4518_, 0, v___x_4517_);
            return v___x_4518_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0___redArg___boxed(
    mut v_p_4519_: *mut crate::leanh::LeanObject,
    mut v_s_4520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4521_ = l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0___redArg(v_p_4519_, v_s_4520_);
    crate::leanh::lean_dec_ref(v_p_4519_);
    return v_res_4521_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0(
    mut v_p_4522_: *mut crate::leanh::LeanObject,
    mut v_s_4523_: *mut crate::leanh::LeanObject,
    mut v_pat_4524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4525_ = l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0___redArg(v_p_4522_, v_s_4523_);
    return v___x_4525_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0___boxed(
    mut v_p_4526_: *mut crate::leanh::LeanObject,
    mut v_s_4527_: *mut crate::leanh::LeanObject,
    mut v_pat_4528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4529_ = l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0(v_p_4526_, v_s_4527_, v_pat_4528_);
    crate::leanh::lean_dec_ref(v_pat_4528_);
    crate::leanh::lean_dec_ref(v_p_4526_);
    return v_res_4529_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(
    mut v_s_4530_: *mut crate::leanh::LeanObject,
    mut v_p_4531_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4532_ = l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0___redArg(v_p_4531_, v_s_4530_);
    if crate::leanh::lean_obj_tag(v___x_4532_) == 0 {
        let mut v___x_4533_: u8 = 0;
        v___x_4533_ = 0;
        return v___x_4533_;
    } else {
        let mut v_val_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4535_: u8 = 0;
        v_val_4534_ = crate::leanh::lean_ctor_get(v___x_4532_, 0);
        crate::leanh::lean_inc(v_val_4534_);
        crate::leanh::lean_dec_ref_known(v___x_4532_, 1);
        v___x_4535_ = l_String_Slice_isNat(v_val_4534_);
        crate::leanh::lean_dec(v_val_4534_);
        return v___x_4535_;
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber___boxed(
    mut v_s_4536_: *mut crate::leanh::LeanObject,
    mut v_p_4537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4538_: u8 = 0;
    let mut v_r_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4538_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(v_s_4536_, v_p_4537_);
    crate::leanh::lean_dec_ref(v_p_4537_);
    v_r_4539_ = crate::leanh::lean_box((v_res_4538_) as usize);
    return v_r_4539_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(
    mut v_fieldName_4542_: *mut crate::leanh::LeanObject,
    mut v_s_4543_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4544_: u8 = 0;
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: u8 = 0;
    v___x_4544_ = 1;
    v___x_4545_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_fieldName_4542_,
        v___x_4544_,
    );
    v___x_4546_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0;
    crate::leanh::lean_inc_ref(v___x_4545_);
    v___x_4547_ = lean_string_append(v___x_4545_, v___x_4546_);
    v___x_4548_ = lean_string_dec_eq(v_s_4543_, v___x_4547_);
    crate::leanh::lean_dec_ref(v___x_4547_);
    if v___x_4548_ == 0 {
        let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4551_: u8 = 0;
        v___x_4549_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1;
        v___x_4550_ = lean_string_append(v___x_4545_, v___x_4549_);
        v___x_4551_ = l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(
            v_s_4543_,
            v___x_4550_,
        );
        crate::leanh::lean_dec_ref(v___x_4550_);
        return v___x_4551_;
    } else {
        crate::leanh::lean_dec_ref(v___x_4545_);
        crate::leanh::lean_dec_ref(v_s_4543_);
        return v___x_4548_;
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___boxed(
    mut v_fieldName_4552_: *mut crate::leanh::LeanObject,
    mut v_s_4553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4554_: u8 = 0;
    let mut v_r_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4554_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(v_fieldName_4552_, v_s_4553_);
    v_r_4555_ = crate::leanh::lean_box((v_res_4554_) as usize);
    return v_r_4555_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(
    mut v_str_4559_: *mut crate::leanh::LeanObject,
    mut v_val_4560_: *mut crate::leanh::LeanObject,
    mut v_env_4561_: *mut crate::leanh::LeanObject,
    mut v_p_4562_: *mut crate::leanh::LeanObject,
    mut v_name_4563_: *mut crate::leanh::LeanObject,
    mut v_as_4564_: *mut crate::leanh::LeanObject,
    mut v_sz_4565_: usize,
    mut v_i_4566_: usize,
    mut v_b_4567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: usize = 0;
    let mut v___x_4571_: usize = 0;
    let mut v___x_4573_: u8 = 0;
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: u8 = 0;
    let mut v_privateSpecs_4579_: u8 = 0;
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: u8 = 0;
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4573_ = lean_usize_dec_lt(v_i_4566_, v_sz_4565_);
                if v___x_4573_ == 0 {
                    crate::leanh::lean_dec(v_p_4562_);
                    crate::leanh::lean_dec_ref(v_str_4559_);
                    v___x_4574_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4574_, 0, v_b_4567_);
                    return v___x_4574_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4567_);
                    v___x_4575_ = crate::leanh::lean_box(0);
                    v___x_4576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0;
                    v_a_4577_ = lean_array_uget_borrowed(v_as_4564_, v_i_4566_);
                    crate::leanh::lean_inc_ref(v_str_4559_);
                    crate::leanh::lean_inc(v_a_4577_);
                    v___x_4578_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(
                        v_a_4577_,
                        v_str_4559_,
                    );
                    if v___x_4578_ == 0 {
                        v_a_4569_ = v___x_4576_;
                        state = 1;
                        continue;
                    } else {
                        v_privateSpecs_4579_ = crate::leanh::lean_ctor_get_uint8(
                            v_val_4560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        crate::leanh::lean_inc_ref(v_str_4559_);
                        crate::leanh::lean_inc(v_p_4562_);
                        v___x_4580_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                            v_env_4561_,
                            v_p_4562_,
                            v_privateSpecs_4579_,
                            v_str_4559_,
                        );
                        v___x_4581_ = lean_name_eq(v_name_4563_, v___x_4580_);
                        crate::leanh::lean_dec(v___x_4580_);
                        if v___x_4581_ == 0 {
                            v_a_4569_ = v___x_4576_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_str_4559_);
                            v___x_4582_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4582_, 0, v_p_4562_);
                            v___x_4583_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4583_, 0, v___x_4582_);
                            crate::leanh::lean_ctor_set(v___x_4583_, 1, v___x_4575_);
                            v___x_4584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4584_, 0, v___x_4583_);
                            return v___x_4584_;
                        }
                    }
                }
            }
            1 => {
                v___x_4570_ = 1usize;
                v___x_4571_ = lean_usize_add(v_i_4566_, v___x_4570_);
                crate::leanh::lean_inc_ref(v_a_4569_);
                v_i_4566_ = v___x_4571_;
                v_b_4567_ = v_a_4569_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___boxed(
    mut v_str_4585_: *mut crate::leanh::LeanObject,
    mut v_val_4586_: *mut crate::leanh::LeanObject,
    mut v_env_4587_: *mut crate::leanh::LeanObject,
    mut v_p_4588_: *mut crate::leanh::LeanObject,
    mut v_name_4589_: *mut crate::leanh::LeanObject,
    mut v_as_4590_: *mut crate::leanh::LeanObject,
    mut v_sz_4591_: *mut crate::leanh::LeanObject,
    mut v_i_4592_: *mut crate::leanh::LeanObject,
    mut v_b_4593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4594_: usize = 0;
    let mut v_i_boxed_4595_: usize = 0;
    let mut v_res_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4594_ = crate::leanh::lean_unbox_usize(v_sz_4591_);
    crate::leanh::lean_dec(v_sz_4591_);
    v_i_boxed_4595_ = crate::leanh::lean_unbox_usize(v_i_4592_);
    crate::leanh::lean_dec(v_i_4592_);
    v_res_4596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(v_str_4585_, v_val_4586_, v_env_4587_, v_p_4588_, v_name_4589_, v_as_4590_, v_sz_boxed_4594_, v_i_boxed_4595_, v_b_4593_);
    crate::leanh::lean_dec_ref(v_as_4590_);
    crate::leanh::lean_dec(v_name_4589_);
    crate::leanh::lean_dec_ref(v_env_4587_);
    crate::leanh::lean_dec_ref(v_val_4586_);
    return v_res_4596_;
}
pub unsafe fn l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(
    mut v_env_4597_: *mut crate::leanh::LeanObject,
    mut v_str_4598_: *mut crate::leanh::LeanObject,
    mut v_name_4599_: *mut crate::leanh::LeanObject,
    mut v_x_4600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clsName_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4612_: usize = 0;
    let mut v___x_4613_: usize = 0;
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4600_) == 0 {
                    crate::leanh::lean_dec_ref(v_str_4598_);
                    crate::leanh::lean_dec_ref(v_env_4597_);
                    v___x_4601_ = crate::leanh::lean_box(0);
                    return v___x_4601_;
                } else {
                    v_head_4602_ = crate::leanh::lean_ctor_get(v_x_4600_, 0);
                    crate::leanh::lean_inc_n(v_head_4602_, 2);
                    v_tail_4603_ = crate::leanh::lean_ctor_get(v_x_4600_, 1);
                    crate::leanh::lean_inc(v_tail_4603_);
                    crate::leanh::lean_dec_ref_known(v_x_4600_, 2);
                    v___x_4604_ = l_Lean_instInhabitedMethodSpecsAttrData_default;
                    v___x_4605_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
                    crate::leanh::lean_inc_ref(v_env_4597_);
                    v___x_4606_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
                        v___x_4604_,
                        v___x_4605_,
                        v_env_4597_,
                        v_head_4602_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4606_) == 0 {
                        crate::leanh::lean_dec(v_head_4602_);
                        v_x_4600_ = v_tail_4603_;
                        state = 0;
                        continue;
                    } else {
                        v_val_4608_ = crate::leanh::lean_ctor_get(v___x_4606_, 0);
                        crate::leanh::lean_inc(v_val_4608_);
                        crate::leanh::lean_dec_ref_known(v___x_4606_, 1);
                        v_clsName_4609_ = crate::leanh::lean_ctor_get(v_val_4608_, 0);
                        crate::leanh::lean_inc(v_clsName_4609_);
                        crate::leanh::lean_inc_ref(v_env_4597_);
                        v___x_4610_ = l_Lean_getStructureFields(v_env_4597_, v_clsName_4609_);
                        v___x_4611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0;
                        v_sz_4612_ = lean_array_size(v___x_4610_);
                        v___x_4613_ = 0usize;
                        crate::leanh::lean_inc_ref(v_str_4598_);
                        v___x_4614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(v_str_4598_, v_val_4608_, v_env_4597_, v_head_4602_, v_name_4599_, v___x_4610_, v_sz_4612_, v___x_4613_, v___x_4611_);
                        crate::leanh::lean_dec_ref(v___x_4610_);
                        crate::leanh::lean_dec(v_val_4608_);
                        if crate::leanh::lean_obj_tag(v___x_4614_) == 0 {
                            v_x_4600_ = v_tail_4603_;
                            state = 0;
                            continue;
                        } else {
                            v_val_4616_ = crate::leanh::lean_ctor_get(v___x_4614_, 0);
                            crate::leanh::lean_inc(v_val_4616_);
                            crate::leanh::lean_dec_ref_known(v___x_4614_, 1);
                            v_fst_4617_ = crate::leanh::lean_ctor_get(v_val_4616_, 0);
                            crate::leanh::lean_inc(v_fst_4617_);
                            crate::leanh::lean_dec(v_val_4616_);
                            if crate::leanh::lean_obj_tag(v_fst_4617_) == 0 {
                                v_x_4600_ = v_tail_4603_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_tail_4603_);
                                crate::leanh::lean_dec_ref(v_str_4598_);
                                crate::leanh::lean_dec_ref(v_env_4597_);
                                return v_fst_4617_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1___boxed(
    mut v_env_4619_: *mut crate::leanh::LeanObject,
    mut v_str_4620_: *mut crate::leanh::LeanObject,
    mut v_name_4621_: *mut crate::leanh::LeanObject,
    mut v_x_4622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4623_ =
        l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(
            v_env_4619_,
            v_str_4620_,
            v_name_4621_,
            v_x_4622_,
        );
    crate::leanh::lean_dec(v_name_4621_);
    return v_res_4623_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(
    mut v_env_4624_: *mut crate::leanh::LeanObject,
    mut v_name_4625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_name_4625_) == 1 {
        let mut v_pre_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_4626_ = crate::leanh::lean_ctor_get(v_name_4625_, 0);
        v_str_4627_ = crate::leanh::lean_ctor_get(v_name_4625_, 1);
        crate::leanh::lean_inc_ref(v_str_4627_);
        crate::leanh::lean_inc_n(v_pre_4626_, 2);
        v___x_4628_ = l_Lean_privateToUserName(v_pre_4626_);
        v___x_4629_ = crate::leanh::lean_box(0);
        v___x_4630_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4630_, 0, v___x_4628_);
        crate::leanh::lean_ctor_set(v___x_4630_, 1, v___x_4629_);
        v___x_4631_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4631_, 0, v_pre_4626_);
        crate::leanh::lean_ctor_set(v___x_4631_, 1, v___x_4630_);
        v___x_4632_ =
            l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(
                v_env_4624_,
                v_str_4627_,
                v_name_4625_,
                v___x_4631_,
            );
        crate::leanh::lean_dec_ref_known(v_name_4625_, 2);
        return v___x_4632_;
    } else {
        let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_name_4625_);
        crate::leanh::lean_dec_ref(v_env_4624_);
        v___x_4633_ = crate::leanh::lean_box(0);
        return v___x_4633_;
    }
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4634_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4634_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4635_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_4636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4636_, 0, v___x_4635_);
    return v___x_4636_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4637_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_4638_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4639_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4639_, 0, v___x_4638_);
    crate::leanh::lean_ctor_set(v___x_4639_, 1, v___x_4638_);
    crate::leanh::lean_ctor_set(v___x_4639_, 2, v___x_4638_);
    crate::leanh::lean_ctor_set(v___x_4639_, 3, v___x_4638_);
    crate::leanh::lean_ctor_set(v___x_4639_, 4, v___x_4637_);
    crate::leanh::lean_ctor_set(v___x_4639_, 5, v___x_4637_);
    crate::leanh::lean_ctor_set(v___x_4639_, 6, v___x_4637_);
    crate::leanh::lean_ctor_set(v___x_4639_, 7, v___x_4637_);
    crate::leanh::lean_ctor_set(v___x_4639_, 8, v___x_4637_);
    crate::leanh::lean_ctor_set(v___x_4639_, 9, v___x_4637_);
    return v___x_4639_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4640_ = crate::leanh::lean_box(1);
    v___x_4641_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6,
    );
    v___x_4642_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_4643_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4643_, 0, v___x_4642_);
    crate::leanh::lean_ctor_set(v___x_4643_, 1, v___x_4641_);
    crate::leanh::lean_ctor_set(v___x_4643_, 2, v___x_4640_);
    return v___x_4643_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4645_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
    v___x_4646_ = l_Lean_stringToMessageData(v___x_4645_);
    return v___x_4646_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4648_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_4649_ = l_Lean_stringToMessageData(v___x_4648_);
    return v___x_4649_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4651_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_4652_ = l_Lean_stringToMessageData(v___x_4651_);
    return v___x_4652_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4654_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_4655_ = l_Lean_stringToMessageData(v___x_4654_);
    return v___x_4655_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4657_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_4658_ = l_Lean_stringToMessageData(v___x_4657_);
    return v___x_4658_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4660_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_4661_ = l_Lean_stringToMessageData(v___x_4660_);
    return v___x_4661_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4663_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_4664_ = l_Lean_stringToMessageData(v___x_4663_);
    return v___x_4664_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_4665_: *mut crate::leanh::LeanObject,
    mut v_declHint_4666_: *mut crate::leanh::LeanObject,
    mut v___y_4667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: u8 = 0;
    let mut v_isExporting_4672_: u8 = 0;
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: u8 = 0;
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4694_: u8 = 0;
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: u8 = 0;
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4726_: u8 = 0;
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4669_ = lean_st_ref_get(v___y_4667_);
                v_env_4670_ = crate::leanh::lean_ctor_get(v___x_4669_, 0);
                crate::leanh::lean_inc_ref(v_env_4670_);
                crate::leanh::lean_dec(v___x_4669_);
                v___x_4671_ = l_Lean_Name_isAnonymous(v_declHint_4666_);
                if v___x_4671_ == 0 {
                    v_isExporting_4672_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_4670_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4672_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_4670_);
                        crate::leanh::lean_dec(v_declHint_4666_);
                        v___x_4673_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4673_, 0, v_msg_4665_);
                        return v___x_4673_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_4670_);
                        v___x_4674_ = l_Lean_Environment_setExporting(v_env_4670_, v___x_4671_);
                        crate::leanh::lean_inc(v_declHint_4666_);
                        crate::leanh::lean_inc_ref(v___x_4674_);
                        v___x_4675_ = l_Lean_Environment_contains(
                            v___x_4674_,
                            v_declHint_4666_,
                            v_isExporting_4672_,
                        );
                        if v___x_4675_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4674_);
                            crate::leanh::lean_dec_ref(v_env_4670_);
                            crate::leanh::lean_dec(v_declHint_4666_);
                            v___x_4676_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4676_, 0, v_msg_4665_);
                            return v___x_4676_;
                        } else {
                            v___x_4677_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_4678_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
                            v___x_4679_ = l_Lean_Options_empty;
                            v___x_4680_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4680_, 0, v___x_4674_);
                            crate::leanh::lean_ctor_set(v___x_4680_, 1, v___x_4677_);
                            crate::leanh::lean_ctor_set(v___x_4680_, 2, v___x_4678_);
                            crate::leanh::lean_ctor_set(v___x_4680_, 3, v___x_4679_);
                            crate::leanh::lean_inc(v_declHint_4666_);
                            v___x_4681_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4666_, v___x_4671_);
                            v_c_4682_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_4682_, 0, v___x_4680_);
                            crate::leanh::lean_ctor_set(v_c_4682_, 1, v___x_4681_);
                            v___x_4683_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4670_,
                                v_declHint_4666_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4683_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_4670_);
                                crate::leanh::lean_dec(v_declHint_4666_);
                                v___x_4684_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                                v___x_4685_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4685_, 0, v___x_4684_);
                                crate::leanh::lean_ctor_set(v___x_4685_, 1, v_c_4682_);
                                v___x_4686_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_4687_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4687_, 0, v___x_4685_);
                                crate::leanh::lean_ctor_set(v___x_4687_, 1, v___x_4686_);
                                v___x_4688_ = l_Lean_MessageData_note(v___x_4687_);
                                v___x_4689_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4689_, 0, v_msg_4665_);
                                crate::leanh::lean_ctor_set(v___x_4689_, 1, v___x_4688_);
                                v___x_4690_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4690_, 0, v___x_4689_);
                                return v___x_4690_;
                            } else {
                                v_val_4691_ = crate::leanh::lean_ctor_get(v___x_4683_, 0);
                                v_isSharedCheck_4726_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4683_)) as u8;
                                if v_isSharedCheck_4726_ == 0 {
                                    v___x_4693_ = v___x_4683_;
                                    v_isShared_4694_ = v_isSharedCheck_4726_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_4691_);
                                    crate::leanh::lean_dec(v___x_4683_);
                                    v___x_4693_ = crate::leanh::lean_box(0);
                                    v_isShared_4694_ = v_isSharedCheck_4726_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_4670_);
                    crate::leanh::lean_dec(v_declHint_4666_);
                    v___x_4727_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4727_, 0, v_msg_4665_);
                    return v___x_4727_;
                }
            }
            1 => {
                v___x_4695_ = crate::leanh::lean_box(0);
                v___x_4696_ = l_Lean_Environment_header(v_env_4670_);
                crate::leanh::lean_dec_ref(v_env_4670_);
                v___x_4697_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4696_);
                v_mod_4698_ = lean_array_get(v___x_4695_, v___x_4697_, v_val_4691_);
                crate::leanh::lean_dec(v_val_4691_);
                crate::leanh::lean_dec_ref(v___x_4697_);
                v___x_4699_ = l_Lean_isPrivateName(v_declHint_4666_);
                crate::leanh::lean_dec(v_declHint_4666_);
                if v___x_4699_ == 0 {
                    v___x_4700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                    v___x_4701_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4701_, 0, v___x_4700_);
                    crate::leanh::lean_ctor_set(v___x_4701_, 1, v_c_4682_);
                    v___x_4702_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_4703_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4703_, 0, v___x_4701_);
                    crate::leanh::lean_ctor_set(v___x_4703_, 1, v___x_4702_);
                    v___x_4704_ = l_Lean_MessageData_ofName(v_mod_4698_);
                    v___x_4705_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4705_, 0, v___x_4703_);
                    crate::leanh::lean_ctor_set(v___x_4705_, 1, v___x_4704_);
                    v___x_4706_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_4707_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4707_, 0, v___x_4705_);
                    crate::leanh::lean_ctor_set(v___x_4707_, 1, v___x_4706_);
                    v___x_4708_ = l_Lean_MessageData_note(v___x_4707_);
                    v___x_4709_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4709_, 0, v_msg_4665_);
                    crate::leanh::lean_ctor_set(v___x_4709_, 1, v___x_4708_);
                    if v_isShared_4694_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4693_, 0);
                        crate::leanh::lean_ctor_set(v___x_4693_, 0, v___x_4709_);
                        v___x_4711_ = v___x_4693_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4709_);
                        v___x_4711_ = v_reuseFailAlloc_4712_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4713_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                    v___x_4714_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4714_, 0, v___x_4713_);
                    crate::leanh::lean_ctor_set(v___x_4714_, 1, v_c_4682_);
                    v___x_4715_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_4716_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4716_, 0, v___x_4714_);
                    crate::leanh::lean_ctor_set(v___x_4716_, 1, v___x_4715_);
                    v___x_4717_ = l_Lean_MessageData_ofName(v_mod_4698_);
                    v___x_4718_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4718_, 0, v___x_4716_);
                    crate::leanh::lean_ctor_set(v___x_4718_, 1, v___x_4717_);
                    v___x_4719_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_4720_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4720_, 0, v___x_4718_);
                    crate::leanh::lean_ctor_set(v___x_4720_, 1, v___x_4719_);
                    v___x_4721_ = l_Lean_MessageData_note(v___x_4720_);
                    v___x_4722_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4722_, 0, v_msg_4665_);
                    crate::leanh::lean_ctor_set(v___x_4722_, 1, v___x_4721_);
                    if v_isShared_4694_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4693_, 0);
                        crate::leanh::lean_ctor_set(v___x_4693_, 0, v___x_4722_);
                        v___x_4724_ = v___x_4693_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4725_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4722_);
                        v___x_4724_ = v_reuseFailAlloc_4725_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4711_;
            }
            3 => {
                return v___x_4724_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_4728_: *mut crate::leanh::LeanObject,
    mut v_declHint_4729_: *mut crate::leanh::LeanObject,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
    mut v___y_4731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4732_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_4728_, v_declHint_4729_, v___y_4730_);
    crate::leanh::lean_dec(v___y_4730_);
    return v_res_4732_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_4733_: *mut crate::leanh::LeanObject,
    mut v_declHint_4734_: *mut crate::leanh::LeanObject,
    mut v___y_4735_: *mut crate::leanh::LeanObject,
    mut v___y_4736_: *mut crate::leanh::LeanObject,
    mut v___y_4737_: *mut crate::leanh::LeanObject,
    mut v___y_4738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4744_: u8 = 0;
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4740_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_4733_, v_declHint_4734_, v___y_4738_);
                v_a_4741_ = crate::leanh::lean_ctor_get(v___x_4740_, 0);
                v_isSharedCheck_4750_ = (!crate::leanh::lean_is_exclusive(v___x_4740_)) as u8;
                if v_isSharedCheck_4750_ == 0 {
                    v___x_4743_ = v___x_4740_;
                    v_isShared_4744_ = v_isSharedCheck_4750_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4741_);
                    crate::leanh::lean_dec(v___x_4740_);
                    v___x_4743_ = crate::leanh::lean_box(0);
                    v_isShared_4744_ = v_isSharedCheck_4750_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4745_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4746_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4746_, 0, v___x_4745_);
                crate::leanh::lean_ctor_set(v___x_4746_, 1, v_a_4741_);
                if v_isShared_4744_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4743_, 0, v___x_4746_);
                    v___x_4748_ = v___x_4743_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4749_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4746_);
                    v___x_4748_ = v_reuseFailAlloc_4749_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4748_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_4751_: *mut crate::leanh::LeanObject,
    mut v_declHint_4752_: *mut crate::leanh::LeanObject,
    mut v___y_4753_: *mut crate::leanh::LeanObject,
    mut v___y_4754_: *mut crate::leanh::LeanObject,
    mut v___y_4755_: *mut crate::leanh::LeanObject,
    mut v___y_4756_: *mut crate::leanh::LeanObject,
    mut v___y_4757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4758_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_4751_, v_declHint_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
    crate::leanh::lean_dec(v___y_4756_);
    crate::leanh::lean_dec_ref(v___y_4755_);
    crate::leanh::lean_dec(v___y_4754_);
    crate::leanh::lean_dec_ref(v___y_4753_);
    return v_res_4758_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_4759_: *mut crate::leanh::LeanObject,
    mut v_msg_4760_: *mut crate::leanh::LeanObject,
    mut v___y_4761_: *mut crate::leanh::LeanObject,
    mut v___y_4762_: *mut crate::leanh::LeanObject,
    mut v___y_4763_: *mut crate::leanh::LeanObject,
    mut v___y_4764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4778_: u8 = 0;
    let mut v_cancelTk_x3f_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4780_: u8 = 0;
    let mut v_inheritedTraceOptions_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_4766_ = crate::leanh::lean_ctor_get(v___y_4763_, 0);
    v_fileMap_4767_ = crate::leanh::lean_ctor_get(v___y_4763_, 1);
    v_options_4768_ = crate::leanh::lean_ctor_get(v___y_4763_, 2);
    v_currRecDepth_4769_ = crate::leanh::lean_ctor_get(v___y_4763_, 3);
    v_maxRecDepth_4770_ = crate::leanh::lean_ctor_get(v___y_4763_, 4);
    v_ref_4771_ = crate::leanh::lean_ctor_get(v___y_4763_, 5);
    v_currNamespace_4772_ = crate::leanh::lean_ctor_get(v___y_4763_, 6);
    v_openDecls_4773_ = crate::leanh::lean_ctor_get(v___y_4763_, 7);
    v_initHeartbeats_4774_ = crate::leanh::lean_ctor_get(v___y_4763_, 8);
    v_maxHeartbeats_4775_ = crate::leanh::lean_ctor_get(v___y_4763_, 9);
    v_quotContext_4776_ = crate::leanh::lean_ctor_get(v___y_4763_, 10);
    v_currMacroScope_4777_ = crate::leanh::lean_ctor_get(v___y_4763_, 11);
    v_diag_4778_ = crate::leanh::lean_ctor_get_uint8(
        v___y_4763_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4779_ = crate::leanh::lean_ctor_get(v___y_4763_, 12);
    v_suppressElabErrors_4780_ = crate::leanh::lean_ctor_get_uint8(
        v___y_4763_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4781_ = crate::leanh::lean_ctor_get(v___y_4763_, 13);
    v_ref_4782_ = l_Lean_replaceRef(v_ref_4759_, v_ref_4771_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4781_);
    crate::leanh::lean_inc(v_cancelTk_x3f_4779_);
    crate::leanh::lean_inc(v_currMacroScope_4777_);
    crate::leanh::lean_inc(v_quotContext_4776_);
    crate::leanh::lean_inc(v_maxHeartbeats_4775_);
    crate::leanh::lean_inc(v_initHeartbeats_4774_);
    crate::leanh::lean_inc(v_openDecls_4773_);
    crate::leanh::lean_inc(v_currNamespace_4772_);
    crate::leanh::lean_inc(v_maxRecDepth_4770_);
    crate::leanh::lean_inc(v_currRecDepth_4769_);
    crate::leanh::lean_inc_ref(v_options_4768_);
    crate::leanh::lean_inc_ref(v_fileMap_4767_);
    crate::leanh::lean_inc_ref(v_fileName_4766_);
    v___x_4783_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_4783_, 0, v_fileName_4766_);
    crate::leanh::lean_ctor_set(v___x_4783_, 1, v_fileMap_4767_);
    crate::leanh::lean_ctor_set(v___x_4783_, 2, v_options_4768_);
    crate::leanh::lean_ctor_set(v___x_4783_, 3, v_currRecDepth_4769_);
    crate::leanh::lean_ctor_set(v___x_4783_, 4, v_maxRecDepth_4770_);
    crate::leanh::lean_ctor_set(v___x_4783_, 5, v_ref_4782_);
    crate::leanh::lean_ctor_set(v___x_4783_, 6, v_currNamespace_4772_);
    crate::leanh::lean_ctor_set(v___x_4783_, 7, v_openDecls_4773_);
    crate::leanh::lean_ctor_set(v___x_4783_, 8, v_initHeartbeats_4774_);
    crate::leanh::lean_ctor_set(v___x_4783_, 9, v_maxHeartbeats_4775_);
    crate::leanh::lean_ctor_set(v___x_4783_, 10, v_quotContext_4776_);
    crate::leanh::lean_ctor_set(v___x_4783_, 11, v_currMacroScope_4777_);
    crate::leanh::lean_ctor_set(v___x_4783_, 12, v_cancelTk_x3f_4779_);
    crate::leanh::lean_ctor_set(v___x_4783_, 13, v_inheritedTraceOptions_4781_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4783_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_4778_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4783_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4780_,
    );
    v___x_4784_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v_msg_4760_, v___y_4761_, v___y_4762_, v___x_4783_, v___y_4764_);
    crate::leanh::lean_dec_ref_known(v___x_4783_, 14);
    return v___x_4784_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_4785_: *mut crate::leanh::LeanObject,
    mut v_msg_4786_: *mut crate::leanh::LeanObject,
    mut v___y_4787_: *mut crate::leanh::LeanObject,
    mut v___y_4788_: *mut crate::leanh::LeanObject,
    mut v___y_4789_: *mut crate::leanh::LeanObject,
    mut v___y_4790_: *mut crate::leanh::LeanObject,
    mut v___y_4791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4792_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_4785_, v_msg_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_);
    crate::leanh::lean_dec(v___y_4790_);
    crate::leanh::lean_dec_ref(v___y_4789_);
    crate::leanh::lean_dec(v___y_4788_);
    crate::leanh::lean_dec_ref(v___y_4787_);
    crate::leanh::lean_dec(v_ref_4785_);
    return v_res_4792_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_4793_: *mut crate::leanh::LeanObject,
    mut v_msg_4794_: *mut crate::leanh::LeanObject,
    mut v_declHint_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
    mut v___y_4799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4801_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_4794_, v_declHint_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
    v_a_4802_ = crate::leanh::lean_ctor_get(v___x_4801_, 0);
    crate::leanh::lean_inc(v_a_4802_);
    crate::leanh::lean_dec_ref(v___x_4801_);
    v___x_4803_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_4793_, v_a_4802_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
    return v___x_4803_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_4804_: *mut crate::leanh::LeanObject,
    mut v_msg_4805_: *mut crate::leanh::LeanObject,
    mut v_declHint_4806_: *mut crate::leanh::LeanObject,
    mut v___y_4807_: *mut crate::leanh::LeanObject,
    mut v___y_4808_: *mut crate::leanh::LeanObject,
    mut v___y_4809_: *mut crate::leanh::LeanObject,
    mut v___y_4810_: *mut crate::leanh::LeanObject,
    mut v___y_4811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4812_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_4804_, v_msg_4805_, v_declHint_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
    crate::leanh::lean_dec(v___y_4810_);
    crate::leanh::lean_dec_ref(v___y_4809_);
    crate::leanh::lean_dec(v___y_4808_);
    crate::leanh::lean_dec_ref(v___y_4807_);
    crate::leanh::lean_dec(v_ref_4804_);
    return v_res_4812_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4814_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_4815_ = l_Lean_stringToMessageData(v___x_4814_);
    return v___x_4815_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(
    mut v_ref_4816_: *mut crate::leanh::LeanObject,
    mut v_constName_4817_: *mut crate::leanh::LeanObject,
    mut v___y_4818_: *mut crate::leanh::LeanObject,
    mut v___y_4819_: *mut crate::leanh::LeanObject,
    mut v___y_4820_: *mut crate::leanh::LeanObject,
    mut v___y_4821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: u8 = 0;
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4823_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_4824_ = 0;
    crate::leanh::lean_inc(v_constName_4817_);
    v___x_4825_ = l_Lean_MessageData_ofConstName(v_constName_4817_, v___x_4824_);
    v___x_4826_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4826_, 0, v___x_4823_);
    crate::leanh::lean_ctor_set(v___x_4826_, 1, v___x_4825_);
    v___x_4827_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once), _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1);
    v___x_4828_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4828_, 0, v___x_4826_);
    crate::leanh::lean_ctor_set(v___x_4828_, 1, v___x_4827_);
    v___x_4829_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_4816_, v___x_4828_, v_constName_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
    return v___x_4829_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_4830_: *mut crate::leanh::LeanObject,
    mut v_constName_4831_: *mut crate::leanh::LeanObject,
    mut v___y_4832_: *mut crate::leanh::LeanObject,
    mut v___y_4833_: *mut crate::leanh::LeanObject,
    mut v___y_4834_: *mut crate::leanh::LeanObject,
    mut v___y_4835_: *mut crate::leanh::LeanObject,
    mut v___y_4836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4837_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(v_ref_4830_, v_constName_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
    crate::leanh::lean_dec(v___y_4835_);
    crate::leanh::lean_dec_ref(v___y_4834_);
    crate::leanh::lean_dec(v___y_4833_);
    crate::leanh::lean_dec_ref(v___y_4832_);
    crate::leanh::lean_dec(v_ref_4830_);
    return v_res_4837_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(
    mut v_constName_4838_: *mut crate::leanh::LeanObject,
    mut v___y_4839_: *mut crate::leanh::LeanObject,
    mut v___y_4840_: *mut crate::leanh::LeanObject,
    mut v___y_4841_: *mut crate::leanh::LeanObject,
    mut v___y_4842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_4844_ = crate::leanh::lean_ctor_get(v___y_4841_, 5);
    v___x_4845_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(v_ref_4844_, v_constName_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
    return v___x_4845_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg___boxed(
    mut v_constName_4846_: *mut crate::leanh::LeanObject,
    mut v___y_4847_: *mut crate::leanh::LeanObject,
    mut v___y_4848_: *mut crate::leanh::LeanObject,
    mut v___y_4849_: *mut crate::leanh::LeanObject,
    mut v___y_4850_: *mut crate::leanh::LeanObject,
    mut v___y_4851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4852_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(v_constName_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
    crate::leanh::lean_dec(v___y_4850_);
    crate::leanh::lean_dec_ref(v___y_4849_);
    crate::leanh::lean_dec(v___y_4848_);
    crate::leanh::lean_dec_ref(v___y_4847_);
    return v_res_4852_;
}
pub unsafe fn l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(
    mut v_constName_4853_: *mut crate::leanh::LeanObject,
    mut v___y_4854_: *mut crate::leanh::LeanObject,
    mut v___y_4855_: *mut crate::leanh::LeanObject,
    mut v___y_4856_: *mut crate::leanh::LeanObject,
    mut v___y_4857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: u8 = 0;
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4867_: u8 = 0;
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4859_ = lean_st_ref_get(v___y_4857_);
                v_env_4860_ = crate::leanh::lean_ctor_get(v___x_4859_, 0);
                crate::leanh::lean_inc_ref(v_env_4860_);
                crate::leanh::lean_dec(v___x_4859_);
                v___x_4861_ = 0;
                crate::leanh::lean_inc(v_constName_4853_);
                v___x_4862_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_4860_,
                    v_constName_4853_,
                    v___x_4861_,
                );
                if crate::leanh::lean_obj_tag(v___x_4862_) == 0 {
                    v___x_4863_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(v_constName_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
                    return v___x_4863_;
                } else {
                    crate::leanh::lean_dec(v_constName_4853_);
                    v_val_4864_ = crate::leanh::lean_ctor_get(v___x_4862_, 0);
                    v_isSharedCheck_4871_ = (!crate::leanh::lean_is_exclusive(v___x_4862_)) as u8;
                    if v_isSharedCheck_4871_ == 0 {
                        v___x_4866_ = v___x_4862_;
                        v_isShared_4867_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4864_);
                        crate::leanh::lean_dec(v___x_4862_);
                        v___x_4866_ = crate::leanh::lean_box(0);
                        v_isShared_4867_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4867_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4866_, 0);
                    v___x_4869_ = v___x_4866_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_val_4864_);
                    v___x_4869_ = v_reuseFailAlloc_4870_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4869_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0___boxed(
    mut v_constName_4872_: *mut crate::leanh::LeanObject,
    mut v___y_4873_: *mut crate::leanh::LeanObject,
    mut v___y_4874_: *mut crate::leanh::LeanObject,
    mut v___y_4875_: *mut crate::leanh::LeanObject,
    mut v___y_4876_: *mut crate::leanh::LeanObject,
    mut v___y_4877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4878_ =
        l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(
            v_constName_4872_,
            v___y_4873_,
            v___y_4874_,
            v___y_4875_,
            v___y_4876_,
        );
    crate::leanh::lean_dec(v___y_4876_);
    crate::leanh::lean_dec_ref(v___y_4875_);
    crate::leanh::lean_dec(v___y_4874_);
    crate::leanh::lean_dec_ref(v___y_4873_);
    return v_res_4878_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4879_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4879_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4880_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0,
    );
    v___x_4881_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4881_, 0, v___x_4880_);
    return v___x_4881_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4882_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4883_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1,
    );
    v___x_4884_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4884_, 0, v___x_4883_);
    crate::leanh::lean_ctor_set(v___x_4884_, 1, v___x_4882_);
    return v___x_4884_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4885_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4886_ = lean_mk_empty_array_with_capacity(v___x_4885_);
    v___x_4887_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4887_, 0, v___x_4886_);
    return v___x_4887_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4888_: usize = 0;
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4888_ = 5usize;
    v___x_4889_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4890_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4891_ = lean_mk_empty_array_with_capacity(v___x_4890_);
    v___x_4892_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3,
    );
    v___x_4893_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4893_, 0, v___x_4892_);
    crate::leanh::lean_ctor_set(v___x_4893_, 1, v___x_4891_);
    crate::leanh::lean_ctor_set(v___x_4893_, 2, v___x_4889_);
    crate::leanh::lean_ctor_set(v___x_4893_, 3, v___x_4889_);
    crate::leanh::lean_ctor_set_usize(v___x_4893_, 4, v___x_4888_);
    return v___x_4893_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4894_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4,
    );
    v___x_4895_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1,
    );
    v___x_4896_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4896_, 0, v___x_4895_);
    crate::leanh::lean_ctor_set(v___x_4896_, 1, v___x_4895_);
    crate::leanh::lean_ctor_set(v___x_4896_, 2, v___x_4895_);
    crate::leanh::lean_ctor_set(v___x_4896_, 3, v___x_4894_);
    return v___x_4896_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4897_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5,
    );
    v___x_4898_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2,
    );
    v___x_4899_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4899_, 0, v___x_4898_);
    crate::leanh::lean_ctor_set(v___x_4899_, 1, v___x_4897_);
    return v___x_4899_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4905_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4906_ = l_Lean_Level_ofNat(v___x_4905_);
    return v___x_4906_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4907_ = crate::leanh::lean_box(0);
    v___x_4908_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10,
    );
    v___x_4909_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4909_, 0, v___x_4908_);
    crate::leanh::lean_ctor_set(v___x_4909_, 1, v___x_4907_);
    return v___x_4909_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4910_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11,
    );
    v___x_4911_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9;
    v___x_4912_ = l_Lean_mkConst(v___x_4911_, v___x_4910_);
    return v___x_4912_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4914_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13;
    v___x_4915_ = l_Lean_stringToMessageData(v___x_4914_);
    return v___x_4915_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4917_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15;
    v___x_4918_ = l_Lean_stringToMessageData(v___x_4917_);
    return v___x_4918_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(
    mut v_ctx_4919_: *mut crate::leanh::LeanObject,
    mut v_simprocs_4920_: *mut crate::leanh::LeanObject,
    mut v_eqThmName_4921_: *mut crate::leanh::LeanObject,
    mut v_destThmName_4922_: *mut crate::leanh::LeanObject,
    mut v_a_4923_: *mut crate::leanh::LeanObject,
    mut v_a_4924_: *mut crate::leanh::LeanObject,
    mut v_a_4925_: *mut crate::leanh::LeanObject,
    mut v_a_4926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4945_: u8 = 0;
    let mut v___y_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: u8 = 0;
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4978_: u8 = 0;
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4982_: u8 = 0;
    let mut v_options_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4984_: u8 = 0;
    let mut v_inheritedTraceOptions_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: u8 = 0;
    let mut v_expr_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4998_: u8 = 0;
    let mut v_unused_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5003_: u8 = 0;
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5007_: u8 = 0;
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v_unused_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5013_: u8 = 0;
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_eqThmName_4921_);
                v___x_4928_ = l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(v_eqThmName_4921_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
                if crate::leanh::lean_obj_tag(v___x_4928_) == 0 {
                    v_a_4929_ = crate::leanh::lean_ctor_get(v___x_4928_, 0);
                    crate::leanh::lean_inc(v_a_4929_);
                    crate::leanh::lean_dec_ref_known(v___x_4928_, 1);
                    v_levelParams_4930_ = crate::leanh::lean_ctor_get(v_a_4929_, 1);
                    v_type_4931_ = crate::leanh::lean_ctor_get(v_a_4929_, 2);
                    v_isSharedCheck_5008_ = (!crate::leanh::lean_is_exclusive(v_a_4929_)) as u8;
                    if v_isSharedCheck_5008_ == 0 {
                        v_unused_5009_ = crate::leanh::lean_ctor_get(v_a_4929_, 0);
                        crate::leanh::lean_dec(v_unused_5009_);
                        v___x_4933_ = v_a_4929_;
                        v_isShared_4934_ = v_isSharedCheck_5008_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_type_4931_);
                        crate::leanh::lean_inc(v_levelParams_4930_);
                        crate::leanh::lean_dec(v_a_4929_);
                        v___x_4933_ = crate::leanh::lean_box(0);
                        v_isShared_4934_ = v_isSharedCheck_5008_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_destThmName_4922_);
                    crate::leanh::lean_dec(v_eqThmName_4921_);
                    crate::leanh::lean_dec_ref(v_simprocs_4920_);
                    crate::leanh::lean_dec_ref(v_ctx_4919_);
                    v_a_5010_ = crate::leanh::lean_ctor_get(v___x_4928_, 0);
                    v_isSharedCheck_5017_ = (!crate::leanh::lean_is_exclusive(v___x_4928_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v___x_5012_ = v___x_4928_;
                        v_isShared_5013_ = v_isSharedCheck_5017_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5010_);
                        crate::leanh::lean_dec(v___x_4928_);
                        v___x_5012_ = crate::leanh::lean_box(0);
                        v_isShared_5013_ = v_isSharedCheck_5017_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4935_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4936_ = lean_mk_empty_array_with_capacity(v___x_4935_);
                v___x_4937_ = lean_array_push(v___x_4936_, v_simprocs_4920_);
                v___x_4938_ = crate::leanh::lean_box(0);
                v___x_4939_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6_once
                    ),
                    _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6,
                );
                crate::leanh::lean_inc_ref(v_type_4931_);
                v___x_4940_ = l_Lean_Meta_simp(
                    v_type_4931_,
                    v_ctx_4919_,
                    v___x_4937_,
                    v___x_4938_,
                    v___x_4939_,
                    v_a_4923_,
                    v_a_4924_,
                    v_a_4925_,
                    v_a_4926_,
                );
                if crate::leanh::lean_obj_tag(v___x_4940_) == 0 {
                    v_a_4941_ = crate::leanh::lean_ctor_get(v___x_4940_, 0);
                    crate::leanh::lean_inc(v_a_4941_);
                    crate::leanh::lean_dec_ref_known(v___x_4940_, 1);
                    v_fst_4942_ = crate::leanh::lean_ctor_get(v_a_4941_, 0);
                    v_isSharedCheck_4998_ = (!crate::leanh::lean_is_exclusive(v_a_4941_)) as u8;
                    if v_isSharedCheck_4998_ == 0 {
                        v_unused_4999_ = crate::leanh::lean_ctor_get(v_a_4941_, 1);
                        crate::leanh::lean_dec(v_unused_4999_);
                        v___x_4944_ = v_a_4941_;
                        v_isShared_4945_ = v_isSharedCheck_4998_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_4942_);
                        crate::leanh::lean_dec(v_a_4941_);
                        v___x_4944_ = crate::leanh::lean_box(0);
                        v_isShared_4945_ = v_isSharedCheck_4998_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4933_);
                    crate::leanh::lean_dec_ref(v_type_4931_);
                    crate::leanh::lean_dec(v_levelParams_4930_);
                    crate::leanh::lean_dec(v_destThmName_4922_);
                    crate::leanh::lean_dec(v_eqThmName_4921_);
                    v_a_5000_ = crate::leanh::lean_ctor_get(v___x_4940_, 0);
                    v_isSharedCheck_5007_ = (!crate::leanh::lean_is_exclusive(v___x_4940_)) as u8;
                    if v_isSharedCheck_5007_ == 0 {
                        v___x_5002_ = v___x_4940_;
                        v_isShared_5003_ = v_isSharedCheck_5007_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5000_);
                        crate::leanh::lean_dec(v___x_4940_);
                        v___x_5002_ = crate::leanh::lean_box(0);
                        v_isShared_5003_ = v_isSharedCheck_5007_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_options_4983_ = crate::leanh::lean_ctor_get(v_a_4925_, 2);
                v_hasTrace_4984_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_4983_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_4984_ == 0 {
                    v___y_4947_ = v_a_4923_;
                    v___y_4948_ = v_a_4924_;
                    v___y_4949_ = v_a_4925_;
                    v___y_4950_ = v_a_4926_;
                    state = 3;
                    continue;
                } else {
                    v_inheritedTraceOptions_4985_ = crate::leanh::lean_ctor_get(v_a_4925_, 13);
                    v___x_4986_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3;
                    v___x_4987_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6);
                    v___x_4988_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4985_,
                        v_options_4983_,
                        v___x_4987_,
                    );
                    if v___x_4988_ == 0 {
                        v___y_4947_ = v_a_4923_;
                        v___y_4948_ = v_a_4924_;
                        v___y_4949_ = v_a_4925_;
                        v___y_4950_ = v_a_4926_;
                        state = 3;
                        continue;
                    } else {
                        v_expr_4989_ = crate::leanh::lean_ctor_get(v_fst_4942_, 0);
                        v___x_4990_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14);
                        crate::leanh::lean_inc(v_destThmName_4922_);
                        v___x_4991_ = l_Lean_MessageData_ofName(v_destThmName_4922_);
                        v___x_4992_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4992_, 0, v___x_4990_);
                        crate::leanh::lean_ctor_set(v___x_4992_, 1, v___x_4991_);
                        v___x_4993_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16);
                        v___x_4994_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4994_, 0, v___x_4992_);
                        crate::leanh::lean_ctor_set(v___x_4994_, 1, v___x_4993_);
                        crate::leanh::lean_inc_ref(v_expr_4989_);
                        v___x_4995_ = l_Lean_indentExpr(v_expr_4989_);
                        v___x_4996_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4996_, 0, v___x_4994_);
                        crate::leanh::lean_ctor_set(v___x_4996_, 1, v___x_4995_);
                        v___x_4997_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v___x_4986_, v___x_4996_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
                        if crate::leanh::lean_obj_tag(v___x_4997_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4997_, 1);
                            v___y_4947_ = v_a_4923_;
                            v___y_4948_ = v_a_4924_;
                            v___y_4949_ = v_a_4925_;
                            v___y_4950_ = v_a_4926_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_4944_);
                            crate::leanh::lean_dec(v_fst_4942_);
                            crate::leanh::lean_del_object(v___x_4933_);
                            crate::leanh::lean_dec_ref(v_type_4931_);
                            crate::leanh::lean_dec(v_levelParams_4930_);
                            crate::leanh::lean_dec(v_destThmName_4922_);
                            crate::leanh::lean_dec(v_eqThmName_4921_);
                            return v___x_4997_;
                        }
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_fst_4942_);
                v___x_4951_ = l_Lean_Meta_Simp_Result_getProof(
                    v_fst_4942_,
                    v___y_4947_,
                    v___y_4948_,
                    v___y_4949_,
                    v___y_4950_,
                );
                if crate::leanh::lean_obj_tag(v___x_4951_) == 0 {
                    v_a_4952_ = crate::leanh::lean_ctor_get(v___x_4951_, 0);
                    crate::leanh::lean_inc(v_a_4952_);
                    crate::leanh::lean_dec_ref_known(v___x_4951_, 1);
                    v_expr_4953_ = crate::leanh::lean_ctor_get(v_fst_4942_, 0);
                    crate::leanh::lean_inc_ref_n(v_expr_4953_, 2);
                    crate::leanh::lean_dec(v_fst_4942_);
                    v___x_4954_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_levelParams_4930_);
                    v___x_4955_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__2(v_levelParams_4930_, v___x_4954_);
                    v___x_4956_ = l_Lean_mkConst(v_eqThmName_4921_, v___x_4955_);
                    v___x_4957_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12_once
                        ),
                        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12,
                    );
                    v___x_4958_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4959_ = lean_mk_empty_array_with_capacity(v___x_4958_);
                    v___x_4960_ = lean_array_push(v___x_4959_, v_type_4931_);
                    v___x_4961_ = lean_array_push(v___x_4960_, v_expr_4953_);
                    v___x_4962_ = lean_array_push(v___x_4961_, v_a_4952_);
                    v___x_4963_ = lean_array_push(v___x_4962_, v___x_4956_);
                    v___x_4964_ = l_Lean_mkAppN(v___x_4957_, v___x_4963_);
                    crate::leanh::lean_dec_ref(v___x_4963_);
                    crate::leanh::lean_inc(v_destThmName_4922_);
                    if v_isShared_4934_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4933_, 2, v_expr_4953_);
                        crate::leanh::lean_ctor_set(v___x_4933_, 0, v_destThmName_4922_);
                        v___x_4966_ = v___x_4933_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4974_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_destThmName_4922_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4974_, 1, v_levelParams_4930_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4974_, 2, v_expr_4953_);
                        v___x_4966_ = v_reuseFailAlloc_4974_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4944_);
                    crate::leanh::lean_dec(v_fst_4942_);
                    crate::leanh::lean_del_object(v___x_4933_);
                    crate::leanh::lean_dec_ref(v_type_4931_);
                    crate::leanh::lean_dec(v_levelParams_4930_);
                    crate::leanh::lean_dec(v_destThmName_4922_);
                    crate::leanh::lean_dec(v_eqThmName_4921_);
                    v_a_4975_ = crate::leanh::lean_ctor_get(v___x_4951_, 0);
                    v_isSharedCheck_4982_ = (!crate::leanh::lean_is_exclusive(v___x_4951_)) as u8;
                    if v_isSharedCheck_4982_ == 0 {
                        v___x_4977_ = v___x_4951_;
                        v_isShared_4978_ = v_isSharedCheck_4982_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4975_);
                        crate::leanh::lean_dec(v___x_4951_);
                        v___x_4977_ = crate::leanh::lean_box(0);
                        v_isShared_4978_ = v_isSharedCheck_4982_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4945_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4944_, 1);
                    crate::leanh::lean_ctor_set(v___x_4944_, 1, v___x_4954_);
                    crate::leanh::lean_ctor_set(v___x_4944_, 0, v_destThmName_4922_);
                    v___x_4968_ = v___x_4944_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4973_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_destThmName_4922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 1, v___x_4954_);
                    v___x_4968_ = v_reuseFailAlloc_4973_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4969_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4969_, 0, v___x_4966_);
                crate::leanh::lean_ctor_set(v___x_4969_, 1, v___x_4964_);
                crate::leanh::lean_ctor_set(v___x_4969_, 2, v___x_4968_);
                v___x_4970_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4970_, 0, v___x_4969_);
                v___x_4971_ = 0;
                v___x_4972_ = l_Lean_addDecl(v___x_4970_, v___x_4971_, v___y_4949_, v___y_4950_);
                return v___x_4972_;
            }
            6 => {
                if v_isShared_4978_ == 0 {
                    v___x_4980_ = v___x_4977_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4981_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4975_);
                    v___x_4980_ = v_reuseFailAlloc_4981_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4980_;
            }
            8 => {
                if v_isShared_5003_ == 0 {
                    v___x_5005_ = v___x_5002_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_5000_);
                    v___x_5005_ = v_reuseFailAlloc_5006_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5005_;
            }
            10 => {
                if v_isShared_5013_ == 0 {
                    v___x_5015_ = v___x_5012_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
                    v___x_5015_ = v_reuseFailAlloc_5016_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___boxed(
    mut v_ctx_5018_: *mut crate::leanh::LeanObject,
    mut v_simprocs_5019_: *mut crate::leanh::LeanObject,
    mut v_eqThmName_5020_: *mut crate::leanh::LeanObject,
    mut v_destThmName_5021_: *mut crate::leanh::LeanObject,
    mut v_a_5022_: *mut crate::leanh::LeanObject,
    mut v_a_5023_: *mut crate::leanh::LeanObject,
    mut v_a_5024_: *mut crate::leanh::LeanObject,
    mut v_a_5025_: *mut crate::leanh::LeanObject,
    mut v_a_5026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5027_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(
        v_ctx_5018_,
        v_simprocs_5019_,
        v_eqThmName_5020_,
        v_destThmName_5021_,
        v_a_5022_,
        v_a_5023_,
        v_a_5024_,
        v_a_5025_,
    );
    crate::leanh::lean_dec(v_a_5025_);
    crate::leanh::lean_dec_ref(v_a_5024_);
    crate::leanh::lean_dec(v_a_5023_);
    crate::leanh::lean_dec_ref(v_a_5022_);
    return v_res_5027_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0(
    mut v_00_u03b1_5028_: *mut crate::leanh::LeanObject,
    mut v_constName_5029_: *mut crate::leanh::LeanObject,
    mut v___y_5030_: *mut crate::leanh::LeanObject,
    mut v___y_5031_: *mut crate::leanh::LeanObject,
    mut v___y_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5035_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(v_constName_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_);
    return v___x_5035_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___boxed(
    mut v_00_u03b1_5036_: *mut crate::leanh::LeanObject,
    mut v_constName_5037_: *mut crate::leanh::LeanObject,
    mut v___y_5038_: *mut crate::leanh::LeanObject,
    mut v___y_5039_: *mut crate::leanh::LeanObject,
    mut v___y_5040_: *mut crate::leanh::LeanObject,
    mut v___y_5041_: *mut crate::leanh::LeanObject,
    mut v___y_5042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5043_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0(v_00_u03b1_5036_, v_constName_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
    crate::leanh::lean_dec(v___y_5041_);
    crate::leanh::lean_dec_ref(v___y_5040_);
    crate::leanh::lean_dec(v___y_5039_);
    crate::leanh::lean_dec_ref(v___y_5038_);
    return v_res_5043_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1(
    mut v_00_u03b1_5044_: *mut crate::leanh::LeanObject,
    mut v_ref_5045_: *mut crate::leanh::LeanObject,
    mut v_constName_5046_: *mut crate::leanh::LeanObject,
    mut v___y_5047_: *mut crate::leanh::LeanObject,
    mut v___y_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5052_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(v_ref_5045_, v_constName_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_);
    return v___x_5052_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_5053_: *mut crate::leanh::LeanObject,
    mut v_ref_5054_: *mut crate::leanh::LeanObject,
    mut v_constName_5055_: *mut crate::leanh::LeanObject,
    mut v___y_5056_: *mut crate::leanh::LeanObject,
    mut v___y_5057_: *mut crate::leanh::LeanObject,
    mut v___y_5058_: *mut crate::leanh::LeanObject,
    mut v___y_5059_: *mut crate::leanh::LeanObject,
    mut v___y_5060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5061_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1(v_00_u03b1_5053_, v_ref_5054_, v_constName_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_);
    crate::leanh::lean_dec(v___y_5059_);
    crate::leanh::lean_dec_ref(v___y_5058_);
    crate::leanh::lean_dec(v___y_5057_);
    crate::leanh::lean_dec_ref(v___y_5056_);
    crate::leanh::lean_dec(v_ref_5054_);
    return v_res_5061_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_5062_: *mut crate::leanh::LeanObject,
    mut v_ref_5063_: *mut crate::leanh::LeanObject,
    mut v_msg_5064_: *mut crate::leanh::LeanObject,
    mut v_declHint_5065_: *mut crate::leanh::LeanObject,
    mut v___y_5066_: *mut crate::leanh::LeanObject,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5071_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_5063_, v_msg_5064_, v_declHint_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_);
    return v___x_5071_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_5072_: *mut crate::leanh::LeanObject,
    mut v_ref_5073_: *mut crate::leanh::LeanObject,
    mut v_msg_5074_: *mut crate::leanh::LeanObject,
    mut v_declHint_5075_: *mut crate::leanh::LeanObject,
    mut v___y_5076_: *mut crate::leanh::LeanObject,
    mut v___y_5077_: *mut crate::leanh::LeanObject,
    mut v___y_5078_: *mut crate::leanh::LeanObject,
    mut v___y_5079_: *mut crate::leanh::LeanObject,
    mut v___y_5080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5081_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_5072_, v_ref_5073_, v_msg_5074_, v_declHint_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_);
    crate::leanh::lean_dec(v___y_5079_);
    crate::leanh::lean_dec_ref(v___y_5078_);
    crate::leanh::lean_dec(v___y_5077_);
    crate::leanh::lean_dec_ref(v___y_5076_);
    crate::leanh::lean_dec(v_ref_5073_);
    return v_res_5081_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_5082_: *mut crate::leanh::LeanObject,
    mut v_declHint_5083_: *mut crate::leanh::LeanObject,
    mut v___y_5084_: *mut crate::leanh::LeanObject,
    mut v___y_5085_: *mut crate::leanh::LeanObject,
    mut v___y_5086_: *mut crate::leanh::LeanObject,
    mut v___y_5087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5089_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_5082_, v_declHint_5083_, v___y_5087_);
    return v___x_5089_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_5090_: *mut crate::leanh::LeanObject,
    mut v_declHint_5091_: *mut crate::leanh::LeanObject,
    mut v___y_5092_: *mut crate::leanh::LeanObject,
    mut v___y_5093_: *mut crate::leanh::LeanObject,
    mut v___y_5094_: *mut crate::leanh::LeanObject,
    mut v___y_5095_: *mut crate::leanh::LeanObject,
    mut v___y_5096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5097_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_5090_, v_declHint_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
    crate::leanh::lean_dec(v___y_5095_);
    crate::leanh::lean_dec_ref(v___y_5094_);
    crate::leanh::lean_dec(v___y_5093_);
    crate::leanh::lean_dec_ref(v___y_5092_);
    return v_res_5097_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_5098_: *mut crate::leanh::LeanObject,
    mut v_ref_5099_: *mut crate::leanh::LeanObject,
    mut v_msg_5100_: *mut crate::leanh::LeanObject,
    mut v___y_5101_: *mut crate::leanh::LeanObject,
    mut v___y_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
    mut v___y_5104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5106_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_5099_, v_msg_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
    return v___x_5106_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_5107_: *mut crate::leanh::LeanObject,
    mut v_ref_5108_: *mut crate::leanh::LeanObject,
    mut v_msg_5109_: *mut crate::leanh::LeanObject,
    mut v___y_5110_: *mut crate::leanh::LeanObject,
    mut v___y_5111_: *mut crate::leanh::LeanObject,
    mut v___y_5112_: *mut crate::leanh::LeanObject,
    mut v___y_5113_: *mut crate::leanh::LeanObject,
    mut v___y_5114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5115_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_5107_, v_ref_5108_, v_msg_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_);
    crate::leanh::lean_dec(v___y_5113_);
    crate::leanh::lean_dec_ref(v___y_5112_);
    crate::leanh::lean_dec(v___y_5111_);
    crate::leanh::lean_dec_ref(v___y_5110_);
    crate::leanh::lean_dec(v_ref_5108_);
    return v_res_5115_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(
    mut v___x_5116_: *mut crate::leanh::LeanObject,
    mut v___x_5117_: *mut crate::leanh::LeanObject,
    mut v_instName_5118_: *mut crate::leanh::LeanObject,
    mut v___x_5119_: u8,
    mut v_a_5120_: *mut crate::leanh::LeanObject,
    mut v_a_5121_: *mut crate::leanh::LeanObject,
    mut v_as_5122_: *mut crate::leanh::LeanObject,
    mut v_sz_5123_: usize,
    mut v_i_5124_: usize,
    mut v_b_5125_: *mut crate::leanh::LeanObject,
    mut v___y_5126_: *mut crate::leanh::LeanObject,
    mut v___y_5127_: *mut crate::leanh::LeanObject,
    mut v___y_5128_: *mut crate::leanh::LeanObject,
    mut v___y_5129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5131_: u8 = 0;
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: u8 = 0;
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5140_: u8 = 0;
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: usize = 0;
    let mut v___x_5154_: usize = 0;
    let mut v_reuseFailAlloc_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5160_: u8 = 0;
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5164_: u8 = 0;
    let mut v_isSharedCheck_5165_: u8 = 0;
    let mut v_unused_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5131_ = lean_usize_dec_lt(v_i_5124_, v_sz_5123_);
                if v___x_5131_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_5121_);
                    crate::leanh::lean_dec_ref(v_a_5120_);
                    crate::leanh::lean_dec(v_instName_5118_);
                    crate::leanh::lean_dec_ref(v___x_5116_);
                    v___x_5132_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5132_, 0, v_b_5125_);
                    return v___x_5132_;
                } else {
                    v_start_5133_ = crate::leanh::lean_ctor_get(v_b_5125_, 0);
                    v_stop_5134_ = crate::leanh::lean_ctor_get(v_b_5125_, 1);
                    v_step_5135_ = crate::leanh::lean_ctor_get(v_b_5125_, 2);
                    v___x_5136_ = lean_nat_dec_lt(v_start_5133_, v_stop_5134_);
                    if v___x_5136_ == 0 {
                        crate::leanh::lean_dec_ref(v_a_5121_);
                        crate::leanh::lean_dec_ref(v_a_5120_);
                        crate::leanh::lean_dec(v_instName_5118_);
                        crate::leanh::lean_dec_ref(v___x_5116_);
                        v___x_5137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5137_, 0, v_b_5125_);
                        return v___x_5137_;
                    } else {
                        crate::leanh::lean_inc(v_step_5135_);
                        crate::leanh::lean_inc(v_stop_5134_);
                        crate::leanh::lean_inc(v_start_5133_);
                        v_isSharedCheck_5165_ = (!crate::leanh::lean_is_exclusive(v_b_5125_)) as u8;
                        if v_isSharedCheck_5165_ == 0 {
                            v_unused_5166_ = crate::leanh::lean_ctor_get(v_b_5125_, 2);
                            crate::leanh::lean_dec(v_unused_5166_);
                            v_unused_5167_ = crate::leanh::lean_ctor_get(v_b_5125_, 1);
                            crate::leanh::lean_dec(v_unused_5167_);
                            v_unused_5168_ = crate::leanh::lean_ctor_get(v_b_5125_, 0);
                            crate::leanh::lean_dec(v_unused_5168_);
                            v___x_5139_ = v_b_5125_;
                            v_isShared_5140_ = v_isSharedCheck_5165_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_5125_);
                            v___x_5139_ = crate::leanh::lean_box(0);
                            v_isShared_5140_ = v_isSharedCheck_5165_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5141_ = crate::leanh::lean_unsigned_to_nat(1);
                v_a_5142_ = lean_array_uget_borrowed(v_as_5122_, v_i_5124_);
                v___x_5143_ =
                    l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1;
                crate::leanh::lean_inc_ref(v___x_5116_);
                v___x_5144_ = lean_string_append(v___x_5116_, v___x_5143_);
                v___x_5145_ = lean_nat_add(v_start_5133_, v___x_5141_);
                v___x_5146_ = l_Nat_reprFast(v___x_5145_);
                v___x_5147_ = lean_string_append(v___x_5144_, v___x_5146_);
                crate::leanh::lean_dec_ref(v___x_5146_);
                crate::leanh::lean_inc(v_instName_5118_);
                v___x_5148_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                    v___x_5117_,
                    v_instName_5118_,
                    v___x_5119_,
                    v___x_5147_,
                );
                crate::leanh::lean_inc(v_a_5142_);
                crate::leanh::lean_inc_ref(v_a_5121_);
                crate::leanh::lean_inc_ref(v_a_5120_);
                v___x_5149_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(
                    v_a_5120_,
                    v_a_5121_,
                    v_a_5142_,
                    v___x_5148_,
                    v___y_5126_,
                    v___y_5127_,
                    v___y_5128_,
                    v___y_5129_,
                );
                if crate::leanh::lean_obj_tag(v___x_5149_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5149_, 1);
                    v___x_5150_ = lean_nat_add(v_start_5133_, v_step_5135_);
                    crate::leanh::lean_dec(v_start_5133_);
                    if v_isShared_5140_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5139_, 0, v___x_5150_);
                        v___x_5152_ = v___x_5139_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5156_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5150_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5156_, 1, v_stop_5134_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5156_, 2, v_step_5135_);
                        v___x_5152_ = v_reuseFailAlloc_5156_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5139_);
                    crate::leanh::lean_dec(v_step_5135_);
                    crate::leanh::lean_dec(v_stop_5134_);
                    crate::leanh::lean_dec(v_start_5133_);
                    crate::leanh::lean_dec_ref(v_a_5121_);
                    crate::leanh::lean_dec_ref(v_a_5120_);
                    crate::leanh::lean_dec(v_instName_5118_);
                    crate::leanh::lean_dec_ref(v___x_5116_);
                    v_a_5157_ = crate::leanh::lean_ctor_get(v___x_5149_, 0);
                    v_isSharedCheck_5164_ = (!crate::leanh::lean_is_exclusive(v___x_5149_)) as u8;
                    if v_isSharedCheck_5164_ == 0 {
                        v___x_5159_ = v___x_5149_;
                        v_isShared_5160_ = v_isSharedCheck_5164_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5157_);
                        crate::leanh::lean_dec(v___x_5149_);
                        v___x_5159_ = crate::leanh::lean_box(0);
                        v_isShared_5160_ = v_isSharedCheck_5164_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5153_ = 1usize;
                v___x_5154_ = lean_usize_add(v_i_5124_, v___x_5153_);
                v_i_5124_ = v___x_5154_;
                v_b_5125_ = v___x_5152_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_5160_ == 0 {
                    v___x_5162_ = v___x_5159_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5163_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
                    v___x_5162_ = v_reuseFailAlloc_5163_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1___boxed(
    mut v___x_5169_: *mut crate::leanh::LeanObject,
    mut v___x_5170_: *mut crate::leanh::LeanObject,
    mut v_instName_5171_: *mut crate::leanh::LeanObject,
    mut v___x_5172_: *mut crate::leanh::LeanObject,
    mut v_a_5173_: *mut crate::leanh::LeanObject,
    mut v_a_5174_: *mut crate::leanh::LeanObject,
    mut v_as_5175_: *mut crate::leanh::LeanObject,
    mut v_sz_5176_: *mut crate::leanh::LeanObject,
    mut v_i_5177_: *mut crate::leanh::LeanObject,
    mut v_b_5178_: *mut crate::leanh::LeanObject,
    mut v___y_5179_: *mut crate::leanh::LeanObject,
    mut v___y_5180_: *mut crate::leanh::LeanObject,
    mut v___y_5181_: *mut crate::leanh::LeanObject,
    mut v___y_5182_: *mut crate::leanh::LeanObject,
    mut v___y_5183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9646__boxed_5184_: u8 = 0;
    let mut v_sz_boxed_5185_: usize = 0;
    let mut v_i_boxed_5186_: usize = 0;
    let mut v_res_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9646__boxed_5184_ = (crate::leanh::lean_unbox(v___x_5172_) as u8);
    v_sz_boxed_5185_ = crate::leanh::lean_unbox_usize(v_sz_5176_);
    crate::leanh::lean_dec(v_sz_5176_);
    v_i_boxed_5186_ = crate::leanh::lean_unbox_usize(v_i_5177_);
    crate::leanh::lean_dec(v_i_5177_);
    v_res_5187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(v___x_5169_, v___x_5170_, v_instName_5171_, v___x_9646__boxed_5184_, v_a_5173_, v_a_5174_, v_as_5175_, v_sz_boxed_5185_, v_i_boxed_5186_, v_b_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_);
    crate::leanh::lean_dec(v___y_5182_);
    crate::leanh::lean_dec_ref(v___y_5181_);
    crate::leanh::lean_dec(v___y_5180_);
    crate::leanh::lean_dec_ref(v___y_5179_);
    crate::leanh::lean_dec_ref(v_as_5175_);
    crate::leanh::lean_dec_ref(v___x_5170_);
    return v_res_5187_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0;
    v___x_5190_ = l_Lean_stringToMessageData(v___x_5189_);
    return v___x_5190_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(
    mut v_a_5191_: *mut crate::leanh::LeanObject,
    mut v___x_5192_: *mut crate::leanh::LeanObject,
    mut v_instName_5193_: *mut crate::leanh::LeanObject,
    mut v_a_5194_: *mut crate::leanh::LeanObject,
    mut v_a_5195_: *mut crate::leanh::LeanObject,
    mut v_as_5196_: *mut crate::leanh::LeanObject,
    mut v_sz_5197_: usize,
    mut v_i_5198_: usize,
    mut v_b_5199_: *mut crate::leanh::LeanObject,
    mut v___y_5200_: *mut crate::leanh::LeanObject,
    mut v___y_5201_: *mut crate::leanh::LeanObject,
    mut v___y_5202_: *mut crate::leanh::LeanObject,
    mut v___y_5203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: usize = 0;
    let mut v___x_5208_: usize = 0;
    let mut v___x_5210_: u8 = 0;
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5217_: u8 = 0;
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_privateSpecs_5222_: u8 = 0;
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5235_: usize = 0;
    let mut v___x_5236_: usize = 0;
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5241_: u8 = 0;
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5245_: u8 = 0;
    let mut v_a_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5249_: u8 = 0;
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5253_: u8 = 0;
    let mut v___x_5254_: u8 = 0;
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5264_: u8 = 0;
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5268_: u8 = 0;
    let mut v_isSharedCheck_5269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5210_ = lean_usize_dec_lt(v_i_5198_, v_sz_5197_);
                if v___x_5210_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_5195_);
                    crate::leanh::lean_dec_ref(v_a_5194_);
                    crate::leanh::lean_dec(v_instName_5193_);
                    v___x_5211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5211_, 0, v_b_5199_);
                    return v___x_5211_;
                } else {
                    v_a_5212_ = lean_array_uget(v_as_5196_, v_i_5198_);
                    v_fst_5213_ = crate::leanh::lean_ctor_get(v_a_5212_, 0);
                    v_snd_5214_ = crate::leanh::lean_ctor_get(v_a_5212_, 1);
                    v_isSharedCheck_5269_ = (!crate::leanh::lean_is_exclusive(v_a_5212_)) as u8;
                    if v_isSharedCheck_5269_ == 0 {
                        v___x_5216_ = v_a_5212_;
                        v_isShared_5217_ = v_isSharedCheck_5269_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5214_);
                        crate::leanh::lean_inc(v_fst_5213_);
                        crate::leanh::lean_dec(v_a_5212_);
                        v___x_5216_ = crate::leanh::lean_box(0);
                        v_isShared_5217_ = v_isSharedCheck_5269_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5207_ = 1usize;
                v___x_5208_ = lean_usize_add(v_i_5198_, v___x_5207_);
                v_i_5198_ = v___x_5208_;
                v_b_5199_ = v_a_5206_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc(v_snd_5214_);
                v___x_5218_ = l_Lean_Meta_getUnfoldEqnFor_x3f(
                    v_snd_5214_,
                    v___x_5210_,
                    v___y_5200_,
                    v___y_5201_,
                    v___y_5202_,
                    v___y_5203_,
                );
                if crate::leanh::lean_obj_tag(v___x_5218_) == 0 {
                    v_a_5219_ = crate::leanh::lean_ctor_get(v___x_5218_, 0);
                    crate::leanh::lean_inc(v_a_5219_);
                    crate::leanh::lean_dec_ref_known(v___x_5218_, 1);
                    v___x_5220_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v_a_5219_) == 1 {
                        crate::leanh::lean_del_object(v___x_5216_);
                        v_val_5221_ = crate::leanh::lean_ctor_get(v_a_5219_, 0);
                        crate::leanh::lean_inc(v_val_5221_);
                        crate::leanh::lean_dec_ref_known(v_a_5219_, 1);
                        v_privateSpecs_5222_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_5191_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v___x_5223_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_fst_5213_,
                                v___x_5210_,
                            );
                        v___x_5224_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0;
                        crate::leanh::lean_inc_ref(v___x_5223_);
                        v___x_5225_ = lean_string_append(v___x_5223_, v___x_5224_);
                        crate::leanh::lean_inc(v_instName_5193_);
                        v___x_5226_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                            v___x_5192_,
                            v_instName_5193_,
                            v_privateSpecs_5222_,
                            v___x_5225_,
                        );
                        crate::leanh::lean_inc_ref(v_a_5195_);
                        crate::leanh::lean_inc_ref(v_a_5194_);
                        v___x_5227_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(
                            v_a_5194_,
                            v_a_5195_,
                            v_val_5221_,
                            v___x_5226_,
                            v___y_5200_,
                            v___y_5201_,
                            v___y_5202_,
                            v___y_5203_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5227_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5227_, 1);
                            v___x_5228_ = l_Lean_Meta_getEqnsFor_x3f(
                                v_snd_5214_,
                                v___y_5200_,
                                v___y_5201_,
                                v___y_5202_,
                                v___y_5203_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5228_) == 0 {
                                v_a_5229_ = crate::leanh::lean_ctor_get(v___x_5228_, 0);
                                crate::leanh::lean_inc(v_a_5229_);
                                crate::leanh::lean_dec_ref_known(v___x_5228_, 1);
                                if crate::leanh::lean_obj_tag(v_a_5229_) == 1 {
                                    v_val_5230_ = crate::leanh::lean_ctor_get(v_a_5229_, 0);
                                    crate::leanh::lean_inc(v_val_5230_);
                                    crate::leanh::lean_dec_ref_known(v_a_5229_, 1);
                                    v___x_5231_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_5232_ = lean_array_get_size(v_val_5230_);
                                    v___x_5233_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_5234_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_5234_, 0, v___x_5231_);
                                    crate::leanh::lean_ctor_set(v___x_5234_, 1, v___x_5232_);
                                    crate::leanh::lean_ctor_set(v___x_5234_, 2, v___x_5233_);
                                    v_sz_5235_ = lean_array_size(v_val_5230_);
                                    v___x_5236_ = 0usize;
                                    crate::leanh::lean_inc_ref(v_a_5195_);
                                    crate::leanh::lean_inc_ref(v_a_5194_);
                                    crate::leanh::lean_inc(v_instName_5193_);
                                    v___x_5237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(v___x_5223_, v___x_5192_, v_instName_5193_, v_privateSpecs_5222_, v_a_5194_, v_a_5195_, v_val_5230_, v_sz_5235_, v___x_5236_, v___x_5234_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_);
                                    crate::leanh::lean_dec(v_val_5230_);
                                    if crate::leanh::lean_obj_tag(v___x_5237_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_5237_, 1);
                                        v_a_5206_ = v___x_5220_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_a_5195_);
                                        crate::leanh::lean_dec_ref(v_a_5194_);
                                        crate::leanh::lean_dec(v_instName_5193_);
                                        v_a_5238_ = crate::leanh::lean_ctor_get(v___x_5237_, 0);
                                        v_isSharedCheck_5245_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5237_)) as u8;
                                        if v_isSharedCheck_5245_ == 0 {
                                            v___x_5240_ = v___x_5237_;
                                            v_isShared_5241_ = v_isSharedCheck_5245_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5238_);
                                            crate::leanh::lean_dec(v___x_5237_);
                                            v___x_5240_ = crate::leanh::lean_box(0);
                                            v_isShared_5241_ = v_isSharedCheck_5245_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5229_);
                                    crate::leanh::lean_dec_ref(v___x_5223_);
                                    v_a_5206_ = v___x_5220_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_5223_);
                                crate::leanh::lean_dec_ref(v_a_5195_);
                                crate::leanh::lean_dec_ref(v_a_5194_);
                                crate::leanh::lean_dec(v_instName_5193_);
                                v_a_5246_ = crate::leanh::lean_ctor_get(v___x_5228_, 0);
                                v_isSharedCheck_5253_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5228_)) as u8;
                                if v_isSharedCheck_5253_ == 0 {
                                    v___x_5248_ = v___x_5228_;
                                    v_isShared_5249_ = v_isSharedCheck_5253_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5246_);
                                    crate::leanh::lean_dec(v___x_5228_);
                                    v___x_5248_ = crate::leanh::lean_box(0);
                                    v_isShared_5249_ = v_isSharedCheck_5253_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5223_);
                            crate::leanh::lean_dec(v_snd_5214_);
                            crate::leanh::lean_dec_ref(v_a_5195_);
                            crate::leanh::lean_dec_ref(v_a_5194_);
                            crate::leanh::lean_dec(v_instName_5193_);
                            return v___x_5227_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5219_);
                        crate::leanh::lean_dec(v_fst_5213_);
                        v___x_5254_ = 0;
                        v___x_5255_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1);
                        v___x_5256_ = l_Lean_MessageData_ofConstName(v_snd_5214_, v___x_5254_);
                        if v_isShared_5217_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_5216_, 7);
                            crate::leanh::lean_ctor_set(v___x_5216_, 1, v___x_5256_);
                            crate::leanh::lean_ctor_set(v___x_5216_, 0, v___x_5255_);
                            v___x_5258_ = v___x_5216_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_5260_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5260_, 0, v___x_5255_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5260_, 1, v___x_5256_);
                            v___x_5258_ = v_reuseFailAlloc_5260_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5216_);
                    crate::leanh::lean_dec(v_snd_5214_);
                    crate::leanh::lean_dec(v_fst_5213_);
                    crate::leanh::lean_dec_ref(v_a_5195_);
                    crate::leanh::lean_dec_ref(v_a_5194_);
                    crate::leanh::lean_dec(v_instName_5193_);
                    v_a_5261_ = crate::leanh::lean_ctor_get(v___x_5218_, 0);
                    v_isSharedCheck_5268_ = (!crate::leanh::lean_is_exclusive(v___x_5218_)) as u8;
                    if v_isSharedCheck_5268_ == 0 {
                        v___x_5263_ = v___x_5218_;
                        v_isShared_5264_ = v_isSharedCheck_5268_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5261_);
                        crate::leanh::lean_dec(v___x_5218_);
                        v___x_5263_ = crate::leanh::lean_box(0);
                        v_isShared_5264_ = v_isSharedCheck_5268_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5241_ == 0 {
                    v___x_5243_ = v___x_5240_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5244_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_a_5238_);
                    v___x_5243_ = v_reuseFailAlloc_5244_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5243_;
            }
            5 => {
                if v_isShared_5249_ == 0 {
                    v___x_5251_ = v___x_5248_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5252_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_a_5246_);
                    v___x_5251_ = v_reuseFailAlloc_5252_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5251_;
            }
            7 => {
                v___x_5259_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_5258_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_);
                if crate::leanh::lean_obj_tag(v___x_5259_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5259_, 1);
                    v_a_5206_ = v___x_5220_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_a_5195_);
                    crate::leanh::lean_dec_ref(v_a_5194_);
                    crate::leanh::lean_dec(v_instName_5193_);
                    return v___x_5259_;
                }
            }
            8 => {
                if v_isShared_5264_ == 0 {
                    v___x_5266_ = v___x_5263_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5267_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5261_);
                    v___x_5266_ = v_reuseFailAlloc_5267_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___boxed(
    mut v_a_5270_: *mut crate::leanh::LeanObject,
    mut v___x_5271_: *mut crate::leanh::LeanObject,
    mut v_instName_5272_: *mut crate::leanh::LeanObject,
    mut v_a_5273_: *mut crate::leanh::LeanObject,
    mut v_a_5274_: *mut crate::leanh::LeanObject,
    mut v_as_5275_: *mut crate::leanh::LeanObject,
    mut v_sz_5276_: *mut crate::leanh::LeanObject,
    mut v_i_5277_: *mut crate::leanh::LeanObject,
    mut v_b_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
    mut v___y_5280_: *mut crate::leanh::LeanObject,
    mut v___y_5281_: *mut crate::leanh::LeanObject,
    mut v___y_5282_: *mut crate::leanh::LeanObject,
    mut v___y_5283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5284_: usize = 0;
    let mut v_i_boxed_5285_: usize = 0;
    let mut v_res_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5284_ = crate::leanh::lean_unbox_usize(v_sz_5276_);
    crate::leanh::lean_dec(v_sz_5276_);
    v_i_boxed_5285_ = crate::leanh::lean_unbox_usize(v_i_5277_);
    crate::leanh::lean_dec(v_i_5277_);
    v_res_5286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(v_a_5270_, v___x_5271_, v_instName_5272_, v_a_5273_, v_a_5274_, v_as_5275_, v_sz_boxed_5284_, v_i_boxed_5285_, v_b_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_);
    crate::leanh::lean_dec(v___y_5282_);
    crate::leanh::lean_dec_ref(v___y_5281_);
    crate::leanh::lean_dec(v___y_5280_);
    crate::leanh::lean_dec_ref(v___y_5279_);
    crate::leanh::lean_dec_ref(v_as_5275_);
    crate::leanh::lean_dec_ref(v___x_5271_);
    crate::leanh::lean_dec_ref(v_a_5270_);
    return v_res_5286_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0;
    v___x_5289_ = l_Lean_stringToMessageData(v___x_5288_);
    return v___x_5289_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2;
    v___x_5292_ = l_Lean_stringToMessageData(v___x_5291_);
    return v___x_5292_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(
    mut v_as_5293_: *mut crate::leanh::LeanObject,
    mut v_sz_5294_: usize,
    mut v_i_5295_: usize,
    mut v_b_5296_: *mut crate::leanh::LeanObject,
    mut v___y_5297_: *mut crate::leanh::LeanObject,
    mut v___y_5298_: *mut crate::leanh::LeanObject,
    mut v___y_5299_: *mut crate::leanh::LeanObject,
    mut v___y_5300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5302_: u8 = 0;
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5306_: u8 = 0;
    let mut v_a_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: usize = 0;
    let mut v___x_5324_: usize = 0;
    let mut v_a_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5329_: u8 = 0;
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5333_: u8 = 0;
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: u8 = 0;
    let mut v_name_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5350_: u8 = 0;
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5302_ = lean_usize_dec_lt(v_i_5295_, v_sz_5294_);
                if v___x_5302_ == 0 {
                    v___x_5303_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5303_, 0, v_b_5296_);
                    return v___x_5303_;
                } else {
                    v_options_5304_ = crate::leanh::lean_ctor_get(v___y_5299_, 2);
                    v_inheritedTraceOptions_5305_ = crate::leanh::lean_ctor_get(v___y_5299_, 13);
                    v_hasTrace_5306_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_5304_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_a_5307_ = lean_array_uget_borrowed(v_as_5293_, v_i_5295_);
                    if v_hasTrace_5306_ == 0 {
                        v___y_5309_ = v___y_5297_;
                        v___y_5310_ = v___y_5298_;
                        v___y_5311_ = v___y_5299_;
                        v___y_5312_ = v___y_5300_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5334_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3;
                        v___x_5335_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6);
                        v___x_5336_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5305_,
                            v_options_5304_,
                            v___x_5335_,
                        );
                        if v___x_5336_ == 0 {
                            v___y_5309_ = v___y_5297_;
                            v___y_5310_ = v___y_5298_;
                            v___y_5311_ = v___y_5299_;
                            v___y_5312_ = v___y_5300_;
                            state = 1;
                            continue;
                        } else {
                            v_name_5337_ = crate::leanh::lean_ctor_get(v_a_5307_, 0);
                            v_type_5338_ = crate::leanh::lean_ctor_get(v_a_5307_, 2);
                            v___x_5339_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1);
                            crate::leanh::lean_inc(v_name_5337_);
                            v___x_5340_ = l_Lean_MessageData_ofName(v_name_5337_);
                            v___x_5341_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5341_, 0, v___x_5339_);
                            crate::leanh::lean_ctor_set(v___x_5341_, 1, v___x_5340_);
                            v___x_5342_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3);
                            v___x_5343_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5343_, 0, v___x_5341_);
                            crate::leanh::lean_ctor_set(v___x_5343_, 1, v___x_5342_);
                            crate::leanh::lean_inc_ref(v_type_5338_);
                            v___x_5344_ = l_Lean_MessageData_ofExpr(v_type_5338_);
                            v___x_5345_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5345_, 0, v___x_5343_);
                            crate::leanh::lean_ctor_set(v___x_5345_, 1, v___x_5344_);
                            v___x_5346_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v___x_5334_, v___x_5345_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_);
                            if crate::leanh::lean_obj_tag(v___x_5346_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5346_, 1);
                                v___y_5309_ = v___y_5297_;
                                v___y_5310_ = v___y_5298_;
                                v___y_5311_ = v___y_5299_;
                                v___y_5312_ = v___y_5300_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_b_5296_);
                                v_a_5347_ = crate::leanh::lean_ctor_get(v___x_5346_, 0);
                                v_isSharedCheck_5354_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5346_)) as u8;
                                if v_isSharedCheck_5354_ == 0 {
                                    v___x_5349_ = v___x_5346_;
                                    v_isShared_5350_ = v_isSharedCheck_5354_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5347_);
                                    crate::leanh::lean_dec(v___x_5346_);
                                    v___x_5349_ = crate::leanh::lean_box(0);
                                    v_isShared_5350_ = v_isSharedCheck_5354_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v_name_5313_ = crate::leanh::lean_ctor_get(v_a_5307_, 0);
                v_levelParams_5314_ = crate::leanh::lean_ctor_get(v_a_5307_, 1);
                v_type_5315_ = crate::leanh::lean_ctor_get(v_a_5307_, 2);
                crate::leanh::lean_inc(v_name_5313_);
                v___x_5316_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5316_, 0, v_name_5313_);
                crate::leanh::lean_inc(v_levelParams_5314_);
                v___x_5317_ = lean_array_mk(v_levelParams_5314_);
                v___x_5318_ = crate::leanh::lean_unsigned_to_nat(1000);
                v___x_5319_ = l_Lean_Meta_simpGlobalConfig;
                crate::leanh::lean_inc_ref(v_type_5315_);
                v___x_5320_ = l_Lean_Meta_mkDSimpTheorem(
                    v___x_5316_,
                    v___x_5317_,
                    v_type_5315_,
                    v___x_5302_,
                    v___x_5318_,
                    v___x_5319_,
                    v___y_5309_,
                    v___y_5310_,
                    v___y_5311_,
                    v___y_5312_,
                );
                if crate::leanh::lean_obj_tag(v___x_5320_) == 0 {
                    v_a_5321_ = crate::leanh::lean_ctor_get(v___x_5320_, 0);
                    crate::leanh::lean_inc(v_a_5321_);
                    crate::leanh::lean_dec_ref_known(v___x_5320_, 1);
                    v___x_5322_ = l_Lean_Meta_SimpTheorems_addSimpTheorem(v_b_5296_, v_a_5321_);
                    v___x_5323_ = 1usize;
                    v___x_5324_ = lean_usize_add(v_i_5295_, v___x_5323_);
                    v_i_5295_ = v___x_5324_;
                    v_b_5296_ = v___x_5322_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5296_);
                    v_a_5326_ = crate::leanh::lean_ctor_get(v___x_5320_, 0);
                    v_isSharedCheck_5333_ = (!crate::leanh::lean_is_exclusive(v___x_5320_)) as u8;
                    if v_isSharedCheck_5333_ == 0 {
                        v___x_5328_ = v___x_5320_;
                        v_isShared_5329_ = v_isSharedCheck_5333_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5326_);
                        crate::leanh::lean_dec(v___x_5320_);
                        v___x_5328_ = crate::leanh::lean_box(0);
                        v_isShared_5329_ = v_isSharedCheck_5333_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5329_ == 0 {
                    v___x_5331_ = v___x_5328_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5326_);
                    v___x_5331_ = v_reuseFailAlloc_5332_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5331_;
            }
            4 => {
                if v_isShared_5350_ == 0 {
                    v___x_5352_ = v___x_5349_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5347_);
                    v___x_5352_ = v_reuseFailAlloc_5353_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___boxed(
    mut v_as_5355_: *mut crate::leanh::LeanObject,
    mut v_sz_5356_: *mut crate::leanh::LeanObject,
    mut v_i_5357_: *mut crate::leanh::LeanObject,
    mut v_b_5358_: *mut crate::leanh::LeanObject,
    mut v___y_5359_: *mut crate::leanh::LeanObject,
    mut v___y_5360_: *mut crate::leanh::LeanObject,
    mut v___y_5361_: *mut crate::leanh::LeanObject,
    mut v___y_5362_: *mut crate::leanh::LeanObject,
    mut v___y_5363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5364_: usize = 0;
    let mut v_i_boxed_5365_: usize = 0;
    let mut v_res_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5364_ = crate::leanh::lean_unbox_usize(v_sz_5356_);
    crate::leanh::lean_dec(v_sz_5356_);
    v_i_boxed_5365_ = crate::leanh::lean_unbox_usize(v_i_5357_);
    crate::leanh::lean_dec(v_i_5357_);
    v_res_5366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(v_as_5355_, v_sz_boxed_5364_, v_i_boxed_5365_, v_b_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_);
    crate::leanh::lean_dec(v___y_5362_);
    crate::leanh::lean_dec_ref(v___y_5361_);
    crate::leanh::lean_dec(v___y_5360_);
    crate::leanh::lean_dec_ref(v___y_5359_);
    crate::leanh::lean_dec_ref(v_as_5355_);
    return v_res_5366_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0(
    mut v___x_5374_: *mut crate::leanh::LeanObject,
    mut v_thms_5375_: *mut crate::leanh::LeanObject,
    mut v_fieldImpls_5376_: *mut crate::leanh::LeanObject,
    mut v_a_5377_: *mut crate::leanh::LeanObject,
    mut v_instName_5378_: *mut crate::leanh::LeanObject,
    mut v___y_5379_: *mut crate::leanh::LeanObject,
    mut v___y_5380_: *mut crate::leanh::LeanObject,
    mut v___y_5381_: *mut crate::leanh::LeanObject,
    mut v___y_5382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5386_: usize = 0;
    let mut v___x_5387_: usize = 0;
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5404_: usize = 0;
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5408_: u8 = 0;
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5412_: u8 = 0;
    let mut v_unused_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5417_: u8 = 0;
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5421_: u8 = 0;
    let mut v_a_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5425_: u8 = 0;
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5429_: u8 = 0;
    let mut v_a_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5433_: u8 = 0;
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5437_: u8 = 0;
    let mut v_a_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5441_: u8 = 0;
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5445_: u8 = 0;
    let mut v_a_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5449_: u8 = 0;
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5384_ =
                    l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_5374_, v___y_5382_);
                if crate::leanh::lean_obj_tag(v___x_5384_) == 0 {
                    v_a_5385_ = crate::leanh::lean_ctor_get(v___x_5384_, 0);
                    crate::leanh::lean_inc(v_a_5385_);
                    crate::leanh::lean_dec_ref_known(v___x_5384_, 1);
                    v_sz_5386_ = lean_array_size(v_thms_5375_);
                    v___x_5387_ = 0usize;
                    v___x_5388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(v_thms_5375_, v_sz_5386_, v___x_5387_, v_a_5385_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
                    if crate::leanh::lean_obj_tag(v___x_5388_) == 0 {
                        v_a_5389_ = crate::leanh::lean_ctor_get(v___x_5388_, 0);
                        crate::leanh::lean_inc(v_a_5389_);
                        crate::leanh::lean_dec_ref_known(v___x_5388_, 1);
                        v___x_5390_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_5382_);
                        if crate::leanh::lean_obj_tag(v___x_5390_) == 0 {
                            v_a_5391_ = crate::leanh::lean_ctor_get(v___x_5390_, 0);
                            crate::leanh::lean_inc(v_a_5391_);
                            crate::leanh::lean_dec_ref_known(v___x_5390_, 1);
                            v___x_5392_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0;
                            v___x_5393_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_5394_ = lean_mk_empty_array_with_capacity(v___x_5393_);
                            v___x_5395_ = lean_array_push(v___x_5394_, v_a_5389_);
                            v___x_5396_ = l_Lean_Options_empty;
                            v___x_5397_ = l_Lean_Meta_Simp_mkContext___redArg(
                                v___x_5392_,
                                v___x_5395_,
                                v_a_5391_,
                                v___x_5396_,
                                v___y_5379_,
                                v___y_5381_,
                                v___y_5382_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5397_) == 0 {
                                v_a_5398_ = crate::leanh::lean_ctor_get(v___x_5397_, 0);
                                crate::leanh::lean_inc(v_a_5398_);
                                crate::leanh::lean_dec_ref_known(v___x_5397_, 1);
                                v___x_5399_ = l_Lean_Meta_Simp_getSimprocs___redArg(v___y_5382_);
                                if crate::leanh::lean_obj_tag(v___x_5399_) == 0 {
                                    v_a_5400_ = crate::leanh::lean_ctor_get(v___x_5399_, 0);
                                    crate::leanh::lean_inc(v_a_5400_);
                                    crate::leanh::lean_dec_ref_known(v___x_5399_, 1);
                                    v___x_5401_ = lean_st_ref_get(v___y_5382_);
                                    v_env_5402_ = crate::leanh::lean_ctor_get(v___x_5401_, 0);
                                    crate::leanh::lean_inc_ref(v_env_5402_);
                                    crate::leanh::lean_dec(v___x_5401_);
                                    v___x_5403_ = crate::leanh::lean_box(0);
                                    v_sz_5404_ = lean_array_size(v_fieldImpls_5376_);
                                    v___x_5405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(v_a_5377_, v_env_5402_, v_instName_5378_, v_a_5398_, v_a_5400_, v_fieldImpls_5376_, v_sz_5404_, v___x_5387_, v___x_5403_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
                                    crate::leanh::lean_dec_ref(v_env_5402_);
                                    if crate::leanh::lean_obj_tag(v___x_5405_) == 0 {
                                        v_isSharedCheck_5412_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5405_)) as u8;
                                        if v_isSharedCheck_5412_ == 0 {
                                            v_unused_5413_ =
                                                crate::leanh::lean_ctor_get(v___x_5405_, 0);
                                            crate::leanh::lean_dec(v_unused_5413_);
                                            v___x_5407_ = v___x_5405_;
                                            v_isShared_5408_ = v_isSharedCheck_5412_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_5405_);
                                            v___x_5407_ = crate::leanh::lean_box(0);
                                            v_isShared_5408_ = v_isSharedCheck_5412_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        return v___x_5405_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5398_);
                                    crate::leanh::lean_dec(v_instName_5378_);
                                    v_a_5414_ = crate::leanh::lean_ctor_get(v___x_5399_, 0);
                                    v_isSharedCheck_5421_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5399_)) as u8;
                                    if v_isSharedCheck_5421_ == 0 {
                                        v___x_5416_ = v___x_5399_;
                                        v_isShared_5417_ = v_isSharedCheck_5421_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5414_);
                                        crate::leanh::lean_dec(v___x_5399_);
                                        v___x_5416_ = crate::leanh::lean_box(0);
                                        v_isShared_5417_ = v_isSharedCheck_5421_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_instName_5378_);
                                v_a_5422_ = crate::leanh::lean_ctor_get(v___x_5397_, 0);
                                v_isSharedCheck_5429_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5397_)) as u8;
                                if v_isSharedCheck_5429_ == 0 {
                                    v___x_5424_ = v___x_5397_;
                                    v_isShared_5425_ = v_isSharedCheck_5429_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5422_);
                                    crate::leanh::lean_dec(v___x_5397_);
                                    v___x_5424_ = crate::leanh::lean_box(0);
                                    v_isShared_5425_ = v_isSharedCheck_5429_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5389_);
                            crate::leanh::lean_dec(v_instName_5378_);
                            v_a_5430_ = crate::leanh::lean_ctor_get(v___x_5390_, 0);
                            v_isSharedCheck_5437_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5390_)) as u8;
                            if v_isSharedCheck_5437_ == 0 {
                                v___x_5432_ = v___x_5390_;
                                v_isShared_5433_ = v_isSharedCheck_5437_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5430_);
                                crate::leanh::lean_dec(v___x_5390_);
                                v___x_5432_ = crate::leanh::lean_box(0);
                                v_isShared_5433_ = v_isSharedCheck_5437_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_instName_5378_);
                        v_a_5438_ = crate::leanh::lean_ctor_get(v___x_5388_, 0);
                        v_isSharedCheck_5445_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5388_)) as u8;
                        if v_isSharedCheck_5445_ == 0 {
                            v___x_5440_ = v___x_5388_;
                            v_isShared_5441_ = v_isSharedCheck_5445_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5438_);
                            crate::leanh::lean_dec(v___x_5388_);
                            v___x_5440_ = crate::leanh::lean_box(0);
                            v_isShared_5441_ = v_isSharedCheck_5445_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_instName_5378_);
                    v_a_5446_ = crate::leanh::lean_ctor_get(v___x_5384_, 0);
                    v_isSharedCheck_5453_ = (!crate::leanh::lean_is_exclusive(v___x_5384_)) as u8;
                    if v_isSharedCheck_5453_ == 0 {
                        v___x_5448_ = v___x_5384_;
                        v_isShared_5449_ = v_isSharedCheck_5453_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5446_);
                        crate::leanh::lean_dec(v___x_5384_);
                        v___x_5448_ = crate::leanh::lean_box(0);
                        v_isShared_5449_ = v_isSharedCheck_5453_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5408_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5407_, 0, v___x_5403_);
                    v___x_5410_ = v___x_5407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5411_, 0, v___x_5403_);
                    v___x_5410_ = v_reuseFailAlloc_5411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5410_;
            }
            3 => {
                if v_isShared_5417_ == 0 {
                    v___x_5419_ = v___x_5416_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5420_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5420_, 0, v_a_5414_);
                    v___x_5419_ = v_reuseFailAlloc_5420_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5419_;
            }
            5 => {
                if v_isShared_5425_ == 0 {
                    v___x_5427_ = v___x_5424_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5428_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5428_, 0, v_a_5422_);
                    v___x_5427_ = v_reuseFailAlloc_5428_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5427_;
            }
            7 => {
                if v_isShared_5433_ == 0 {
                    v___x_5435_ = v___x_5432_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5436_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5436_, 0, v_a_5430_);
                    v___x_5435_ = v_reuseFailAlloc_5436_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5435_;
            }
            9 => {
                if v_isShared_5441_ == 0 {
                    v___x_5443_ = v___x_5440_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5444_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_a_5438_);
                    v___x_5443_ = v_reuseFailAlloc_5444_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5443_;
            }
            11 => {
                if v_isShared_5449_ == 0 {
                    v___x_5451_ = v___x_5448_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_a_5446_);
                    v___x_5451_ = v_reuseFailAlloc_5452_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___boxed(
    mut v___x_5454_: *mut crate::leanh::LeanObject,
    mut v_thms_5455_: *mut crate::leanh::LeanObject,
    mut v_fieldImpls_5456_: *mut crate::leanh::LeanObject,
    mut v_a_5457_: *mut crate::leanh::LeanObject,
    mut v_instName_5458_: *mut crate::leanh::LeanObject,
    mut v___y_5459_: *mut crate::leanh::LeanObject,
    mut v___y_5460_: *mut crate::leanh::LeanObject,
    mut v___y_5461_: *mut crate::leanh::LeanObject,
    mut v___y_5462_: *mut crate::leanh::LeanObject,
    mut v___y_5463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5464_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0(
        v___x_5454_,
        v_thms_5455_,
        v_fieldImpls_5456_,
        v_a_5457_,
        v_instName_5458_,
        v___y_5459_,
        v___y_5460_,
        v___y_5461_,
        v___y_5462_,
    );
    crate::leanh::lean_dec(v___y_5462_);
    crate::leanh::lean_dec_ref(v___y_5461_);
    crate::leanh::lean_dec(v___y_5460_);
    crate::leanh::lean_dec_ref(v___y_5459_);
    crate::leanh::lean_dec_ref(v_a_5457_);
    crate::leanh::lean_dec_ref(v_fieldImpls_5456_);
    crate::leanh::lean_dec_ref(v_thms_5455_);
    crate::leanh::lean_dec_ref(v___x_5454_);
    return v_res_5464_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(
    mut v___y_5465_: *mut crate::leanh::LeanObject,
    mut v_isExporting_5466_: u8,
    mut v___x_5467_: *mut crate::leanh::LeanObject,
    mut v___y_5468_: *mut crate::leanh::LeanObject,
    mut v___x_5469_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_5470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5483_: u8 = 0;
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5495_: u8 = 0;
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5502_: u8 = 0;
    let mut v_unused_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5505_: u8 = 0;
    let mut v_unused_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5472_ = lean_st_ref_take(v___y_5465_);
                v_env_5473_ = crate::leanh::lean_ctor_get(v___x_5472_, 0);
                v_nextMacroScope_5474_ = crate::leanh::lean_ctor_get(v___x_5472_, 1);
                v_ngen_5475_ = crate::leanh::lean_ctor_get(v___x_5472_, 2);
                v_auxDeclNGen_5476_ = crate::leanh::lean_ctor_get(v___x_5472_, 3);
                v_traceState_5477_ = crate::leanh::lean_ctor_get(v___x_5472_, 4);
                v_messages_5478_ = crate::leanh::lean_ctor_get(v___x_5472_, 6);
                v_infoState_5479_ = crate::leanh::lean_ctor_get(v___x_5472_, 7);
                v_snapshotTasks_5480_ = crate::leanh::lean_ctor_get(v___x_5472_, 8);
                v_isSharedCheck_5505_ = (!crate::leanh::lean_is_exclusive(v___x_5472_)) as u8;
                if v_isSharedCheck_5505_ == 0 {
                    v_unused_5506_ = crate::leanh::lean_ctor_get(v___x_5472_, 5);
                    crate::leanh::lean_dec(v_unused_5506_);
                    v___x_5482_ = v___x_5472_;
                    v_isShared_5483_ = v_isSharedCheck_5505_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5480_);
                    crate::leanh::lean_inc(v_infoState_5479_);
                    crate::leanh::lean_inc(v_messages_5478_);
                    crate::leanh::lean_inc(v_traceState_5477_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5476_);
                    crate::leanh::lean_inc(v_ngen_5475_);
                    crate::leanh::lean_inc(v_nextMacroScope_5474_);
                    crate::leanh::lean_inc(v_env_5473_);
                    crate::leanh::lean_dec(v___x_5472_);
                    v___x_5482_ = crate::leanh::lean_box(0);
                    v_isShared_5483_ = v_isSharedCheck_5505_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5484_ = l_Lean_Environment_setExporting(v_env_5473_, v_isExporting_5466_);
                if v_isShared_5483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5482_, 5, v___x_5467_);
                    crate::leanh::lean_ctor_set(v___x_5482_, 0, v___x_5484_);
                    v___x_5486_ = v___x_5482_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5504_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 0, v___x_5484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 1, v_nextMacroScope_5474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 2, v_ngen_5475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 3, v_auxDeclNGen_5476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 4, v_traceState_5477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 5, v___x_5467_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 6, v_messages_5478_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 7, v_infoState_5479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 8, v_snapshotTasks_5480_);
                    v___x_5486_ = v_reuseFailAlloc_5504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5487_ = lean_st_ref_set(v___y_5465_, v___x_5486_);
                v___x_5488_ = lean_st_ref_take(v___y_5468_);
                v_mctx_5489_ = crate::leanh::lean_ctor_get(v___x_5488_, 0);
                v_zetaDeltaFVarIds_5490_ = crate::leanh::lean_ctor_get(v___x_5488_, 2);
                v_postponed_5491_ = crate::leanh::lean_ctor_get(v___x_5488_, 3);
                v_diag_5492_ = crate::leanh::lean_ctor_get(v___x_5488_, 4);
                v_isSharedCheck_5502_ = (!crate::leanh::lean_is_exclusive(v___x_5488_)) as u8;
                if v_isSharedCheck_5502_ == 0 {
                    v_unused_5503_ = crate::leanh::lean_ctor_get(v___x_5488_, 1);
                    crate::leanh::lean_dec(v_unused_5503_);
                    v___x_5494_ = v___x_5488_;
                    v_isShared_5495_ = v_isSharedCheck_5502_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5492_);
                    crate::leanh::lean_inc(v_postponed_5491_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5490_);
                    crate::leanh::lean_inc(v_mctx_5489_);
                    crate::leanh::lean_dec(v___x_5488_);
                    v___x_5494_ = crate::leanh::lean_box(0);
                    v_isShared_5495_ = v_isSharedCheck_5502_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5495_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5494_, 1, v___x_5469_);
                    v___x_5497_ = v___x_5494_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5501_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_mctx_5489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5501_, 1, v___x_5469_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5501_,
                        2,
                        v_zetaDeltaFVarIds_5490_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5501_, 3, v_postponed_5491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5501_, 4, v_diag_5492_);
                    v___x_5497_ = v_reuseFailAlloc_5501_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5498_ = lean_st_ref_set(v___y_5468_, v___x_5497_);
                v___x_5499_ = crate::leanh::lean_box(0);
                v___x_5500_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5500_, 0, v___x_5499_);
                return v___x_5500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0___boxed(
    mut v___y_5507_: *mut crate::leanh::LeanObject,
    mut v_isExporting_5508_: *mut crate::leanh::LeanObject,
    mut v___x_5509_: *mut crate::leanh::LeanObject,
    mut v___y_5510_: *mut crate::leanh::LeanObject,
    mut v___x_5511_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_5512_: *mut crate::leanh::LeanObject,
    mut v___y_5513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_5514_: u8 = 0;
    let mut v_res_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_5514_ = (crate::leanh::lean_unbox(v_isExporting_5508_) as u8);
    v_res_5515_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(v___y_5507_, v_isExporting_boxed_5514_, v___x_5509_, v___y_5510_, v___x_5511_, v_a_x3f_5512_);
    crate::leanh::lean_dec(v_a_x3f_5512_);
    crate::leanh::lean_dec(v___y_5510_);
    crate::leanh::lean_dec(v___y_5507_);
    return v_res_5515_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5516_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5516_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5517_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0);
    v___x_5518_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5518_, 0, v___x_5517_);
    return v___x_5518_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5519_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1);
    v___x_5520_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5520_, 0, v___x_5519_);
    crate::leanh::lean_ctor_set(v___x_5520_, 1, v___x_5519_);
    return v___x_5520_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5521_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1);
    v___x_5522_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5522_, 0, v___x_5521_);
    crate::leanh::lean_ctor_set(v___x_5522_, 1, v___x_5521_);
    crate::leanh::lean_ctor_set(v___x_5522_, 2, v___x_5521_);
    crate::leanh::lean_ctor_set(v___x_5522_, 3, v___x_5521_);
    crate::leanh::lean_ctor_set(v___x_5522_, 4, v___x_5521_);
    crate::leanh::lean_ctor_set(v___x_5522_, 5, v___x_5521_);
    return v___x_5522_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(
    mut v_x_5523_: *mut crate::leanh::LeanObject,
    mut v_isExporting_5524_: u8,
    mut v___y_5525_: *mut crate::leanh::LeanObject,
    mut v___y_5526_: *mut crate::leanh::LeanObject,
    mut v___y_5527_: *mut crate::leanh::LeanObject,
    mut v___y_5528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_5532_: u8 = 0;
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5544_: u8 = 0;
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5557_: u8 = 0;
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5566_: u8 = 0;
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5572_: u8 = 0;
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5576_: u8 = 0;
    let mut v_unused_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5579_: u8 = 0;
    let mut v_a_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5585_: u8 = 0;
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5589_: u8 = 0;
    let mut v_unused_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5592_: u8 = 0;
    let mut v_unused_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5595_: u8 = 0;
    let mut v_unused_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5530_ = lean_st_ref_get(v___y_5528_);
                v_env_5531_ = crate::leanh::lean_ctor_get(v___x_5530_, 0);
                crate::leanh::lean_inc_ref(v_env_5531_);
                crate::leanh::lean_dec(v___x_5530_);
                v_isExporting_5532_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_5531_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_5531_);
                v___x_5533_ = lean_st_ref_take(v___y_5528_);
                v_env_5534_ = crate::leanh::lean_ctor_get(v___x_5533_, 0);
                v_nextMacroScope_5535_ = crate::leanh::lean_ctor_get(v___x_5533_, 1);
                v_ngen_5536_ = crate::leanh::lean_ctor_get(v___x_5533_, 2);
                v_auxDeclNGen_5537_ = crate::leanh::lean_ctor_get(v___x_5533_, 3);
                v_traceState_5538_ = crate::leanh::lean_ctor_get(v___x_5533_, 4);
                v_messages_5539_ = crate::leanh::lean_ctor_get(v___x_5533_, 6);
                v_infoState_5540_ = crate::leanh::lean_ctor_get(v___x_5533_, 7);
                v_snapshotTasks_5541_ = crate::leanh::lean_ctor_get(v___x_5533_, 8);
                v_isSharedCheck_5595_ = (!crate::leanh::lean_is_exclusive(v___x_5533_)) as u8;
                if v_isSharedCheck_5595_ == 0 {
                    v_unused_5596_ = crate::leanh::lean_ctor_get(v___x_5533_, 5);
                    crate::leanh::lean_dec(v_unused_5596_);
                    v___x_5543_ = v___x_5533_;
                    v_isShared_5544_ = v_isSharedCheck_5595_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5541_);
                    crate::leanh::lean_inc(v_infoState_5540_);
                    crate::leanh::lean_inc(v_messages_5539_);
                    crate::leanh::lean_inc(v_traceState_5538_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5537_);
                    crate::leanh::lean_inc(v_ngen_5536_);
                    crate::leanh::lean_inc(v_nextMacroScope_5535_);
                    crate::leanh::lean_inc(v_env_5534_);
                    crate::leanh::lean_dec(v___x_5533_);
                    v___x_5543_ = crate::leanh::lean_box(0);
                    v_isShared_5544_ = v_isSharedCheck_5595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5545_ = l_Lean_Environment_setExporting(v_env_5534_, v_isExporting_5524_);
                v___x_5546_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2);
                if v_isShared_5544_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5543_, 5, v___x_5546_);
                    crate::leanh::lean_ctor_set(v___x_5543_, 0, v___x_5545_);
                    v___x_5548_ = v___x_5543_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5594_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5545_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 1, v_nextMacroScope_5535_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 2, v_ngen_5536_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 3, v_auxDeclNGen_5537_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 4, v_traceState_5538_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 5, v___x_5546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 6, v_messages_5539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 7, v_infoState_5540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 8, v_snapshotTasks_5541_);
                    v___x_5548_ = v_reuseFailAlloc_5594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5549_ = lean_st_ref_set(v___y_5528_, v___x_5548_);
                v___x_5550_ = lean_st_ref_take(v___y_5526_);
                v_mctx_5551_ = crate::leanh::lean_ctor_get(v___x_5550_, 0);
                v_zetaDeltaFVarIds_5552_ = crate::leanh::lean_ctor_get(v___x_5550_, 2);
                v_postponed_5553_ = crate::leanh::lean_ctor_get(v___x_5550_, 3);
                v_diag_5554_ = crate::leanh::lean_ctor_get(v___x_5550_, 4);
                v_isSharedCheck_5592_ = (!crate::leanh::lean_is_exclusive(v___x_5550_)) as u8;
                if v_isSharedCheck_5592_ == 0 {
                    v_unused_5593_ = crate::leanh::lean_ctor_get(v___x_5550_, 1);
                    crate::leanh::lean_dec(v_unused_5593_);
                    v___x_5556_ = v___x_5550_;
                    v_isShared_5557_ = v_isSharedCheck_5592_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5554_);
                    crate::leanh::lean_inc(v_postponed_5553_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5552_);
                    crate::leanh::lean_inc(v_mctx_5551_);
                    crate::leanh::lean_dec(v___x_5550_);
                    v___x_5556_ = crate::leanh::lean_box(0);
                    v_isShared_5557_ = v_isSharedCheck_5592_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5558_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3);
                if v_isShared_5557_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5556_, 1, v___x_5558_);
                    v___x_5560_ = v___x_5556_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5591_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_mctx_5551_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5591_, 1, v___x_5558_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5591_,
                        2,
                        v_zetaDeltaFVarIds_5552_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5591_, 3, v_postponed_5553_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5591_, 4, v_diag_5554_);
                    v___x_5560_ = v_reuseFailAlloc_5591_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5561_ = lean_st_ref_set(v___y_5526_, v___x_5560_);
                crate::leanh::lean_inc(v___y_5528_);
                crate::leanh::lean_inc_ref(v___y_5527_);
                crate::leanh::lean_inc(v___y_5526_);
                crate::leanh::lean_inc_ref(v___y_5525_);
                v_r_5562_ = crate::leanh::lean_apply_5(
                    v_x_5523_,
                    v___y_5525_,
                    v___y_5526_,
                    v___y_5527_,
                    v___y_5528_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_5562_) == 0 {
                    v_a_5563_ = crate::leanh::lean_ctor_get(v_r_5562_, 0);
                    v_isSharedCheck_5579_ = (!crate::leanh::lean_is_exclusive(v_r_5562_)) as u8;
                    if v_isSharedCheck_5579_ == 0 {
                        v___x_5565_ = v_r_5562_;
                        v_isShared_5566_ = v_isSharedCheck_5579_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5563_);
                        crate::leanh::lean_dec(v_r_5562_);
                        v___x_5565_ = crate::leanh::lean_box(0);
                        v_isShared_5566_ = v_isSharedCheck_5579_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_5580_ = crate::leanh::lean_ctor_get(v_r_5562_, 0);
                    crate::leanh::lean_inc(v_a_5580_);
                    crate::leanh::lean_dec_ref_known(v_r_5562_, 1);
                    v___x_5581_ = crate::leanh::lean_box(0);
                    v___x_5582_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(v___y_5528_, v_isExporting_5532_, v___x_5546_, v___y_5526_, v___x_5558_, v___x_5581_);
                    v_isSharedCheck_5589_ = (!crate::leanh::lean_is_exclusive(v___x_5582_)) as u8;
                    if v_isSharedCheck_5589_ == 0 {
                        v_unused_5590_ = crate::leanh::lean_ctor_get(v___x_5582_, 0);
                        crate::leanh::lean_dec(v_unused_5590_);
                        v___x_5584_ = v___x_5582_;
                        v_isShared_5585_ = v_isSharedCheck_5589_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5582_);
                        v___x_5584_ = crate::leanh::lean_box(0);
                        v_isShared_5585_ = v_isSharedCheck_5589_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_5563_);
                if v_isShared_5566_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5565_, 1);
                    v___x_5568_ = v___x_5565_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5578_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_a_5563_);
                    v___x_5568_ = v_reuseFailAlloc_5578_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5569_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(v___y_5528_, v_isExporting_5532_, v___x_5546_, v___y_5526_, v___x_5558_, v___x_5568_);
                crate::leanh::lean_dec_ref(v___x_5568_);
                v_isSharedCheck_5576_ = (!crate::leanh::lean_is_exclusive(v___x_5569_)) as u8;
                if v_isSharedCheck_5576_ == 0 {
                    v_unused_5577_ = crate::leanh::lean_ctor_get(v___x_5569_, 0);
                    crate::leanh::lean_dec(v_unused_5577_);
                    v___x_5571_ = v___x_5569_;
                    v_isShared_5572_ = v_isSharedCheck_5576_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_5569_);
                    v___x_5571_ = crate::leanh::lean_box(0);
                    v_isShared_5572_ = v_isSharedCheck_5576_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5572_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5571_, 0, v_a_5563_);
                    v___x_5574_ = v___x_5571_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5575_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_a_5563_);
                    v___x_5574_ = v_reuseFailAlloc_5575_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5574_;
            }
            9 => {
                if v_isShared_5585_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5584_, 1);
                    crate::leanh::lean_ctor_set(v___x_5584_, 0, v_a_5580_);
                    v___x_5587_ = v___x_5584_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5588_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_a_5580_);
                    v___x_5587_ = v_reuseFailAlloc_5588_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___boxed(
    mut v_x_5597_: *mut crate::leanh::LeanObject,
    mut v_isExporting_5598_: *mut crate::leanh::LeanObject,
    mut v___y_5599_: *mut crate::leanh::LeanObject,
    mut v___y_5600_: *mut crate::leanh::LeanObject,
    mut v___y_5601_: *mut crate::leanh::LeanObject,
    mut v___y_5602_: *mut crate::leanh::LeanObject,
    mut v___y_5603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_5604_: u8 = 0;
    let mut v_res_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_5604_ = (crate::leanh::lean_unbox(v_isExporting_5598_) as u8);
    v_res_5605_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(v_x_5597_, v_isExporting_boxed_5604_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_);
    crate::leanh::lean_dec(v___y_5602_);
    crate::leanh::lean_dec_ref(v___y_5601_);
    crate::leanh::lean_dec(v___y_5600_);
    crate::leanh::lean_dec_ref(v___y_5599_);
    return v_res_5605_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(
    mut v_x_5606_: *mut crate::leanh::LeanObject,
    mut v_when_5607_: u8,
    mut v___y_5608_: *mut crate::leanh::LeanObject,
    mut v___y_5609_: *mut crate::leanh::LeanObject,
    mut v___y_5610_: *mut crate::leanh::LeanObject,
    mut v___y_5611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_when_5607_ == 0 {
        let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v___y_5611_);
        crate::leanh::lean_inc_ref(v___y_5610_);
        crate::leanh::lean_inc(v___y_5609_);
        crate::leanh::lean_inc_ref(v___y_5608_);
        v___x_5613_ = crate::leanh::lean_apply_5(
            v_x_5606_,
            v___y_5608_,
            v___y_5609_,
            v___y_5610_,
            v___y_5611_,
            crate::leanh::lean_box(0),
        );
        return v___x_5613_;
    } else {
        let mut v___x_5614_: u8 = 0;
        let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5614_ = 0;
        v___x_5615_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(v_x_5606_, v___x_5614_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_);
        return v___x_5615_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg___boxed(
    mut v_x_5616_: *mut crate::leanh::LeanObject,
    mut v_when_5617_: *mut crate::leanh::LeanObject,
    mut v___y_5618_: *mut crate::leanh::LeanObject,
    mut v___y_5619_: *mut crate::leanh::LeanObject,
    mut v___y_5620_: *mut crate::leanh::LeanObject,
    mut v___y_5621_: *mut crate::leanh::LeanObject,
    mut v___y_5622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_5623_: u8 = 0;
    let mut v_res_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_5623_ = (crate::leanh::lean_unbox(v_when_5617_) as u8);
    v_res_5624_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(v_x_5616_, v_when_boxed_5623_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
    crate::leanh::lean_dec(v___y_5621_);
    crate::leanh::lean_dec_ref(v___y_5620_);
    crate::leanh::lean_dec(v___y_5619_);
    crate::leanh::lean_dec_ref(v___y_5618_);
    return v_res_5624_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize(
    mut v_instName_5625_: *mut crate::leanh::LeanObject,
    mut v_a_5626_: *mut crate::leanh::LeanObject,
    mut v_a_5627_: *mut crate::leanh::LeanObject,
    mut v_a_5628_: *mut crate::leanh::LeanObject,
    mut v_a_5629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_privateSpecs_5633_: u8 = 0;
    let mut v_fieldImpls_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thms_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_instName_5625_);
                v___x_5631_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(
                    v_instName_5625_,
                    v_a_5626_,
                    v_a_5627_,
                    v_a_5628_,
                    v_a_5629_,
                );
                if crate::leanh::lean_obj_tag(v___x_5631_) == 0 {
                    v_a_5632_ = crate::leanh::lean_ctor_get(v___x_5631_, 0);
                    crate::leanh::lean_inc(v_a_5632_);
                    crate::leanh::lean_dec_ref_known(v___x_5631_, 1);
                    v_privateSpecs_5633_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5632_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_fieldImpls_5634_ = crate::leanh::lean_ctor_get(v_a_5632_, 1);
                    crate::leanh::lean_inc_ref(v_fieldImpls_5634_);
                    v_thms_5635_ = crate::leanh::lean_ctor_get(v_a_5632_, 2);
                    crate::leanh::lean_inc_ref(v_thms_5635_);
                    v___x_5636_ =
                        l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsSimpExtension;
                    v___f_5637_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                    crate::leanh::lean_closure_set(v___f_5637_, 0, v___x_5636_);
                    crate::leanh::lean_closure_set(v___f_5637_, 1, v_thms_5635_);
                    crate::leanh::lean_closure_set(v___f_5637_, 2, v_fieldImpls_5634_);
                    crate::leanh::lean_closure_set(v___f_5637_, 3, v_a_5632_);
                    crate::leanh::lean_closure_set(v___f_5637_, 4, v_instName_5625_);
                    v___x_5638_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(v___f_5637_, v_privateSpecs_5633_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_);
                    return v___x_5638_;
                } else {
                    crate::leanh::lean_dec(v_instName_5625_);
                    v_a_5639_ = crate::leanh::lean_ctor_get(v___x_5631_, 0);
                    v_isSharedCheck_5646_ = (!crate::leanh::lean_is_exclusive(v___x_5631_)) as u8;
                    if v_isSharedCheck_5646_ == 0 {
                        v___x_5641_ = v___x_5631_;
                        v_isShared_5642_ = v_isSharedCheck_5646_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5639_);
                        crate::leanh::lean_dec(v___x_5631_);
                        v___x_5641_ = crate::leanh::lean_box(0);
                        v_isShared_5642_ = v_isSharedCheck_5646_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5642_ == 0 {
                    v___x_5644_ = v___x_5641_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
                    v___x_5644_ = v_reuseFailAlloc_5645_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___boxed(
    mut v_instName_5647_: *mut crate::leanh::LeanObject,
    mut v_a_5648_: *mut crate::leanh::LeanObject,
    mut v_a_5649_: *mut crate::leanh::LeanObject,
    mut v_a_5650_: *mut crate::leanh::LeanObject,
    mut v_a_5651_: *mut crate::leanh::LeanObject,
    mut v_a_5652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5653_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize(
        v_instName_5647_,
        v_a_5648_,
        v_a_5649_,
        v_a_5650_,
        v_a_5651_,
    );
    crate::leanh::lean_dec(v_a_5651_);
    crate::leanh::lean_dec_ref(v_a_5650_);
    crate::leanh::lean_dec(v_a_5649_);
    crate::leanh::lean_dec_ref(v_a_5648_);
    return v_res_5653_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3(
    mut v_00_u03b1_5654_: *mut crate::leanh::LeanObject,
    mut v_x_5655_: *mut crate::leanh::LeanObject,
    mut v_isExporting_5656_: u8,
    mut v___y_5657_: *mut crate::leanh::LeanObject,
    mut v___y_5658_: *mut crate::leanh::LeanObject,
    mut v___y_5659_: *mut crate::leanh::LeanObject,
    mut v___y_5660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5662_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(v_x_5655_, v_isExporting_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_);
    return v___x_5662_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___boxed(
    mut v_00_u03b1_5663_: *mut crate::leanh::LeanObject,
    mut v_x_5664_: *mut crate::leanh::LeanObject,
    mut v_isExporting_5665_: *mut crate::leanh::LeanObject,
    mut v___y_5666_: *mut crate::leanh::LeanObject,
    mut v___y_5667_: *mut crate::leanh::LeanObject,
    mut v___y_5668_: *mut crate::leanh::LeanObject,
    mut v___y_5669_: *mut crate::leanh::LeanObject,
    mut v___y_5670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_5671_: u8 = 0;
    let mut v_res_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_5671_ = (crate::leanh::lean_unbox(v_isExporting_5665_) as u8);
    v_res_5672_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3(v_00_u03b1_5663_, v_x_5664_, v_isExporting_boxed_5671_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_);
    crate::leanh::lean_dec(v___y_5669_);
    crate::leanh::lean_dec_ref(v___y_5668_);
    crate::leanh::lean_dec(v___y_5667_);
    crate::leanh::lean_dec_ref(v___y_5666_);
    return v_res_5672_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3(
    mut v_00_u03b1_5673_: *mut crate::leanh::LeanObject,
    mut v_x_5674_: *mut crate::leanh::LeanObject,
    mut v_when_5675_: u8,
    mut v___y_5676_: *mut crate::leanh::LeanObject,
    mut v___y_5677_: *mut crate::leanh::LeanObject,
    mut v___y_5678_: *mut crate::leanh::LeanObject,
    mut v___y_5679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5681_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(v_x_5674_, v_when_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_);
    return v___x_5681_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___boxed(
    mut v_00_u03b1_5682_: *mut crate::leanh::LeanObject,
    mut v_x_5683_: *mut crate::leanh::LeanObject,
    mut v_when_5684_: *mut crate::leanh::LeanObject,
    mut v___y_5685_: *mut crate::leanh::LeanObject,
    mut v___y_5686_: *mut crate::leanh::LeanObject,
    mut v___y_5687_: *mut crate::leanh::LeanObject,
    mut v___y_5688_: *mut crate::leanh::LeanObject,
    mut v___y_5689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_5690_: u8 = 0;
    let mut v_res_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_5690_ = (crate::leanh::lean_unbox(v_when_5684_) as u8);
    v_res_5691_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3(v_00_u03b1_5682_, v_x_5683_, v_when_boxed_5690_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_);
    crate::leanh::lean_dec(v___y_5688_);
    crate::leanh::lean_dec_ref(v___y_5687_);
    crate::leanh::lean_dec(v___y_5686_);
    crate::leanh::lean_dec_ref(v___y_5685_);
    return v_res_5691_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(
    mut v_instName_5694_: *mut crate::leanh::LeanObject,
    mut v_a_5695_: *mut crate::leanh::LeanObject,
    mut v_a_5696_: *mut crate::leanh::LeanObject,
    mut v_a_5697_: *mut crate::leanh::LeanObject,
    mut v_a_5698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_privateSpecs_5705_: u8 = 0;
    let mut v_fieldImpls_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: u8 = 0;
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5720_: u8 = 0;
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5700_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0;
                crate::leanh::lean_inc(v_instName_5694_);
                v___x_5701_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(
                    v_instName_5694_,
                    v_a_5695_,
                    v_a_5696_,
                    v_a_5697_,
                    v_a_5698_,
                );
                if crate::leanh::lean_obj_tag(v___x_5701_) == 0 {
                    v_a_5702_ = crate::leanh::lean_ctor_get(v___x_5701_, 0);
                    crate::leanh::lean_inc(v_a_5702_);
                    crate::leanh::lean_dec_ref_known(v___x_5701_, 1);
                    v___x_5703_ = lean_st_ref_get(v_a_5698_);
                    v_env_5704_ = crate::leanh::lean_ctor_get(v___x_5703_, 0);
                    crate::leanh::lean_inc_ref(v_env_5704_);
                    crate::leanh::lean_dec(v___x_5703_);
                    v_privateSpecs_5705_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5702_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_fieldImpls_5706_ = crate::leanh::lean_ctor_get(v_a_5702_, 1);
                    crate::leanh::lean_inc_ref(v_fieldImpls_5706_);
                    crate::leanh::lean_dec(v_a_5702_);
                    v___x_5707_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5708_ = lean_array_get(v___x_5700_, v_fieldImpls_5706_, v___x_5707_);
                    crate::leanh::lean_dec_ref(v_fieldImpls_5706_);
                    v_fst_5709_ = crate::leanh::lean_ctor_get(v___x_5708_, 0);
                    crate::leanh::lean_inc(v_fst_5709_);
                    crate::leanh::lean_dec(v___x_5708_);
                    v___x_5710_ = 1;
                    v___x_5711_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_fst_5709_,
                        v___x_5710_,
                    );
                    v___x_5712_ =
                        l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0;
                    v___x_5713_ = lean_string_append(v___x_5711_, v___x_5712_);
                    crate::leanh::lean_inc_n(v_instName_5694_, 2);
                    v___x_5714_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                        v_env_5704_,
                        v_instName_5694_,
                        v_privateSpecs_5705_,
                        v___x_5713_,
                    );
                    crate::leanh::lean_dec_ref(v_env_5704_);
                    v___x_5715_ = crate::leanh::lean_alloc_closure(
                        l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___boxed
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_5715_, 0, v_instName_5694_);
                    v___x_5716_ = l_Lean_Meta_realizeConst(
                        v_instName_5694_,
                        v___x_5714_,
                        v___x_5715_,
                        v_a_5695_,
                        v_a_5696_,
                        v_a_5697_,
                        v_a_5698_,
                    );
                    return v___x_5716_;
                } else {
                    crate::leanh::lean_dec(v_instName_5694_);
                    v_a_5717_ = crate::leanh::lean_ctor_get(v___x_5701_, 0);
                    v_isSharedCheck_5724_ = (!crate::leanh::lean_is_exclusive(v___x_5701_)) as u8;
                    if v_isSharedCheck_5724_ == 0 {
                        v___x_5719_ = v___x_5701_;
                        v_isShared_5720_ = v_isSharedCheck_5724_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5717_);
                        crate::leanh::lean_dec(v___x_5701_);
                        v___x_5719_ = crate::leanh::lean_box(0);
                        v_isShared_5720_ = v_isSharedCheck_5724_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5720_ == 0 {
                    v___x_5722_ = v___x_5719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_a_5717_);
                    v___x_5722_ = v_reuseFailAlloc_5723_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___boxed(
    mut v_instName_5725_: *mut crate::leanh::LeanObject,
    mut v_a_5726_: *mut crate::leanh::LeanObject,
    mut v_a_5727_: *mut crate::leanh::LeanObject,
    mut v_a_5728_: *mut crate::leanh::LeanObject,
    mut v_a_5729_: *mut crate::leanh::LeanObject,
    mut v_a_5730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5731_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(
        v_instName_5725_,
        v_a_5726_,
        v_a_5727_,
        v_a_5728_,
        v_a_5729_,
    );
    crate::leanh::lean_dec(v_a_5729_);
    crate::leanh::lean_dec_ref(v_a_5728_);
    crate::leanh::lean_dec(v_a_5727_);
    crate::leanh::lean_dec_ref(v_a_5726_);
    return v_res_5731_;
}
pub unsafe fn l_Lean_getMethodSpecTheorem___redArg(
    mut v_instName_5732_: *mut crate::leanh::LeanObject,
    mut v_op_5733_: *mut crate::leanh::LeanObject,
    mut v_a_5734_: *mut crate::leanh::LeanObject,
    mut v_a_5735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5745_: u8 = 0;
    let mut v_privateSpecs_5746_: u8 = 0;
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5754_: u8 = 0;
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5761_: u8 = 0;
    let mut v_a_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5765_: u8 = 0;
    let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5769_: u8 = 0;
    let mut v_isSharedCheck_5770_: u8 = 0;
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5737_ = lean_st_ref_get(v_a_5735_);
                v_env_5738_ = crate::leanh::lean_ctor_get(v___x_5737_, 0);
                crate::leanh::lean_inc_ref_n(v_env_5738_, 2);
                crate::leanh::lean_dec(v___x_5737_);
                v___x_5739_ = l_Lean_instInhabitedMethodSpecsAttrData_default;
                v___x_5740_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
                crate::leanh::lean_inc(v_instName_5732_);
                v___x_5741_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
                    v___x_5739_,
                    v___x_5740_,
                    v_env_5738_,
                    v_instName_5732_,
                );
                if crate::leanh::lean_obj_tag(v___x_5741_) == 1 {
                    v_val_5742_ = crate::leanh::lean_ctor_get(v___x_5741_, 0);
                    v_isSharedCheck_5770_ = (!crate::leanh::lean_is_exclusive(v___x_5741_)) as u8;
                    if v_isSharedCheck_5770_ == 0 {
                        v___x_5744_ = v___x_5741_;
                        v_isShared_5745_ = v_isSharedCheck_5770_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5742_);
                        crate::leanh::lean_dec(v___x_5741_);
                        v___x_5744_ = crate::leanh::lean_box(0);
                        v_isShared_5745_ = v_isSharedCheck_5770_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5741_);
                    crate::leanh::lean_dec_ref(v_env_5738_);
                    crate::leanh::lean_dec_ref(v_op_5733_);
                    crate::leanh::lean_dec(v_instName_5732_);
                    v___x_5771_ = crate::leanh::lean_box(0);
                    v___x_5772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5772_, 0, v___x_5771_);
                    return v___x_5772_;
                }
            }
            1 => {
                v_privateSpecs_5746_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_5742_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec(v_val_5742_);
                v___x_5747_ =
                    l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0;
                v___x_5748_ = lean_string_append(v_op_5733_, v___x_5747_);
                v___x_5749_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                    v_env_5738_,
                    v_instName_5732_,
                    v_privateSpecs_5746_,
                    v___x_5748_,
                );
                crate::leanh::lean_dec_ref(v_env_5738_);
                v___x_5750_ =
                    l_Lean_realizeGlobalConstNoOverloadCore(v___x_5749_, v_a_5734_, v_a_5735_);
                if crate::leanh::lean_obj_tag(v___x_5750_) == 0 {
                    v_a_5751_ = crate::leanh::lean_ctor_get(v___x_5750_, 0);
                    v_isSharedCheck_5761_ = (!crate::leanh::lean_is_exclusive(v___x_5750_)) as u8;
                    if v_isSharedCheck_5761_ == 0 {
                        v___x_5753_ = v___x_5750_;
                        v_isShared_5754_ = v_isSharedCheck_5761_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5751_);
                        crate::leanh::lean_dec(v___x_5750_);
                        v___x_5753_ = crate::leanh::lean_box(0);
                        v_isShared_5754_ = v_isSharedCheck_5761_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5744_);
                    v_a_5762_ = crate::leanh::lean_ctor_get(v___x_5750_, 0);
                    v_isSharedCheck_5769_ = (!crate::leanh::lean_is_exclusive(v___x_5750_)) as u8;
                    if v_isSharedCheck_5769_ == 0 {
                        v___x_5764_ = v___x_5750_;
                        v_isShared_5765_ = v_isSharedCheck_5769_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5762_);
                        crate::leanh::lean_dec(v___x_5750_);
                        v___x_5764_ = crate::leanh::lean_box(0);
                        v_isShared_5765_ = v_isSharedCheck_5769_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5745_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5744_, 0, v_a_5751_);
                    v___x_5756_ = v___x_5744_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5760_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5760_, 0, v_a_5751_);
                    v___x_5756_ = v_reuseFailAlloc_5760_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5754_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5753_, 0, v___x_5756_);
                    v___x_5758_ = v___x_5753_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5759_, 0, v___x_5756_);
                    v___x_5758_ = v_reuseFailAlloc_5759_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5758_;
            }
            5 => {
                if v_isShared_5765_ == 0 {
                    v___x_5767_ = v___x_5764_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5768_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_a_5762_);
                    v___x_5767_ = v_reuseFailAlloc_5768_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getMethodSpecTheorem___redArg___boxed(
    mut v_instName_5773_: *mut crate::leanh::LeanObject,
    mut v_op_5774_: *mut crate::leanh::LeanObject,
    mut v_a_5775_: *mut crate::leanh::LeanObject,
    mut v_a_5776_: *mut crate::leanh::LeanObject,
    mut v_a_5777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5778_ =
        l_Lean_getMethodSpecTheorem___redArg(v_instName_5773_, v_op_5774_, v_a_5775_, v_a_5776_);
    crate::leanh::lean_dec(v_a_5776_);
    crate::leanh::lean_dec_ref(v_a_5775_);
    return v_res_5778_;
}
pub unsafe fn l_Lean_getMethodSpecTheorem(
    mut v_instName_5779_: *mut crate::leanh::LeanObject,
    mut v_op_5780_: *mut crate::leanh::LeanObject,
    mut v_a_5781_: *mut crate::leanh::LeanObject,
    mut v_a_5782_: *mut crate::leanh::LeanObject,
    mut v_a_5783_: *mut crate::leanh::LeanObject,
    mut v_a_5784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5786_ =
        l_Lean_getMethodSpecTheorem___redArg(v_instName_5779_, v_op_5780_, v_a_5783_, v_a_5784_);
    return v___x_5786_;
}
pub unsafe fn l_Lean_getMethodSpecTheorem___boxed(
    mut v_instName_5787_: *mut crate::leanh::LeanObject,
    mut v_op_5788_: *mut crate::leanh::LeanObject,
    mut v_a_5789_: *mut crate::leanh::LeanObject,
    mut v_a_5790_: *mut crate::leanh::LeanObject,
    mut v_a_5791_: *mut crate::leanh::LeanObject,
    mut v_a_5792_: *mut crate::leanh::LeanObject,
    mut v_a_5793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5794_ = l_Lean_getMethodSpecTheorem(
        v_instName_5787_,
        v_op_5788_,
        v_a_5789_,
        v_a_5790_,
        v_a_5791_,
        v_a_5792_,
    );
    crate::leanh::lean_dec(v_a_5792_);
    crate::leanh::lean_dec_ref(v_a_5791_);
    crate::leanh::lean_dec(v_a_5790_);
    crate::leanh::lean_dec_ref(v_a_5789_);
    return v_res_5794_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0___redArg(
    mut v_op_5795_: *mut crate::leanh::LeanObject,
    mut v_instName_5796_: *mut crate::leanh::LeanObject,
    mut v___x_5797_: u8,
    mut v___x_5798_: *mut crate::leanh::LeanObject,
    mut v_a_5799_: *mut crate::leanh::LeanObject,
    mut v___y_5800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5807_: u8 = 0;
    let mut v_env_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: u8 = 0;
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5826_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5802_ = lean_st_ref_get(v___y_5800_);
                v_fst_5803_ = crate::leanh::lean_ctor_get(v_a_5799_, 0);
                v_snd_5804_ = crate::leanh::lean_ctor_get(v_a_5799_, 1);
                v_isSharedCheck_5826_ = (!crate::leanh::lean_is_exclusive(v_a_5799_)) as u8;
                if v_isSharedCheck_5826_ == 0 {
                    v___x_5806_ = v_a_5799_;
                    v_isShared_5807_ = v_isSharedCheck_5826_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5804_);
                    crate::leanh::lean_inc(v_fst_5803_);
                    crate::leanh::lean_dec(v_a_5799_);
                    v___x_5806_ = crate::leanh::lean_box(0);
                    v_isShared_5807_ = v_isSharedCheck_5826_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_env_5808_ = crate::leanh::lean_ctor_get(v___x_5802_, 0);
                crate::leanh::lean_inc_ref(v_env_5808_);
                crate::leanh::lean_dec(v___x_5802_);
                v___x_5809_ =
                    l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1;
                crate::leanh::lean_inc_ref(v_op_5795_);
                v___x_5810_ = lean_string_append(v_op_5795_, v___x_5809_);
                v___x_5811_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5812_ = lean_nat_add(v_fst_5803_, v___x_5811_);
                crate::leanh::lean_inc(v___x_5812_);
                v___x_5813_ = l_Nat_reprFast(v___x_5812_);
                v___x_5814_ = lean_string_append(v___x_5810_, v___x_5813_);
                crate::leanh::lean_dec_ref(v___x_5813_);
                crate::leanh::lean_inc(v_instName_5796_);
                v___x_5815_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                    v_env_5808_,
                    v_instName_5796_,
                    v___x_5797_,
                    v___x_5814_,
                );
                crate::leanh::lean_dec_ref(v_env_5808_);
                v___x_5816_ = l_Lean_Environment_containsOnBranch(v___x_5798_, v___x_5815_);
                if v___x_5816_ == 0 {
                    crate::leanh::lean_dec(v___x_5815_);
                    crate::leanh::lean_dec(v___x_5812_);
                    crate::leanh::lean_dec(v_instName_5796_);
                    crate::leanh::lean_dec_ref(v_op_5795_);
                    if v_isShared_5807_ == 0 {
                        v___x_5818_ = v___x_5806_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5820_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5820_, 0, v_fst_5803_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5820_, 1, v_snd_5804_);
                        v___x_5818_ = v_reuseFailAlloc_5820_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_5803_);
                    v___x_5821_ = lean_array_push(v_snd_5804_, v___x_5815_);
                    if v_isShared_5807_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5806_, 1, v___x_5821_);
                        crate::leanh::lean_ctor_set(v___x_5806_, 0, v___x_5812_);
                        v___x_5823_ = v___x_5806_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5825_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5825_, 0, v___x_5812_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5825_, 1, v___x_5821_);
                        v___x_5823_ = v_reuseFailAlloc_5825_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5819_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5819_, 0, v___x_5818_);
                return v___x_5819_;
            }
            3 => {
                v_a_5799_ = v___x_5823_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0___redArg___boxed(
    mut v_op_5827_: *mut crate::leanh::LeanObject,
    mut v_instName_5828_: *mut crate::leanh::LeanObject,
    mut v___x_5829_: *mut crate::leanh::LeanObject,
    mut v___x_5830_: *mut crate::leanh::LeanObject,
    mut v_a_5831_: *mut crate::leanh::LeanObject,
    mut v___y_5832_: *mut crate::leanh::LeanObject,
    mut v___y_5833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2216__boxed_5834_: u8 = 0;
    let mut v_res_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2216__boxed_5834_ = (crate::leanh::lean_unbox(v___x_5829_) as u8);
    v_res_5835_ = l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0___redArg(v_op_5827_, v_instName_5828_, v___x_2216__boxed_5834_, v___x_5830_, v_a_5831_, v___y_5832_);
    crate::leanh::lean_dec(v___y_5832_);
    crate::leanh::lean_dec_ref(v___x_5830_);
    return v_res_5835_;
}
pub unsafe fn l_Lean_getMethodSpecTheorems(
    mut v_instName_5841_: *mut crate::leanh::LeanObject,
    mut v_op_5842_: *mut crate::leanh::LeanObject,
    mut v_a_5843_: *mut crate::leanh::LeanObject,
    mut v_a_5844_: *mut crate::leanh::LeanObject,
    mut v_a_5845_: *mut crate::leanh::LeanObject,
    mut v_a_5846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5856_: u8 = 0;
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_privateSpecs_5859_: u8 = 0;
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5871_: u8 = 0;
    let mut v_snd_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5879_: u8 = 0;
    let mut v_a_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5883_: u8 = 0;
    let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5887_: u8 = 0;
    let mut v_a_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5891_: u8 = 0;
    let mut v___x_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5895_: u8 = 0;
    let mut v_isSharedCheck_5896_: u8 = 0;
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5848_ = lean_st_ref_get(v_a_5846_);
                v_env_5849_ = crate::leanh::lean_ctor_get(v___x_5848_, 0);
                crate::leanh::lean_inc_ref(v_env_5849_);
                crate::leanh::lean_dec(v___x_5848_);
                v___x_5850_ = l_Lean_instInhabitedMethodSpecsAttrData_default;
                v___x_5851_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
                crate::leanh::lean_inc(v_instName_5841_);
                v___x_5852_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
                    v___x_5850_,
                    v___x_5851_,
                    v_env_5849_,
                    v_instName_5841_,
                );
                if crate::leanh::lean_obj_tag(v___x_5852_) == 1 {
                    v_val_5853_ = crate::leanh::lean_ctor_get(v___x_5852_, 0);
                    v_isSharedCheck_5896_ = (!crate::leanh::lean_is_exclusive(v___x_5852_)) as u8;
                    if v_isSharedCheck_5896_ == 0 {
                        v___x_5855_ = v___x_5852_;
                        v_isShared_5856_ = v_isSharedCheck_5896_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5853_);
                        crate::leanh::lean_dec(v___x_5852_);
                        v___x_5855_ = crate::leanh::lean_box(0);
                        v_isShared_5856_ = v_isSharedCheck_5896_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5852_);
                    crate::leanh::lean_dec_ref(v_op_5842_);
                    crate::leanh::lean_dec(v_instName_5841_);
                    v___x_5897_ = crate::leanh::lean_box(0);
                    v___x_5898_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5898_, 0, v___x_5897_);
                    return v___x_5898_;
                }
            }
            1 => {
                v___x_5857_ = lean_st_ref_get(v_a_5846_);
                v_env_5858_ = crate::leanh::lean_ctor_get(v___x_5857_, 0);
                crate::leanh::lean_inc_ref(v_env_5858_);
                crate::leanh::lean_dec(v___x_5857_);
                v_privateSpecs_5859_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_5853_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec(v_val_5853_);
                v___x_5860_ =
                    l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0;
                crate::leanh::lean_inc_ref(v_op_5842_);
                v___x_5861_ = lean_string_append(v_op_5842_, v___x_5860_);
                crate::leanh::lean_inc(v_instName_5841_);
                v___x_5862_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                    v_env_5858_,
                    v_instName_5841_,
                    v_privateSpecs_5859_,
                    v___x_5861_,
                );
                crate::leanh::lean_dec_ref(v_env_5858_);
                v___x_5863_ =
                    l_Lean_realizeGlobalConstNoOverloadCore(v___x_5862_, v_a_5845_, v_a_5846_);
                if crate::leanh::lean_obj_tag(v___x_5863_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5863_, 1);
                    v___x_5864_ = lean_st_ref_get(v_a_5846_);
                    v_env_5865_ = crate::leanh::lean_ctor_get(v___x_5864_, 0);
                    crate::leanh::lean_inc_ref(v_env_5865_);
                    crate::leanh::lean_dec(v___x_5864_);
                    v___x_5866_ = l_Lean_getMethodSpecTheorems___closed__1;
                    v___x_5867_ = l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0___redArg(v_op_5842_, v_instName_5841_, v_privateSpecs_5859_, v_env_5865_, v___x_5866_, v_a_5846_);
                    crate::leanh::lean_dec_ref(v_env_5865_);
                    if crate::leanh::lean_obj_tag(v___x_5867_) == 0 {
                        v_a_5868_ = crate::leanh::lean_ctor_get(v___x_5867_, 0);
                        v_isSharedCheck_5879_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5867_)) as u8;
                        if v_isSharedCheck_5879_ == 0 {
                            v___x_5870_ = v___x_5867_;
                            v_isShared_5871_ = v_isSharedCheck_5879_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5868_);
                            crate::leanh::lean_dec(v___x_5867_);
                            v___x_5870_ = crate::leanh::lean_box(0);
                            v_isShared_5871_ = v_isSharedCheck_5879_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5855_);
                        v_a_5880_ = crate::leanh::lean_ctor_get(v___x_5867_, 0);
                        v_isSharedCheck_5887_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5867_)) as u8;
                        if v_isSharedCheck_5887_ == 0 {
                            v___x_5882_ = v___x_5867_;
                            v_isShared_5883_ = v_isSharedCheck_5887_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5880_);
                            crate::leanh::lean_dec(v___x_5867_);
                            v___x_5882_ = crate::leanh::lean_box(0);
                            v_isShared_5883_ = v_isSharedCheck_5887_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5855_);
                    crate::leanh::lean_dec_ref(v_op_5842_);
                    crate::leanh::lean_dec(v_instName_5841_);
                    v_a_5888_ = crate::leanh::lean_ctor_get(v___x_5863_, 0);
                    v_isSharedCheck_5895_ = (!crate::leanh::lean_is_exclusive(v___x_5863_)) as u8;
                    if v_isSharedCheck_5895_ == 0 {
                        v___x_5890_ = v___x_5863_;
                        v_isShared_5891_ = v_isSharedCheck_5895_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5888_);
                        crate::leanh::lean_dec(v___x_5863_);
                        v___x_5890_ = crate::leanh::lean_box(0);
                        v_isShared_5891_ = v_isSharedCheck_5895_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_5872_ = crate::leanh::lean_ctor_get(v_a_5868_, 1);
                crate::leanh::lean_inc(v_snd_5872_);
                crate::leanh::lean_dec(v_a_5868_);
                if v_isShared_5856_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5855_, 0, v_snd_5872_);
                    v___x_5874_ = v___x_5855_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5878_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5878_, 0, v_snd_5872_);
                    v___x_5874_ = v_reuseFailAlloc_5878_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5871_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5870_, 0, v___x_5874_);
                    v___x_5876_ = v___x_5870_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5877_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5877_, 0, v___x_5874_);
                    v___x_5876_ = v_reuseFailAlloc_5877_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5876_;
            }
            5 => {
                if v_isShared_5883_ == 0 {
                    v___x_5885_ = v___x_5882_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5886_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5886_, 0, v_a_5880_);
                    v___x_5885_ = v_reuseFailAlloc_5886_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5885_;
            }
            7 => {
                if v_isShared_5891_ == 0 {
                    v___x_5893_ = v___x_5890_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5894_, 0, v_a_5888_);
                    v___x_5893_ = v_reuseFailAlloc_5894_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getMethodSpecTheorems___boxed(
    mut v_instName_5899_: *mut crate::leanh::LeanObject,
    mut v_op_5900_: *mut crate::leanh::LeanObject,
    mut v_a_5901_: *mut crate::leanh::LeanObject,
    mut v_a_5902_: *mut crate::leanh::LeanObject,
    mut v_a_5903_: *mut crate::leanh::LeanObject,
    mut v_a_5904_: *mut crate::leanh::LeanObject,
    mut v_a_5905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5906_ = l_Lean_getMethodSpecTheorems(
        v_instName_5899_,
        v_op_5900_,
        v_a_5901_,
        v_a_5902_,
        v_a_5903_,
        v_a_5904_,
    );
    crate::leanh::lean_dec(v_a_5904_);
    crate::leanh::lean_dec_ref(v_a_5903_);
    crate::leanh::lean_dec(v_a_5902_);
    crate::leanh::lean_dec_ref(v_a_5901_);
    return v_res_5906_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0(
    mut v_op_5907_: *mut crate::leanh::LeanObject,
    mut v_instName_5908_: *mut crate::leanh::LeanObject,
    mut v___x_5909_: u8,
    mut v___x_5910_: *mut crate::leanh::LeanObject,
    mut v_inst_5911_: *mut crate::leanh::LeanObject,
    mut v_a_5912_: *mut crate::leanh::LeanObject,
    mut v___y_5913_: *mut crate::leanh::LeanObject,
    mut v___y_5914_: *mut crate::leanh::LeanObject,
    mut v___y_5915_: *mut crate::leanh::LeanObject,
    mut v___y_5916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5918_ = l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0___redArg(v_op_5907_, v_instName_5908_, v___x_5909_, v___x_5910_, v_a_5912_, v___y_5916_);
    return v___x_5918_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0___boxed(
    mut v_op_5919_: *mut crate::leanh::LeanObject,
    mut v_instName_5920_: *mut crate::leanh::LeanObject,
    mut v___x_5921_: *mut crate::leanh::LeanObject,
    mut v___x_5922_: *mut crate::leanh::LeanObject,
    mut v_inst_5923_: *mut crate::leanh::LeanObject,
    mut v_a_5924_: *mut crate::leanh::LeanObject,
    mut v___y_5925_: *mut crate::leanh::LeanObject,
    mut v___y_5926_: *mut crate::leanh::LeanObject,
    mut v___y_5927_: *mut crate::leanh::LeanObject,
    mut v___y_5928_: *mut crate::leanh::LeanObject,
    mut v___y_5929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2384__boxed_5930_: u8 = 0;
    let mut v_res_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2384__boxed_5930_ = (crate::leanh::lean_unbox(v___x_5921_) as u8);
    v_res_5931_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0(
            v_op_5919_,
            v_instName_5920_,
            v___x_2384__boxed_5930_,
            v___x_5922_,
            v_inst_5923_,
            v_a_5924_,
            v___y_5925_,
            v___y_5926_,
            v___y_5927_,
            v___y_5928_,
        );
    crate::leanh::lean_dec(v___y_5928_);
    crate::leanh::lean_dec_ref(v___y_5927_);
    crate::leanh::lean_dec(v___y_5926_);
    crate::leanh::lean_dec_ref(v___y_5925_);
    crate::leanh::lean_dec_ref(v___x_5922_);
    return v_res_5931_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(
    mut v_env_5932_: *mut crate::leanh::LeanObject,
    mut v_name_5933_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5934_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(v_env_5932_, v_name_5933_);
    if crate::leanh::lean_obj_tag(v___x_5934_) == 0 {
        let mut v___x_5935_: u8 = 0;
        v___x_5935_ = 0;
        return v___x_5935_;
    } else {
        let mut v___x_5936_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_5934_, 1);
        v___x_5936_ = 1;
        return v___x_5936_;
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(
    mut v_env_5937_: *mut crate::leanh::LeanObject,
    mut v_name_5938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5939_: u8 = 0;
    let mut v_r_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5939_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(v_env_5937_, v_name_5938_);
    v_r_5940_ = crate::leanh::lean_box((v_res_5939_) as usize);
    return v_r_5940_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(
    mut v___x_5941_: *mut crate::leanh::LeanObject,
    mut v_name_5942_: *mut crate::leanh::LeanObject,
    mut v___y_5943_: *mut crate::leanh::LeanObject,
    mut v___y_5944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: u8 = 0;
    let mut v___x_5951_: u8 = 0;
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5969_: u8 = 0;
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5975_: u8 = 0;
    let mut v_unused_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5979_: u8 = 0;
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5984_: u8 = 0;
    let mut v_unused_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5989_: u8 = 0;
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5993_: u8 = 0;
    let mut v___x_5994_: u8 = 0;
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5946_ = lean_st_ref_get(v___y_5944_);
                v_env_5947_ = crate::leanh::lean_ctor_get(v___x_5946_, 0);
                crate::leanh::lean_inc_ref(v_env_5947_);
                crate::leanh::lean_dec(v___x_5946_);
                v___x_5948_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(
                    v_env_5947_,
                    v_name_5942_,
                );
                if crate::leanh::lean_obj_tag(v___x_5948_) == 1 {
                    v_val_5949_ = crate::leanh::lean_ctor_get(v___x_5948_, 0);
                    crate::leanh::lean_inc(v_val_5949_);
                    crate::leanh::lean_dec_ref_known(v___x_5948_, 1);
                    v___x_5950_ = 0;
                    v___x_5951_ = 1;
                    v___x_5952_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2);
                    v___x_5953_ = crate::leanh::lean_unsigned_to_nat(32);
                    v___x_5954_ = lean_mk_empty_array_with_capacity(v___x_5953_);
                    crate::leanh::lean_dec_ref(v___x_5954_);
                    v___x_5955_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5956_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6);
                    v___x_5957_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7);
                    v___x_5958_ =
                        l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8;
                    v___x_5959_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___x_5941_);
                    v___x_5960_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    crate::leanh::lean_ctor_set(v___x_5960_, 0, v___x_5952_);
                    crate::leanh::lean_ctor_set(v___x_5960_, 1, v___x_5941_);
                    crate::leanh::lean_ctor_set(v___x_5960_, 2, v___x_5957_);
                    crate::leanh::lean_ctor_set(v___x_5960_, 3, v___x_5958_);
                    crate::leanh::lean_ctor_set(v___x_5960_, 4, v___x_5959_);
                    crate::leanh::lean_ctor_set(v___x_5960_, 5, v___x_5955_);
                    crate::leanh::lean_ctor_set(v___x_5960_, 6, v___x_5959_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5960_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v___x_5950_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5960_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                        v___x_5950_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5960_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                        v___x_5950_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5960_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                        v___x_5951_,
                    );
                    v___x_5961_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10);
                    v___x_5962_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11);
                    v___x_5963_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12);
                    v___x_5964_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5964_, 0, v___x_5961_);
                    crate::leanh::lean_ctor_set(v___x_5964_, 1, v___x_5962_);
                    crate::leanh::lean_ctor_set(v___x_5964_, 2, v___x_5941_);
                    crate::leanh::lean_ctor_set(v___x_5964_, 3, v___x_5956_);
                    crate::leanh::lean_ctor_set(v___x_5964_, 4, v___x_5963_);
                    v___x_5965_ = lean_st_mk_ref(v___x_5964_);
                    v___x_5966_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(
                        v_val_5949_,
                        v___x_5960_,
                        v___x_5965_,
                        v___y_5943_,
                        v___y_5944_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_5960_, 7);
                    if crate::leanh::lean_obj_tag(v___x_5966_) == 0 {
                        v_isSharedCheck_5975_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5966_)) as u8;
                        if v_isSharedCheck_5975_ == 0 {
                            v_unused_5976_ = crate::leanh::lean_ctor_get(v___x_5966_, 0);
                            crate::leanh::lean_dec(v_unused_5976_);
                            v___x_5968_ = v___x_5966_;
                            v_isShared_5969_ = v_isSharedCheck_5975_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5966_);
                            v___x_5968_ = crate::leanh::lean_box(0);
                            v_isShared_5969_ = v_isSharedCheck_5975_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5965_);
                        if crate::leanh::lean_obj_tag(v___x_5966_) == 0 {
                            v_isSharedCheck_5984_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5966_)) as u8;
                            if v_isSharedCheck_5984_ == 0 {
                                v_unused_5985_ = crate::leanh::lean_ctor_get(v___x_5966_, 0);
                                crate::leanh::lean_dec(v_unused_5985_);
                                v___x_5978_ = v___x_5966_;
                                v_isShared_5979_ = v_isSharedCheck_5984_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5966_);
                                v___x_5978_ = crate::leanh::lean_box(0);
                                v_isShared_5979_ = v_isSharedCheck_5984_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_5986_ = crate::leanh::lean_ctor_get(v___x_5966_, 0);
                            v_isSharedCheck_5993_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5966_)) as u8;
                            if v_isSharedCheck_5993_ == 0 {
                                v___x_5988_ = v___x_5966_;
                                v_isShared_5989_ = v_isSharedCheck_5993_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5986_);
                                crate::leanh::lean_dec(v___x_5966_);
                                v___x_5988_ = crate::leanh::lean_box(0);
                                v_isShared_5989_ = v_isSharedCheck_5993_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5948_);
                    crate::leanh::lean_dec(v___x_5941_);
                    v___x_5994_ = 0;
                    v___x_5995_ = crate::leanh::lean_box((v___x_5994_) as usize);
                    v___x_5996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5996_, 0, v___x_5995_);
                    return v___x_5996_;
                }
            }
            1 => {
                v___x_5970_ = lean_st_ref_get(v___x_5965_);
                crate::leanh::lean_dec(v___x_5965_);
                crate::leanh::lean_dec(v___x_5970_);
                v___x_5971_ = crate::leanh::lean_box((v___x_5951_) as usize);
                if v_isShared_5969_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5968_, 0, v___x_5971_);
                    v___x_5973_ = v___x_5968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5974_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5974_, 0, v___x_5971_);
                    v___x_5973_ = v_reuseFailAlloc_5974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5973_;
            }
            3 => {
                v___x_5980_ = crate::leanh::lean_box((v___x_5951_) as usize);
                if v_isShared_5979_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5978_, 0);
                    crate::leanh::lean_ctor_set(v___x_5978_, 0, v___x_5980_);
                    v___x_5982_ = v___x_5978_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5983_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5983_, 0, v___x_5980_);
                    v___x_5982_ = v_reuseFailAlloc_5983_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5982_;
            }
            5 => {
                if v_isShared_5989_ == 0 {
                    v___x_5991_ = v___x_5988_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5992_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5992_, 0, v_a_5986_);
                    v___x_5991_ = v_reuseFailAlloc_5992_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(
    mut v___x_5997_: *mut crate::leanh::LeanObject,
    mut v_name_5998_: *mut crate::leanh::LeanObject,
    mut v___y_5999_: *mut crate::leanh::LeanObject,
    mut v___y_6000_: *mut crate::leanh::LeanObject,
    mut v___y_6001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6002_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(v___x_5997_, v_name_5998_, v___y_5999_, v___y_6000_);
    crate::leanh::lean_dec(v___y_6000_);
    crate::leanh::lean_dec_ref(v___y_5999_);
    return v_res_6002_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6007_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_;
    v___x_6008_ = l_Lean_registerReservedNamePredicate(v___f_6007_);
    if crate::leanh::lean_obj_tag(v___x_6008_) == 0 {
        let mut v___f_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_6008_, 1);
        v___f_6009_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_;
        v___x_6010_ = l_Lean_registerReservedNameAction(v___f_6009_);
        return v___x_6010_;
    } else {
        return v___x_6008_;
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(
    mut v_a_6011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6012_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_();
    return v_res_6012_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6030_ = crate::leanh::lean_unsigned_to_nat(2329740376);
    v___x_6031_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_;
    v___x_6032_ = l_Lean_Name_num___override(v___x_6031_, v___x_6030_);
    return v___x_6032_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6034_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_;
    v___x_6035_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
    v___x_6036_ = l_Lean_Name_str___override(v___x_6035_, v___x_6034_);
    return v___x_6036_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6038_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_;
    v___x_6039_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
    v___x_6040_ = l_Lean_Name_str___override(v___x_6039_, v___x_6038_);
    return v___x_6040_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6041_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_6042_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
    v___x_6043_ = l_Lean_Name_num___override(v___x_6042_, v___x_6041_);
    return v___x_6043_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: u8 = 0;
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6045_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3;
    v___x_6046_ = 0;
    v___x_6047_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
    v___x_6048_ = l_Lean_registerTraceClass(v___x_6045_, v___x_6046_, v___x_6047_);
    return v___x_6048_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2____boxed(
    mut v_a_6049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6050_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_();
    return v_res_6050_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_MethodSpecs(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Structure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsSimpExtension =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsSimpExtension,
    );
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_MethodSpecs(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_MethodSpecs(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Structure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_MethodSpecs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_MethodSpecs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_MethodSpecs(builtin);
}
