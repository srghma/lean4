// Lean compiler output
// Module: Lean.Meta.MethodSpecs
// Imports: Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Tactic.Simp.Main Lean.Structure
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
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_replaceRef,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_array_mk,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_dec_eq, lean_string_utf8_byte_size,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Level::lean_level_eq;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__2_value) as *mut LeanObject;
pub static l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__0_value) as *mut LeanObject;
pub static l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__0_value) as *mut LeanObject] };
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__1_value) as *mut LeanObject;
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 101, 113, 117, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 111, 108, 100, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 102, 105, 101, 108, 100, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [32, 105, 110, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [102, 117, 110, 99, 116, 105, 111, 110, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11_value: LeanStringObject<64> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 64, m_capacity: 64, m_length: 63, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 116, 97, 107, 101, 32, 105, 116, 115, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 105, 110, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 111, 114, 100, 101, 114, 32, 97, 115, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [96, 32, 105, 115, 32, 99, 97, 108, 108, 101, 100, 32, 119, 105, 116, 104, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 10, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15_value: LeanStringObject<58> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [10, 119, 104, 105, 99, 104, 32, 100, 105, 102, 102, 101, 114, 115, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 39, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 10, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [102, 105, 101, 108, 100, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 32, 111, 102, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 111, 102, 32, 97, 32, 99, 111, 110, 115, 116, 97, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [77, 101, 116, 104, 111, 100, 83, 112, 101, 99, 115, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value
) as *mut LeanObject;
static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value) as *mut LeanObject,142734480563613395 as *mut LeanObject] };
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value) as *mut LeanObject,16869473420000565890 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [77, 101, 116, 104, 111, 100, 83, 112, 101, 99, 115, 32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 10, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [10, 116, 104, 109, 115, 58, 32, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [10, 112, 114, 105, 118, 97, 116, 101, 83, 112, 101, 99, 115, 58, 32, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [116, 104, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 111, 102, 32, 96, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__19_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 104, 97, 112, 101, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__19_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20:
    *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__4_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__5_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 68, 101, 102, 110, 63, 0]};
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6_value) as *mut LeanObject;
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__1_value:
    LeanStringObject<21> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__3_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__3_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__5_value:
    LeanStringObject<44> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__5_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__7_value:
    LeanStringObject<28> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__7_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedMethodSpecsAttrData_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedMethodSpecsAttrData: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 24) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [
        282574488338432 as *mut LeanObject,
        72621647814721793 as *mut LeanObject,
        65793 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1: u64 = 0;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value) as *mut LeanObject,16627468330847833091 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,5821782099191670350 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,14012549361381910007 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [109, 101, 116, 104, 111, 100, 83, 112, 101, 99, 115, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,3332304603237231731 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [109, 101, 116, 104, 111, 100, 95, 115, 112, 101, 99, 115, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,14706946839582711653 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__13_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [103, 101, 110, 101, 114, 97, 116, 101, 32, 109, 101, 116, 104, 111, 100, 32, 115, 112, 101, 99, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 115, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__13_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__13_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__14_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__13_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__14_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__14_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__15_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__15_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__15_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__16_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__16_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__16_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__17_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 8) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__14_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__15_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__16_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__17_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__17_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__0_value: LeanStringObject<566> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 566, m_capacity: 566, m_length: 565, m_data: [71, 101, 110, 101, 114, 97, 116, 101, 32, 109, 101, 116, 104, 111, 100, 32, 115, 112, 101, 99, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 102, 111, 114, 32, 116, 104, 101, 32, 109, 101, 116, 104, 111, 100, 115, 32, 111, 102, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 116, 121, 112, 101, 32, 99, 108, 97, 115, 115, 32, 105, 110, 115, 116, 97, 110, 99, 101, 46, 10, 10, 84, 104, 105, 115, 32, 101, 120, 112, 101, 99, 116, 115, 32, 97, 108, 108, 32, 40, 110, 111, 110, 45, 112, 114, 111, 111, 102, 41, 32, 109, 101, 116, 104, 111, 100, 115, 32, 111, 102, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 116, 111, 32, 98, 101, 32, 100, 101, 102, 105, 110, 101, 100, 32, 118, 105, 97, 32, 115, 101, 112, 97, 114, 97, 116, 101, 32, 104, 101, 108, 112, 101, 114, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 44, 10, 119, 104, 105, 99, 104, 32, 109, 117, 115, 116, 32, 116, 97, 107, 101, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 97, 115, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 105, 116, 115, 101, 108, 102, 44, 32, 105, 110, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 111, 114, 100, 101, 114, 46, 10, 10, 73, 102, 32, 105, 116, 32, 105, 115, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116, 111, 32, 97, 110, 32, 105, 110, 115, 116, 97, 110, 99, 101, 10, 96, 96, 96, 10, 105, 110, 115, 116, 97, 110, 99, 101, 32, 105, 110, 115, 116, 67, 108, 115, 84, 32, 58, 32, 67, 108, 115, 32, 84, 32, 119, 104, 101, 114, 101, 32, 111, 112, 32, 58, 61, 32, 111, 112, 73, 109, 112, 108, 10, 96, 96, 96, 10, 105, 116, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 97, 32, 116, 104, 101, 111, 114, 101, 109, 32, 96, 105, 110, 115, 116, 67, 108, 115, 84, 46, 111, 112, 95, 115, 112, 101, 99, 96, 32, 98, 97, 115, 101, 100, 32, 111, 110, 32, 96, 111, 112, 73, 109, 112, 108, 46, 101, 113, 95, 100, 101, 102, 96, 44, 32, 98, 117, 116, 32, 112, 104, 114, 97, 115, 101, 100, 32, 105, 110, 32, 116, 101, 114, 109, 115, 32, 111, 102, 32, 116, 104, 101, 10, 111, 118, 101, 114, 108, 111, 97, 100, 101, 100, 32, 96, 67, 108, 115, 46, 111, 112, 96, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 44, 32, 97, 110, 100, 32, 115, 105, 109, 105, 108, 97, 114, 108, 121, 32, 96, 105, 110, 115, 116, 67, 108, 115, 84, 46, 111, 112, 95, 115, 112, 101, 99, 95, 60, 110, 62, 96, 32, 98, 97, 115, 101, 100, 32, 111, 110, 32, 116, 104, 101, 32, 101, 113, 117, 97, 116, 105, 111, 110, 97, 108, 32, 116, 104, 101, 111, 114, 101, 109, 115, 10, 96, 111, 112, 73, 109, 112, 108, 46, 101, 113, 95, 60, 110, 62, 96, 46, 10, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 99 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 119 as usize) << 1) | 1) as *mut LeanObject,((( 3 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__1_value) as *mut LeanObject,((( 3 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 114 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 114 as usize) << 1) | 1) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__3_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__4_value) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [109, 101, 116, 104, 111, 100, 95, 115, 112, 101, 99, 115, 95, 115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut LeanObject,12978546787041305861 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value: LeanStringObject<74> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [115, 105, 109, 112, 32, 108, 101, 109, 109, 97, 32, 117, 115, 101, 100, 32, 116, 111, 32, 112, 111, 115, 116, 45, 112, 114, 111, 99, 101, 115, 115, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 32, 99, 114, 101, 97, 116, 101, 100, 32, 98, 121, 32, 96, 64, 91, 109, 101, 116, 104, 111, 100, 95, 115, 112, 101, 99, 115, 93, 96, 46, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [109, 101, 116, 104, 111, 100, 83, 112, 101, 99, 115, 83, 105, 109, 112, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut LeanObject,3786670690208729641 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1_value
) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__7_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__7_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__8_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__8_value)
        as *mut LeanObject;
static l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__7_value)
            as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__8_value)
            as *mut LeanObject,
        5647098122476602039 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9_value)
        as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13_value)
        as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15_value)
        as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 117, 110, 102, 111, 108, 100, 105, 110, 103, 32, 116, 104, 101, 111, 114, 101, 109, 32, 102, 111, 114, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [97, 100, 100, 105, 110, 103, 32, 115, 105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 32, 102, 111, 114, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0_value: LeanCtorObject<7> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 32) as u16, other: 3, tag: 0 }, m_objs: [((( 100000 as usize) << 1) | 1) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,72058697861300480 as *mut LeanObject,1103806595073 as *mut LeanObject,72340172838076672 as *mut LeanObject,257 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_getMethodSpecTheorems___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_getMethodSpecTheorems___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getMethodSpecTheorems___closed__0_value) as *mut LeanObject;
pub static l_Lean_getMethodSpecTheorems___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_getMethodSpecTheorems___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_getMethodSpecTheorems___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getMethodSpecTheorems___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject,3909582110267790918 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject,10411835254743274231 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value) as *mut LeanObject,1063899344436178826 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value) as *mut LeanObject,11253650946146721326 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value) as *mut LeanObject,17241205374711927315 as *mut LeanObject] };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0(
    mut v_k_3026_: *mut LeanObject,
    mut v_b_3027_: *mut LeanObject,
    mut v_c_3028_: *mut LeanObject,
    mut v___y_3029_: *mut LeanObject,
    mut v___y_3030_: *mut LeanObject,
    mut v___y_3031_: *mut LeanObject,
    mut v___y_3032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3032_);
    lean_inc_ref(v___y_3031_);
    lean_inc(v___y_3030_);
    lean_inc_ref(v___y_3029_);
    v___x_3034_ = lean_apply_7(
        v_k_3026_,
        v_b_3027_,
        v_c_3028_,
        v___y_3029_,
        v___y_3030_,
        v___y_3031_,
        v___y_3032_,
        lean_box(0),
    );
    return v___x_3034_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0___boxed(
    mut v_k_3035_: *mut LeanObject,
    mut v_b_3036_: *mut LeanObject,
    mut v_c_3037_: *mut LeanObject,
    mut v___y_3038_: *mut LeanObject,
    mut v___y_3039_: *mut LeanObject,
    mut v___y_3040_: *mut LeanObject,
    mut v___y_3041_: *mut LeanObject,
    mut v___y_3042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3043_: *mut LeanObject = core::ptr::null_mut();
    v_res_3043_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0(v_k_3035_, v_b_3036_, v_c_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
    lean_dec(v___y_3041_);
    lean_dec_ref(v___y_3040_);
    lean_dec(v___y_3039_);
    lean_dec_ref(v___y_3038_);
    return v_res_3043_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(
    mut v_type_3044_: *mut LeanObject,
    mut v_k_3045_: *mut LeanObject,
    mut v_cleanupAnnotations_3046_: u8,
    mut v_whnfType_3047_: u8,
    mut v___y_3048_: *mut LeanObject,
    mut v___y_3049_: *mut LeanObject,
    mut v___y_3050_: *mut LeanObject,
    mut v___y_3051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3058_: u8 = 0;
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3062_: u8 = 0;
    let mut v_a_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3070_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3053_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_3053_, 0, v_k_3045_);
                v___x_3054_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_3044_,
                    v___f_3053_,
                    v_cleanupAnnotations_3046_,
                    v_whnfType_3047_,
                    v___y_3048_,
                    v___y_3049_,
                    v___y_3050_,
                    v___y_3051_,
                );
                if lean_obj_tag(v___x_3054_) == 0 {
                    v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
                    v_isSharedCheck_3062_ = (!lean_is_exclusive(v___x_3054_)) as u8;
                    if v_isSharedCheck_3062_ == 0 {
                        v___x_3057_ = v___x_3054_;
                        v_isShared_3058_ = v_isSharedCheck_3062_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3055_);
                        lean_dec(v___x_3054_);
                        v___x_3057_ = lean_box(0);
                        v_isShared_3058_ = v_isSharedCheck_3062_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3063_ = lean_ctor_get(v___x_3054_, 0);
                    v_isSharedCheck_3070_ = (!lean_is_exclusive(v___x_3054_)) as u8;
                    if v_isSharedCheck_3070_ == 0 {
                        v___x_3065_ = v___x_3054_;
                        v_isShared_3066_ = v_isSharedCheck_3070_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3063_);
                        lean_dec(v___x_3054_);
                        v___x_3065_ = lean_box(0);
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
                    v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
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
                    v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
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
    mut v_type_3071_: *mut LeanObject,
    mut v_k_3072_: *mut LeanObject,
    mut v_cleanupAnnotations_3073_: *mut LeanObject,
    mut v_whnfType_3074_: *mut LeanObject,
    mut v___y_3075_: *mut LeanObject,
    mut v___y_3076_: *mut LeanObject,
    mut v___y_3077_: *mut LeanObject,
    mut v___y_3078_: *mut LeanObject,
    mut v___y_3079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3080_: u8 = 0;
    let mut v_whnfType_boxed_3081_: u8 = 0;
    let mut v_res_3082_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3080_ = (lean_unbox(v_cleanupAnnotations_3073_) as u8);
    v_whnfType_boxed_3081_ = (lean_unbox(v_whnfType_3074_) as u8);
    v_res_3082_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(v_type_3071_, v_k_3072_, v_cleanupAnnotations_boxed_3080_, v_whnfType_boxed_3081_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
    lean_dec(v___y_3078_);
    lean_dec_ref(v___y_3077_);
    lean_dec(v___y_3076_);
    lean_dec_ref(v___y_3075_);
    return v_res_3082_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1(
    mut v_00_u03b1_3083_: *mut LeanObject,
    mut v_type_3084_: *mut LeanObject,
    mut v_k_3085_: *mut LeanObject,
    mut v_cleanupAnnotations_3086_: u8,
    mut v_whnfType_3087_: u8,
    mut v___y_3088_: *mut LeanObject,
    mut v___y_3089_: *mut LeanObject,
    mut v___y_3090_: *mut LeanObject,
    mut v___y_3091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    v___x_3093_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(v_type_3084_, v_k_3085_, v_cleanupAnnotations_3086_, v_whnfType_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___boxed(
    mut v_00_u03b1_3094_: *mut LeanObject,
    mut v_type_3095_: *mut LeanObject,
    mut v_k_3096_: *mut LeanObject,
    mut v_cleanupAnnotations_3097_: *mut LeanObject,
    mut v_whnfType_3098_: *mut LeanObject,
    mut v___y_3099_: *mut LeanObject,
    mut v___y_3100_: *mut LeanObject,
    mut v___y_3101_: *mut LeanObject,
    mut v___y_3102_: *mut LeanObject,
    mut v___y_3103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3104_: u8 = 0;
    let mut v_whnfType_boxed_3105_: u8 = 0;
    let mut v_res_3106_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3104_ = (lean_unbox(v_cleanupAnnotations_3097_) as u8);
    v_whnfType_boxed_3105_ = (lean_unbox(v_whnfType_3098_) as u8);
    v_res_3106_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1(v_00_u03b1_3094_, v_type_3095_, v_k_3096_, v_cleanupAnnotations_boxed_3104_, v_whnfType_boxed_3105_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
    lean_dec(v___y_3102_);
    lean_dec_ref(v___y_3101_);
    lean_dec(v___y_3100_);
    lean_dec_ref(v___y_3099_);
    return v_res_3106_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(
    mut v_e_3107_: *mut LeanObject,
    mut v_k_3108_: *mut LeanObject,
    mut v_cleanupAnnotations_3109_: u8,
    mut v___y_3110_: *mut LeanObject,
    mut v___y_3111_: *mut LeanObject,
    mut v___y_3112_: *mut LeanObject,
    mut v___y_3113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: u8 = 0;
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3127_: u8 = 0;
    let mut v_a_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3115_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_3115_, 0, v_k_3108_);
                v___x_3116_ = 1;
                v___x_3117_ = 0;
                v___x_3118_ = lean_box(0);
                v___x_3119_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_3119_) == 0 {
                    v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
                    v_isSharedCheck_3127_ = (!lean_is_exclusive(v___x_3119_)) as u8;
                    if v_isSharedCheck_3127_ == 0 {
                        v___x_3122_ = v___x_3119_;
                        v_isShared_3123_ = v_isSharedCheck_3127_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3120_);
                        lean_dec(v___x_3119_);
                        v___x_3122_ = lean_box(0);
                        v_isShared_3123_ = v_isSharedCheck_3127_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3128_ = lean_ctor_get(v___x_3119_, 0);
                    v_isSharedCheck_3135_ = (!lean_is_exclusive(v___x_3119_)) as u8;
                    if v_isSharedCheck_3135_ == 0 {
                        v___x_3130_ = v___x_3119_;
                        v_isShared_3131_ = v_isSharedCheck_3135_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3128_);
                        lean_dec(v___x_3119_);
                        v___x_3130_ = lean_box(0);
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
                    v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
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
                    v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
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
    mut v_e_3136_: *mut LeanObject,
    mut v_k_3137_: *mut LeanObject,
    mut v_cleanupAnnotations_3138_: *mut LeanObject,
    mut v___y_3139_: *mut LeanObject,
    mut v___y_3140_: *mut LeanObject,
    mut v___y_3141_: *mut LeanObject,
    mut v___y_3142_: *mut LeanObject,
    mut v___y_3143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3144_: u8 = 0;
    let mut v_res_3145_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3144_ = (lean_unbox(v_cleanupAnnotations_3138_) as u8);
    v_res_3145_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(v_e_3136_, v_k_3137_, v_cleanupAnnotations_boxed_3144_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
    lean_dec(v___y_3142_);
    lean_dec_ref(v___y_3141_);
    lean_dec(v___y_3140_);
    lean_dec_ref(v___y_3139_);
    return v_res_3145_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(
    mut v_00_u03b1_3146_: *mut LeanObject,
    mut v_e_3147_: *mut LeanObject,
    mut v_k_3148_: *mut LeanObject,
    mut v_cleanupAnnotations_3149_: u8,
    mut v___y_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
    mut v___y_3153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    v___x_3155_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(v_e_3147_, v_k_3148_, v_cleanupAnnotations_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
    return v___x_3155_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___boxed(
    mut v_00_u03b1_3156_: *mut LeanObject,
    mut v_e_3157_: *mut LeanObject,
    mut v_k_3158_: *mut LeanObject,
    mut v_cleanupAnnotations_3159_: *mut LeanObject,
    mut v___y_3160_: *mut LeanObject,
    mut v___y_3161_: *mut LeanObject,
    mut v___y_3162_: *mut LeanObject,
    mut v___y_3163_: *mut LeanObject,
    mut v___y_3164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3165_: u8 = 0;
    let mut v_res_3166_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3165_ = (lean_unbox(v_cleanupAnnotations_3159_) as u8);
    v_res_3166_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(v_00_u03b1_3156_, v_e_3157_, v_k_3158_, v_cleanupAnnotations_boxed_3165_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
    lean_dec(v___y_3163_);
    lean_dec_ref(v___y_3162_);
    lean_dec(v___y_3161_);
    lean_dec_ref(v___y_3160_);
    return v_res_3166_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0(
    mut v_xs_3167_: *mut LeanObject,
    mut v_x_3168_: *mut LeanObject,
    mut v___y_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
    mut v___y_3171_: *mut LeanObject,
    mut v___y_3172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    v___x_3174_ = lean_array_get_size(v_xs_3167_);
    v___x_3175_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3175_, 0, v___x_3174_);
    return v___x_3175_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0___boxed(
    mut v_xs_3176_: *mut LeanObject,
    mut v_x_3177_: *mut LeanObject,
    mut v___y_3178_: *mut LeanObject,
    mut v___y_3179_: *mut LeanObject,
    mut v___y_3180_: *mut LeanObject,
    mut v___y_3181_: *mut LeanObject,
    mut v___y_3182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3183_: *mut LeanObject = core::ptr::null_mut();
    v_res_3183_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0(
        v_xs_3176_,
        v_x_3177_,
        v___y_3178_,
        v___y_3179_,
        v___y_3180_,
        v___y_3181_,
    );
    lean_dec(v___y_3181_);
    lean_dec_ref(v___y_3180_);
    lean_dec(v___y_3179_);
    lean_dec_ref(v___y_3178_);
    lean_dec_ref(v_x_3177_);
    lean_dec_ref(v_xs_3176_);
    return v_res_3183_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(
    mut v_msgData_3184_: *mut LeanObject,
    mut v___y_3185_: *mut LeanObject,
    mut v___y_3186_: *mut LeanObject,
    mut v___y_3187_: *mut LeanObject,
    mut v___y_3188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    v___x_3190_ = lean_st_ref_get(v___y_3188_);
    v_env_3191_ = lean_ctor_get(v___x_3190_, 0);
    lean_inc_ref(v_env_3191_);
    lean_dec(v___x_3190_);
    v___x_3192_ = lean_st_ref_get(v___y_3186_);
    v_mctx_3193_ = lean_ctor_get(v___x_3192_, 0);
    lean_inc_ref(v_mctx_3193_);
    lean_dec(v___x_3192_);
    v_lctx_3194_ = lean_ctor_get(v___y_3185_, 2);
    v_options_3195_ = lean_ctor_get(v___y_3187_, 2);
    lean_inc_ref(v_options_3195_);
    lean_inc_ref(v_lctx_3194_);
    v___x_3196_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3196_, 0, v_env_3191_);
    lean_ctor_set(v___x_3196_, 1, v_mctx_3193_);
    lean_ctor_set(v___x_3196_, 2, v_lctx_3194_);
    lean_ctor_set(v___x_3196_, 3, v_options_3195_);
    v___x_3197_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3197_, 0, v___x_3196_);
    lean_ctor_set(v___x_3197_, 1, v_msgData_3184_);
    v___x_3198_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3198_, 0, v___x_3197_);
    return v___x_3198_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4___boxed(
    mut v_msgData_3199_: *mut LeanObject,
    mut v___y_3200_: *mut LeanObject,
    mut v___y_3201_: *mut LeanObject,
    mut v___y_3202_: *mut LeanObject,
    mut v___y_3203_: *mut LeanObject,
    mut v___y_3204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3205_: *mut LeanObject = core::ptr::null_mut();
    v_res_3205_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(v_msgData_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
    lean_dec(v___y_3203_);
    lean_dec_ref(v___y_3202_);
    lean_dec(v___y_3201_);
    lean_dec_ref(v___y_3200_);
    return v_res_3205_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(
    mut v_msg_3206_: *mut LeanObject,
    mut v___y_3207_: *mut LeanObject,
    mut v___y_3208_: *mut LeanObject,
    mut v___y_3209_: *mut LeanObject,
    mut v___y_3210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3217_: u8 = 0;
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3212_ = lean_ctor_get(v___y_3209_, 5);
                v___x_3213_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(v_msg_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
                v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
                v_isSharedCheck_3222_ = (!lean_is_exclusive(v___x_3213_)) as u8;
                if v_isSharedCheck_3222_ == 0 {
                    v___x_3216_ = v___x_3213_;
                    v_isShared_3217_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3214_);
                    lean_dec(v___x_3213_);
                    v___x_3216_ = lean_box(0);
                    v_isShared_3217_ = v_isSharedCheck_3222_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3212_);
                v___x_3218_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3218_, 0, v_ref_3212_);
                lean_ctor_set(v___x_3218_, 1, v_a_3214_);
                if v_isShared_3217_ == 0 {
                    lean_ctor_set_tag(v___x_3216_, 1);
                    lean_ctor_set(v___x_3216_, 0, v___x_3218_);
                    v___x_3220_ = v___x_3216_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
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
    mut v_msg_3223_: *mut LeanObject,
    mut v___y_3224_: *mut LeanObject,
    mut v___y_3225_: *mut LeanObject,
    mut v___y_3226_: *mut LeanObject,
    mut v___y_3227_: *mut LeanObject,
    mut v___y_3228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3229_: *mut LeanObject = core::ptr::null_mut();
    v_res_3229_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v_msg_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
    lean_dec(v___y_3227_);
    lean_dec_ref(v___y_3226_);
    lean_dec(v___y_3225_);
    lean_dec_ref(v___y_3224_);
    return v_res_3229_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0()
-> f64 {
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: f64 = 0.0;
    v___x_3230_ = lean_unsigned_to_nat(0);
    v___x_3231_ = lean_float_of_nat(v___x_3230_);
    return v___x_3231_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(
    mut v_cls_3235_: *mut LeanObject,
    mut v_msg_3236_: *mut LeanObject,
    mut v___y_3237_: *mut LeanObject,
    mut v___y_3238_: *mut LeanObject,
    mut v___y_3239_: *mut LeanObject,
    mut v___y_3240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3247_: u8 = 0;
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v_tid_3261_: u64 = 0;
    let mut v_traces_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: f64 = 0.0;
    let mut v___x_3268_: u8 = 0;
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3242_ = lean_ctor_get(v___y_3239_, 5);
                v___x_3243_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(v_msg_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
                v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
                v_isSharedCheck_3288_ = (!lean_is_exclusive(v___x_3243_)) as u8;
                if v_isSharedCheck_3288_ == 0 {
                    v___x_3246_ = v___x_3243_;
                    v_isShared_3247_ = v_isSharedCheck_3288_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3244_);
                    lean_dec(v___x_3243_);
                    v___x_3246_ = lean_box(0);
                    v_isShared_3247_ = v_isSharedCheck_3288_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3248_ = lean_st_ref_take(v___y_3240_);
                v_traceState_3249_ = lean_ctor_get(v___x_3248_, 4);
                v_env_3250_ = lean_ctor_get(v___x_3248_, 0);
                v_nextMacroScope_3251_ = lean_ctor_get(v___x_3248_, 1);
                v_ngen_3252_ = lean_ctor_get(v___x_3248_, 2);
                v_auxDeclNGen_3253_ = lean_ctor_get(v___x_3248_, 3);
                v_cache_3254_ = lean_ctor_get(v___x_3248_, 5);
                v_messages_3255_ = lean_ctor_get(v___x_3248_, 6);
                v_infoState_3256_ = lean_ctor_get(v___x_3248_, 7);
                v_snapshotTasks_3257_ = lean_ctor_get(v___x_3248_, 8);
                v_isSharedCheck_3287_ = (!lean_is_exclusive(v___x_3248_)) as u8;
                if v_isSharedCheck_3287_ == 0 {
                    v___x_3259_ = v___x_3248_;
                    v_isShared_3260_ = v_isSharedCheck_3287_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3257_);
                    lean_inc(v_infoState_3256_);
                    lean_inc(v_messages_3255_);
                    lean_inc(v_cache_3254_);
                    lean_inc(v_traceState_3249_);
                    lean_inc(v_auxDeclNGen_3253_);
                    lean_inc(v_ngen_3252_);
                    lean_inc(v_nextMacroScope_3251_);
                    lean_inc(v_env_3250_);
                    lean_dec(v___x_3248_);
                    v___x_3259_ = lean_box(0);
                    v_isShared_3260_ = v_isSharedCheck_3287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3261_ = lean_ctor_get_uint64(
                    v_traceState_3249_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3262_ = lean_ctor_get(v_traceState_3249_, 0);
                v_isSharedCheck_3286_ = (!lean_is_exclusive(v_traceState_3249_)) as u8;
                if v_isSharedCheck_3286_ == 0 {
                    v___x_3264_ = v_traceState_3249_;
                    v_isShared_3265_ = v_isSharedCheck_3286_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_3262_);
                    lean_dec(v_traceState_3249_);
                    v___x_3264_ = lean_box(0);
                    v_isShared_3265_ = v_isSharedCheck_3286_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3266_ = lean_box(0);
                v___x_3267_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0);
                v___x_3268_ = 0;
                v___x_3269_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__1;
                v___x_3270_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_3270_, 0, v_cls_3235_);
                lean_ctor_set(v___x_3270_, 1, v___x_3266_);
                lean_ctor_set(v___x_3270_, 2, v___x_3269_);
                lean_ctor_set_float(
                    v___x_3270_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3267_,
                );
                lean_ctor_set_float(
                    v___x_3270_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3267_,
                );
                lean_ctor_set_uint8(
                    v___x_3270_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_3268_,
                );
                v___x_3271_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__2;
                v___x_3272_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_3272_, 0, v___x_3270_);
                lean_ctor_set(v___x_3272_, 1, v_a_3244_);
                lean_ctor_set(v___x_3272_, 2, v___x_3271_);
                lean_inc(v_ref_3242_);
                v___x_3273_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3273_, 0, v_ref_3242_);
                lean_ctor_set(v___x_3273_, 1, v___x_3272_);
                v___x_3274_ = l_Lean_PersistentArray_push___redArg(v_traces_3262_, v___x_3273_);
                if v_isShared_3265_ == 0 {
                    lean_ctor_set(v___x_3264_, 0, v___x_3274_);
                    v___x_3276_ = v___x_3264_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3274_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3285_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3261_,
                    );
                    v___x_3276_ = v_reuseFailAlloc_3285_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3260_ == 0 {
                    lean_ctor_set(v___x_3259_, 4, v___x_3276_);
                    v___x_3278_ = v___x_3259_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_env_3250_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_nextMacroScope_3251_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 2, v_ngen_3252_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 3, v_auxDeclNGen_3253_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 4, v___x_3276_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 5, v_cache_3254_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 6, v_messages_3255_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 7, v_infoState_3256_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 8, v_snapshotTasks_3257_);
                    v___x_3278_ = v_reuseFailAlloc_3284_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3279_ = lean_st_ref_set(v___y_3240_, v___x_3278_);
                v___x_3280_ = lean_box(0);
                if v_isShared_3247_ == 0 {
                    lean_ctor_set(v___x_3246_, 0, v___x_3280_);
                    v___x_3282_ = v___x_3246_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
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
    mut v_cls_3289_: *mut LeanObject,
    mut v_msg_3290_: *mut LeanObject,
    mut v___y_3291_: *mut LeanObject,
    mut v___y_3292_: *mut LeanObject,
    mut v___y_3293_: *mut LeanObject,
    mut v___y_3294_: *mut LeanObject,
    mut v___y_3295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3296_: *mut LeanObject = core::ptr::null_mut();
    v_res_3296_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v_cls_3289_, v_msg_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
    lean_dec(v___y_3294_);
    lean_dec_ref(v___y_3293_);
    lean_dec(v___y_3292_);
    lean_dec_ref(v___y_3291_);
    return v_res_3296_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10(
    mut v_a_3297_: *mut LeanObject,
    mut v_a_3298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3297_) == 0 {
                    v___x_3299_ = l_List_reverse___redArg(v_a_3298_);
                    return v___x_3299_;
                } else {
                    v_head_3300_ = lean_ctor_get(v_a_3297_, 0);
                    v_tail_3301_ = lean_ctor_get(v_a_3297_, 1);
                    v_isSharedCheck_3310_ = (!lean_is_exclusive(v_a_3297_)) as u8;
                    if v_isSharedCheck_3310_ == 0 {
                        v___x_3303_ = v_a_3297_;
                        v_isShared_3304_ = v_isSharedCheck_3310_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3301_);
                        lean_inc(v_head_3300_);
                        lean_dec(v_a_3297_);
                        v___x_3303_ = lean_box(0);
                        v_isShared_3304_ = v_isSharedCheck_3310_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3305_ = l_Lean_MessageData_ofExpr(v_head_3300_);
                if v_isShared_3304_ == 0 {
                    lean_ctor_set(v___x_3303_, 1, v_a_3298_);
                    lean_ctor_set(v___x_3303_, 0, v___x_3305_);
                    v___x_3307_ = v___x_3303_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3305_);
                    lean_ctor_set(v_reuseFailAlloc_3309_, 1, v_a_3298_);
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
    mut v_bs_3313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3314_: u8 = 0;
    let mut v_v_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: usize = 0;
    let mut v___x_3320_: usize = 0;
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3314_ = lean_usize_dec_lt(v_i_3312_, v_sz_3311_);
                if v___x_3314_ == 0 {
                    return v_bs_3313_;
                } else {
                    v_v_3315_ = lean_array_uget_borrowed(v_bs_3313_, v_i_3312_);
                    v_type_3316_ = lean_ctor_get(v_v_3315_, 2);
                    lean_inc_ref(v_type_3316_);
                    v___x_3317_ = lean_unsigned_to_nat(0);
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
    mut v_sz_3323_: *mut LeanObject,
    mut v_i_3324_: *mut LeanObject,
    mut v_bs_3325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3326_: usize = 0;
    let mut v_i_boxed_3327_: usize = 0;
    let mut v_res_3328_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3326_ = lean_unbox_usize(v_sz_3323_);
    lean_dec(v_sz_3323_);
    v_i_boxed_3327_ = lean_unbox_usize(v_i_3324_);
    lean_dec(v_i_3324_);
    v_res_3328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9(v_sz_boxed_3326_, v_i_boxed_3327_, v_bs_3325_);
    return v_res_3328_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2()
-> *mut LeanObject {
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    v___x_3332_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__1;
    v___x_3333_ = l_Lean_MessageData_ofFormat(v___x_3332_);
    return v___x_3333_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3()
-> *mut LeanObject {
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    v___x_3334_ = lean_box(1);
    v___x_3335_ = l_Lean_MessageData_ofFormat(v___x_3334_);
    return v___x_3335_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(
    mut v_a_3336_: *mut LeanObject,
    mut v_a_3337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3343_: u8 = 0;
    let mut v_fst_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3348_: u8 = 0;
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3363_: u8 = 0;
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3336_) == 0 {
                    v___x_3338_ = l_List_reverse___redArg(v_a_3337_);
                    return v___x_3338_;
                } else {
                    v_head_3339_ = lean_ctor_get(v_a_3336_, 0);
                    v_tail_3340_ = lean_ctor_get(v_a_3336_, 1);
                    v_isSharedCheck_3364_ = (!lean_is_exclusive(v_a_3336_)) as u8;
                    if v_isSharedCheck_3364_ == 0 {
                        v___x_3342_ = v_a_3336_;
                        v_isShared_3343_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3340_);
                        lean_inc(v_head_3339_);
                        lean_dec(v_a_3336_);
                        v___x_3342_ = lean_box(0);
                        v_isShared_3343_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3344_ = lean_ctor_get(v_head_3339_, 0);
                v_snd_3345_ = lean_ctor_get(v_head_3339_, 1);
                v_isSharedCheck_3363_ = (!lean_is_exclusive(v_head_3339_)) as u8;
                if v_isSharedCheck_3363_ == 0 {
                    v___x_3347_ = v_head_3339_;
                    v_isShared_3348_ = v_isSharedCheck_3363_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3345_);
                    lean_inc(v_fst_3344_);
                    lean_dec(v_head_3339_);
                    v___x_3347_ = lean_box(0);
                    v_isShared_3348_ = v_isSharedCheck_3363_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3349_ = l_Lean_MessageData_ofName(v_fst_3344_);
                v___x_3350_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2_once), _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2);
                if v_isShared_3348_ == 0 {
                    lean_ctor_set_tag(v___x_3347_, 7);
                    lean_ctor_set(v___x_3347_, 1, v___x_3350_);
                    lean_ctor_set(v___x_3347_, 0, v___x_3349_);
                    v___x_3352_ = v___x_3347_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3362_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3349_);
                    lean_ctor_set(v_reuseFailAlloc_3362_, 1, v___x_3350_);
                    v___x_3352_ = v_reuseFailAlloc_3362_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3353_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3_once), _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3);
                v___x_3354_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3354_, 0, v___x_3352_);
                lean_ctor_set(v___x_3354_, 1, v___x_3353_);
                v___x_3355_ = l_Lean_MessageData_ofName(v_snd_3345_);
                v___x_3356_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3356_, 0, v___x_3354_);
                lean_ctor_set(v___x_3356_, 1, v___x_3355_);
                v___x_3357_ = l_Lean_MessageData_paren(v___x_3356_);
                if v_isShared_3343_ == 0 {
                    lean_ctor_set(v___x_3342_, 1, v_a_3337_);
                    lean_ctor_set(v___x_3342_, 0, v___x_3357_);
                    v___x_3359_ = v___x_3342_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3357_);
                    lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_a_3337_);
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
    mut v_a_3365_: *mut LeanObject,
    mut v_a_3366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3372_: u8 = 0;
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3365_) == 0 {
                    v___x_3367_ = l_List_reverse___redArg(v_a_3366_);
                    return v___x_3367_;
                } else {
                    v_head_3368_ = lean_ctor_get(v_a_3365_, 0);
                    v_tail_3369_ = lean_ctor_get(v_a_3365_, 1);
                    v_isSharedCheck_3378_ = (!lean_is_exclusive(v_a_3365_)) as u8;
                    if v_isSharedCheck_3378_ == 0 {
                        v___x_3371_ = v_a_3365_;
                        v_isShared_3372_ = v_isSharedCheck_3378_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3369_);
                        lean_inc(v_head_3368_);
                        lean_dec(v_a_3365_);
                        v___x_3371_ = lean_box(0);
                        v_isShared_3372_ = v_isSharedCheck_3378_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3373_ = l_Lean_mkLevelParam(v_head_3368_);
                if v_isShared_3372_ == 0 {
                    lean_ctor_set(v___x_3371_, 1, v_a_3366_);
                    lean_ctor_set(v___x_3371_, 0, v___x_3373_);
                    v___x_3375_ = v___x_3371_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3373_);
                    lean_ctor_set(v_reuseFailAlloc_3377_, 1, v_a_3366_);
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
    mut v_xs_3379_: *mut LeanObject,
    mut v_ys_3380_: *mut LeanObject,
    mut v_x_3381_: *mut LeanObject,
) -> u8 {
    let mut v_zero_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3383_: u8 = 0;
    let mut v_one_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3382_ = lean_unsigned_to_nat(0);
                v_isZero_3383_ = lean_nat_dec_eq(v_x_3381_, v_zero_3382_);
                if v_isZero_3383_ == 1 {
                    lean_dec(v_x_3381_);
                    return v_isZero_3383_;
                } else {
                    v_one_3384_ = lean_unsigned_to_nat(1);
                    v_n_3385_ = lean_nat_sub(v_x_3381_, v_one_3384_);
                    lean_dec(v_x_3381_);
                    v___x_3386_ = lean_array_fget_borrowed(v_xs_3379_, v_n_3385_);
                    v___x_3387_ = lean_array_fget_borrowed(v_ys_3380_, v_n_3385_);
                    v___x_3388_ = lean_expr_eqv(v___x_3386_, v___x_3387_);
                    if v___x_3388_ == 0 {
                        lean_dec(v_n_3385_);
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
    mut v_xs_3390_: *mut LeanObject,
    mut v_ys_3391_: *mut LeanObject,
    mut v_x_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3393_: u8 = 0;
    let mut v_r_3394_: *mut LeanObject = core::ptr::null_mut();
    v_res_3393_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(v_xs_3390_, v_ys_3391_, v_x_3392_);
    lean_dec_ref(v_ys_3391_);
    lean_dec_ref(v_xs_3390_);
    v_r_3394_ = lean_box((v_res_3393_) as usize);
    return v_r_3394_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(
    mut v_a_3395_: *mut LeanObject,
    mut v_a_3396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3402_: u8 = 0;
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3408_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3395_) == 0 {
                    v___x_3397_ = l_List_reverse___redArg(v_a_3396_);
                    return v___x_3397_;
                } else {
                    v_head_3398_ = lean_ctor_get(v_a_3395_, 0);
                    v_tail_3399_ = lean_ctor_get(v_a_3395_, 1);
                    v_isSharedCheck_3408_ = (!lean_is_exclusive(v_a_3395_)) as u8;
                    if v_isSharedCheck_3408_ == 0 {
                        v___x_3401_ = v_a_3395_;
                        v_isShared_3402_ = v_isSharedCheck_3408_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3399_);
                        lean_inc(v_head_3398_);
                        lean_dec(v_a_3395_);
                        v___x_3401_ = lean_box(0);
                        v_isShared_3402_ = v_isSharedCheck_3408_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3403_ = l_Lean_MessageData_ofLevel(v_head_3398_);
                if v_isShared_3402_ == 0 {
                    lean_ctor_set(v___x_3401_, 1, v_a_3396_);
                    lean_ctor_set(v___x_3401_, 0, v___x_3403_);
                    v___x_3405_ = v___x_3401_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3403_);
                    lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_a_3396_);
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
    mut v_x_3409_: *mut LeanObject,
    mut v_x_3410_: *mut LeanObject,
) -> u8 {
    let mut v___x_3411_: u8 = 0;
    let mut v___x_3412_: u8 = 0;
    let mut v___x_3413_: u8 = 0;
    let mut v_head_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3409_) == 0 {
                    if lean_obj_tag(v_x_3410_) == 0 {
                        v___x_3411_ = 1;
                        return v___x_3411_;
                    } else {
                        v___x_3412_ = 0;
                        return v___x_3412_;
                    }
                } else {
                    if lean_obj_tag(v_x_3410_) == 0 {
                        v___x_3413_ = 0;
                        return v___x_3413_;
                    } else {
                        v_head_3414_ = lean_ctor_get(v_x_3409_, 0);
                        v_tail_3415_ = lean_ctor_get(v_x_3409_, 1);
                        v_head_3416_ = lean_ctor_get(v_x_3410_, 0);
                        v_tail_3417_ = lean_ctor_get(v_x_3410_, 1);
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
    mut v_x_3420_: *mut LeanObject,
    mut v_x_3421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3422_: u8 = 0;
    let mut v_r_3423_: *mut LeanObject = core::ptr::null_mut();
    v_res_3422_ =
        l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5(
            v_x_3420_, v_x_3421_,
        );
    lean_dec(v_x_3421_);
    lean_dec(v_x_3420_);
    v_r_3423_ = lean_box((v_res_3422_) as usize);
    return v_r_3423_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0()
-> *mut LeanObject {
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_3425_: *mut LeanObject = core::ptr::null_mut();
    v___x_3424_ = lean_box(0);
    v_dummy_3425_ = l_Lean_Expr_sort___override(v___x_3424_);
    return v_dummy_3425_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2()
-> *mut LeanObject {
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    v___x_3427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1;
    v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
    return v___x_3428_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4()
-> *mut LeanObject {
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    v___x_3430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3;
    v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
    return v___x_3431_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6()
-> *mut LeanObject {
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5;
    v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
    return v___x_3434_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8()
-> *mut LeanObject {
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    v___x_3436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7;
    v___x_3437_ = l_Lean_stringToMessageData(v___x_3436_);
    return v___x_3437_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10()
-> *mut LeanObject {
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    v___x_3439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9;
    v___x_3440_ = l_Lean_stringToMessageData(v___x_3439_);
    return v___x_3440_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12()
-> *mut LeanObject {
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11;
    v___x_3443_ = l_Lean_stringToMessageData(v___x_3442_);
    return v___x_3443_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14()
-> *mut LeanObject {
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    v___x_3445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13;
    v___x_3446_ = l_Lean_stringToMessageData(v___x_3445_);
    return v___x_3446_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16()
-> *mut LeanObject {
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15;
    v___x_3449_ = l_Lean_stringToMessageData(v___x_3448_);
    return v___x_3449_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18()
-> *mut LeanObject {
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    v___x_3451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17;
    v___x_3452_ = l_Lean_stringToMessageData(v___x_3451_);
    return v___x_3452_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20()
-> *mut LeanObject {
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    v___x_3454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19;
    v___x_3455_ = l_Lean_stringToMessageData(v___x_3454_);
    return v___x_3455_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(
    mut v_val_3456_: *mut LeanObject,
    mut v_a_3457_: *mut LeanObject,
    mut v___x_3458_: *mut LeanObject,
    mut v_xs_3459_: *mut LeanObject,
    mut v___x_3460_: *mut LeanObject,
    mut v___x_3461_: *mut LeanObject,
    mut v_as_3462_: *mut LeanObject,
    mut v_sz_3463_: usize,
    mut v_i_3464_: usize,
    mut v_b_3465_: *mut LeanObject,
    mut v___y_3466_: *mut LeanObject,
    mut v___y_3467_: *mut LeanObject,
    mut v___y_3468_: *mut LeanObject,
    mut v___y_3469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: usize = 0;
    let mut v___x_3474_: usize = 0;
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v_fst_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3488_: u8 = 0;
    let mut v_fst_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3492_: u8 = 0;
    let mut v_array_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: u8 = 0;
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3509_: u8 = 0;
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: u8 = 0;
    let mut v_a_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3522_: u8 = 0;
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_privateSpecs_3540_: u8 = 0;
    let mut v___y_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projFn_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: u8 = 0;
    let mut v___x_3565_: u8 = 0;
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: u8 = 0;
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3580_: u8 = 0;
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3584_: u8 = 0;
    let mut v_a_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3588_: u8 = 0;
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3592_: u8 = 0;
    let mut v_a_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3596_: u8 = 0;
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3600_: u8 = 0;
    let mut v_a_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3604_: u8 = 0;
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_3640_: u8 = 0;
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: u8 = 0;
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: u8 = 0;
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: u8 = 0;
    let mut v___x_3648_: u8 = 0;
    let mut v___x_3649_: u8 = 0;
    let mut v___y_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3664_: u8 = 0;
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3668_: u8 = 0;
    let mut v_dummy_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u8 = 0;
    let mut v___x_3682_: u8 = 0;
    let mut v___y_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: u8 = 0;
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3708_: u8 = 0;
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3712_: u8 = 0;
    let mut v___x_3713_: u8 = 0;
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3727_: u8 = 0;
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3741_: u8 = 0;
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3745_: u8 = 0;
    let mut v_isSharedCheck_3746_: u8 = 0;
    let mut v_unused_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3750_: u8 = 0;
    let mut v_unused_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3752_: u8 = 0;
    let mut v_unused_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut v_unused_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3476_ = lean_usize_dec_lt(v_i_3464_, v_sz_3463_);
                if v___x_3476_ == 0 {
                    lean_dec(v___x_3461_);
                    lean_dec(v___x_3460_);
                    lean_dec_ref(v___x_3458_);
                    lean_dec_ref(v_a_3457_);
                    lean_dec(v_val_3456_);
                    v___x_3477_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3477_, 0, v_b_3465_);
                    return v___x_3477_;
                } else {
                    v_snd_3478_ = lean_ctor_get(v_b_3465_, 1);
                    lean_inc(v_snd_3478_);
                    v_snd_3479_ = lean_ctor_get(v_snd_3478_, 1);
                    lean_inc(v_snd_3479_);
                    v_snd_3480_ = lean_ctor_get(v_snd_3479_, 1);
                    lean_inc(v_snd_3480_);
                    v_fst_3481_ = lean_ctor_get(v_b_3465_, 0);
                    v_isSharedCheck_3754_ = (!lean_is_exclusive(v_b_3465_)) as u8;
                    if v_isSharedCheck_3754_ == 0 {
                        v_unused_3755_ = lean_ctor_get(v_b_3465_, 1);
                        lean_dec(v_unused_3755_);
                        v___x_3483_ = v_b_3465_;
                        v_isShared_3484_ = v_isSharedCheck_3754_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_3481_);
                        lean_dec(v_b_3465_);
                        v___x_3483_ = lean_box(0);
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
                v_fst_3485_ = lean_ctor_get(v_snd_3478_, 0);
                v_isSharedCheck_3752_ = (!lean_is_exclusive(v_snd_3478_)) as u8;
                if v_isSharedCheck_3752_ == 0 {
                    v_unused_3753_ = lean_ctor_get(v_snd_3478_, 1);
                    lean_dec(v_unused_3753_);
                    v___x_3487_ = v_snd_3478_;
                    v_isShared_3488_ = v_isSharedCheck_3752_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_fst_3485_);
                    lean_dec(v_snd_3478_);
                    v___x_3487_ = lean_box(0);
                    v_isShared_3488_ = v_isSharedCheck_3752_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_3489_ = lean_ctor_get(v_snd_3479_, 0);
                v_isSharedCheck_3750_ = (!lean_is_exclusive(v_snd_3479_)) as u8;
                if v_isSharedCheck_3750_ == 0 {
                    v_unused_3751_ = lean_ctor_get(v_snd_3479_, 1);
                    lean_dec(v_unused_3751_);
                    v___x_3491_ = v_snd_3479_;
                    v_isShared_3492_ = v_isSharedCheck_3750_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_fst_3489_);
                    lean_dec(v_snd_3479_);
                    v___x_3491_ = lean_box(0);
                    v_isShared_3492_ = v_isSharedCheck_3750_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_array_3493_ = lean_ctor_get(v_snd_3480_, 0);
                v_start_3494_ = lean_ctor_get(v_snd_3480_, 1);
                v_stop_3495_ = lean_ctor_get(v_snd_3480_, 2);
                v___x_3496_ = lean_nat_dec_lt(v_start_3494_, v_stop_3495_);
                if v___x_3496_ == 0 {
                    lean_dec(v___x_3461_);
                    lean_dec(v___x_3460_);
                    lean_dec_ref(v___x_3458_);
                    lean_dec_ref(v_a_3457_);
                    lean_dec(v_val_3456_);
                    if v_isShared_3492_ == 0 {
                        v___x_3498_ = v___x_3491_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_fst_3489_);
                        lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_snd_3480_);
                        v___x_3498_ = v_reuseFailAlloc_3506_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_3495_);
                    lean_inc(v_start_3494_);
                    lean_inc_ref(v_array_3493_);
                    v_isSharedCheck_3746_ = (!lean_is_exclusive(v_snd_3480_)) as u8;
                    if v_isSharedCheck_3746_ == 0 {
                        v_unused_3747_ = lean_ctor_get(v_snd_3480_, 2);
                        lean_dec(v_unused_3747_);
                        v_unused_3748_ = lean_ctor_get(v_snd_3480_, 1);
                        lean_dec(v_unused_3748_);
                        v_unused_3749_ = lean_ctor_get(v_snd_3480_, 0);
                        lean_dec(v_unused_3749_);
                        v___x_3508_ = v_snd_3480_;
                        v_isShared_3509_ = v_isSharedCheck_3746_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v_snd_3480_);
                        v___x_3508_ = lean_box(0);
                        v_isShared_3509_ = v_isSharedCheck_3746_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3488_ == 0 {
                    lean_ctor_set(v___x_3487_, 1, v___x_3498_);
                    v___x_3500_ = v___x_3487_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_fst_3485_);
                    lean_ctor_set(v_reuseFailAlloc_3505_, 1, v___x_3498_);
                    v___x_3500_ = v_reuseFailAlloc_3505_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3484_ == 0 {
                    lean_ctor_set(v___x_3483_, 1, v___x_3500_);
                    v___x_3502_ = v___x_3483_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_fst_3481_);
                    lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3500_);
                    v___x_3502_ = v_reuseFailAlloc_3504_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3503_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3503_, 0, v___x_3502_);
                return v___x_3503_;
            }
            8 => {
                v___x_3510_ = lean_array_fget(v_array_3493_, v_start_3494_);
                lean_inc(v___x_3510_);
                v___x_3511_ = l_Lean_Meta_isProof(
                    v___x_3510_,
                    v___y_3466_,
                    v___y_3467_,
                    v___y_3468_,
                    v___y_3469_,
                );
                if lean_obj_tag(v___x_3511_) == 0 {
                    v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
                    lean_inc(v_a_3512_);
                    lean_dec_ref_known(v___x_3511_, 1);
                    v___x_3513_ = lean_unsigned_to_nat(1);
                    v___x_3514_ = lean_nat_add(v_start_3494_, v___x_3513_);
                    lean_dec(v_start_3494_);
                    if v_isShared_3509_ == 0 {
                        lean_ctor_set(v___x_3508_, 1, v___x_3514_);
                        v___x_3516_ = v___x_3508_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_array_3493_);
                        lean_ctor_set(v_reuseFailAlloc_3737_, 1, v___x_3514_);
                        lean_ctor_set(v_reuseFailAlloc_3737_, 2, v_stop_3495_);
                        v___x_3516_ = v_reuseFailAlloc_3737_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3510_);
                    lean_del_object(v___x_3508_);
                    lean_dec(v_stop_3495_);
                    lean_dec(v_start_3494_);
                    lean_dec_ref(v_array_3493_);
                    lean_del_object(v___x_3491_);
                    lean_dec(v_fst_3489_);
                    lean_del_object(v___x_3487_);
                    lean_dec(v_fst_3485_);
                    lean_del_object(v___x_3483_);
                    lean_dec(v_fst_3481_);
                    lean_dec(v___x_3461_);
                    lean_dec(v___x_3460_);
                    lean_dec_ref(v___x_3458_);
                    lean_dec_ref(v_a_3457_);
                    lean_dec(v_val_3456_);
                    v_a_3738_ = lean_ctor_get(v___x_3511_, 0);
                    v_isSharedCheck_3745_ = (!lean_is_exclusive(v___x_3511_)) as u8;
                    if v_isSharedCheck_3745_ == 0 {
                        v___x_3740_ = v___x_3511_;
                        v_isShared_3741_ = v_isSharedCheck_3745_;
                        state = 38;
                        continue;
                    } else {
                        lean_inc(v_a_3738_);
                        lean_dec(v___x_3511_);
                        v___x_3740_ = lean_box(0);
                        v_isShared_3741_ = v_isSharedCheck_3745_;
                        state = 38;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3517_ = (lean_unbox(v_a_3512_) as u8);
                if v___x_3517_ == 0 {
                    v_a_3518_ = lean_array_uget_borrowed(v_as_3462_, v_i_3464_);
                    v___x_3537_ = l_Lean_Expr_eta(v___x_3510_);
                    v___x_3629_ = l_Lean_Expr_getAppFn(v___x_3537_);
                    v_dummy_3669_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0);
                    v_nargs_3670_ = l_Lean_Expr_getAppNumArgs(v___x_3537_);
                    lean_inc(v_nargs_3670_);
                    v___x_3671_ = lean_mk_array(v_nargs_3670_, v_dummy_3669_);
                    v___x_3672_ = lean_nat_sub(v_nargs_3670_, v___x_3513_);
                    lean_dec(v_nargs_3670_);
                    lean_inc_ref(v___x_3537_);
                    v___x_3673_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v___x_3537_,
                        v___x_3671_,
                        v___x_3672_,
                    );
                    v___x_3713_ = l_Lean_Expr_isConst(v___x_3629_);
                    if v___x_3713_ == 0 {
                        v___x_3714_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18);
                        lean_inc(v_a_3518_);
                        v___x_3715_ = l_Lean_MessageData_ofName(v_a_3518_);
                        v___x_3716_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3716_, 0, v___x_3714_);
                        lean_ctor_set(v___x_3716_, 1, v___x_3715_);
                        v___x_3717_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20);
                        v___x_3718_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3718_, 0, v___x_3716_);
                        lean_ctor_set(v___x_3718_, 1, v___x_3717_);
                        v___x_3719_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_3718_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
                        if lean_obj_tag(v___x_3719_) == 0 {
                            lean_dec_ref_known(v___x_3719_, 1);
                            v___y_3684_ = v___y_3466_;
                            v___y_3685_ = v___y_3467_;
                            v___y_3686_ = v___y_3468_;
                            v___y_3687_ = v___y_3469_;
                            state = 30;
                            continue;
                        } else {
                            lean_dec_ref(v___x_3673_);
                            lean_dec_ref(v___x_3629_);
                            lean_dec_ref(v___x_3537_);
                            lean_dec_ref(v___x_3516_);
                            lean_dec(v_a_3512_);
                            lean_del_object(v___x_3491_);
                            lean_dec(v_fst_3489_);
                            lean_del_object(v___x_3487_);
                            lean_dec(v_fst_3485_);
                            lean_del_object(v___x_3483_);
                            lean_dec(v_fst_3481_);
                            lean_dec(v___x_3461_);
                            lean_dec(v___x_3460_);
                            lean_dec_ref(v___x_3458_);
                            lean_dec_ref(v_a_3457_);
                            lean_dec(v_val_3456_);
                            v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
                            v_isSharedCheck_3727_ = (!lean_is_exclusive(v___x_3719_)) as u8;
                            if v_isSharedCheck_3727_ == 0 {
                                v___x_3722_ = v___x_3719_;
                                v_isShared_3723_ = v_isSharedCheck_3727_;
                                state = 33;
                                continue;
                            } else {
                                lean_inc(v_a_3720_);
                                lean_dec(v___x_3719_);
                                v___x_3722_ = lean_box(0);
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
                    lean_dec(v_a_3512_);
                    lean_dec(v___x_3510_);
                    if v_isShared_3492_ == 0 {
                        lean_ctor_set(v___x_3491_, 1, v___x_3516_);
                        v___x_3729_ = v___x_3491_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_fst_3489_);
                        lean_ctor_set(v_reuseFailAlloc_3736_, 1, v___x_3516_);
                        v___x_3729_ = v_reuseFailAlloc_3736_;
                        state = 35;
                        continue;
                    }
                }
            }
            10 => {
                lean_inc(v___y_3521_);
                lean_inc(v_a_3518_);
                if v_isShared_3492_ == 0 {
                    lean_ctor_set(v___x_3491_, 1, v___y_3521_);
                    lean_ctor_set(v___x_3491_, 0, v_a_3518_);
                    v___x_3524_ = v___x_3491_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3518_);
                    lean_ctor_set(v_reuseFailAlloc_3536_, 1, v___y_3521_);
                    v___x_3524_ = v_reuseFailAlloc_3536_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3525_ = lean_array_push(v_fst_3481_, v___x_3524_);
                lean_inc(v___x_3460_);
                v___x_3526_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3526_, 0, v___y_3521_);
                lean_ctor_set(v___x_3526_, 1, v___x_3460_);
                lean_ctor_set(v___x_3526_, 2, v___y_3520_);
                v___x_3527_ = lean_array_push(v_fst_3485_, v___x_3526_);
                v___x_3528_ = lean_box((v___y_3522_) as usize);
                if v_isShared_3488_ == 0 {
                    lean_ctor_set(v___x_3487_, 1, v___x_3516_);
                    lean_ctor_set(v___x_3487_, 0, v___x_3528_);
                    v___x_3530_ = v___x_3487_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3528_);
                    lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___x_3516_);
                    v___x_3530_ = v_reuseFailAlloc_3535_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3484_ == 0 {
                    lean_ctor_set(v___x_3483_, 1, v___x_3530_);
                    lean_ctor_set(v___x_3483_, 0, v___x_3527_);
                    v___x_3532_ = v___x_3483_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3527_);
                    lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3530_);
                    v___x_3532_ = v_reuseFailAlloc_3534_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_3533_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3533_, 0, v___x_3525_);
                lean_ctor_set(v___x_3533_, 1, v___x_3532_);
                v_a_3472_ = v___x_3533_;
                state = 1;
                continue;
            }
            14 => {
                v___x_3545_ = lean_st_ref_get(v___y_3544_);
                v_env_3546_ = lean_ctor_get(v___x_3545_, 0);
                lean_inc_ref(v_env_3546_);
                lean_dec(v___x_3545_);
                lean_inc(v_a_3518_);
                lean_inc(v_val_3456_);
                v___x_3547_ = l_Lean_getFieldInfo_x3f(v_env_3546_, v_val_3456_, v_a_3518_);
                if lean_obj_tag(v___x_3547_) == 1 {
                    v_val_3548_ = lean_ctor_get(v___x_3547_, 0);
                    lean_inc(v_val_3548_);
                    lean_dec_ref_known(v___x_3547_, 1);
                    v_projFn_3549_ = lean_ctor_get(v_val_3548_, 1);
                    lean_inc(v_projFn_3549_);
                    lean_dec(v_val_3548_);
                    v___x_3550_ = l_Lean_Expr_getAppFn(v_a_3457_);
                    v___x_3551_ = l_Lean_Expr_constLevels_x21(v___x_3550_);
                    lean_dec_ref(v___x_3550_);
                    v___x_3552_ = l_Lean_mkConst(v_projFn_3549_, v___x_3551_);
                    v_dummy_3553_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0);
                    v_nargs_3554_ = l_Lean_Expr_getAppNumArgs(v_a_3457_);
                    lean_inc(v_nargs_3554_);
                    v___x_3555_ = lean_mk_array(v_nargs_3554_, v_dummy_3553_);
                    v___x_3556_ = lean_nat_sub(v_nargs_3554_, v___x_3513_);
                    lean_dec(v_nargs_3554_);
                    lean_inc_ref(v_a_3457_);
                    v___x_3557_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_a_3457_,
                        v___x_3555_,
                        v___x_3556_,
                    );
                    v___x_3558_ = lean_mk_empty_array_with_capacity(v___x_3513_);
                    lean_inc_ref(v___x_3458_);
                    v___x_3559_ = lean_array_push(v___x_3558_, v___x_3458_);
                    v___x_3560_ = l_Array_append___redArg(v___x_3557_, v___x_3559_);
                    lean_dec_ref(v___x_3559_);
                    v___x_3561_ = l_Lean_mkAppN(v___x_3552_, v___x_3560_);
                    lean_dec_ref(v___x_3560_);
                    lean_inc_ref(v___x_3561_);
                    lean_inc_ref(v___x_3537_);
                    v___x_3562_ = l_Lean_Meta_mkEq(
                        v___x_3537_,
                        v___x_3561_,
                        v___y_3541_,
                        v___y_3542_,
                        v___y_3543_,
                        v___y_3544_,
                    );
                    if lean_obj_tag(v___x_3562_) == 0 {
                        v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
                        lean_inc_n(v_a_3563_, 2);
                        lean_dec_ref_known(v___x_3562_, 1);
                        v___x_3564_ = 1;
                        v___x_3565_ = (lean_unbox(v_a_3512_) as u8);
                        lean_dec(v_a_3512_);
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
                        if lean_obj_tag(v___x_3566_) == 0 {
                            v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
                            lean_inc(v_a_3567_);
                            lean_dec_ref_known(v___x_3566_, 1);
                            v___x_3568_ = l_Lean_Meta_isExprDefEq(
                                v___x_3537_,
                                v___x_3561_,
                                v___y_3541_,
                                v___y_3542_,
                                v___y_3543_,
                                v___y_3544_,
                            );
                            if lean_obj_tag(v___x_3568_) == 0 {
                                v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
                                lean_inc(v_a_3569_);
                                lean_dec_ref_known(v___x_3568_, 1);
                                v___x_3570_ = (lean_unbox(v_a_3569_) as u8);
                                lean_dec(v_a_3569_);
                                if v___x_3570_ == 0 {
                                    v___x_3571_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2);
                                    v___x_3572_ = l_Lean_MessageData_ofExpr(v_a_3563_);
                                    v___x_3573_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3573_, 0, v___x_3571_);
                                    lean_ctor_set(v___x_3573_, 1, v___x_3572_);
                                    v___x_3574_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4);
                                    v___x_3575_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3575_, 0, v___x_3573_);
                                    lean_ctor_set(v___x_3575_, 1, v___x_3574_);
                                    v___x_3576_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_3575_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
                                    if lean_obj_tag(v___x_3576_) == 0 {
                                        lean_dec_ref_known(v___x_3576_, 1);
                                        v___y_3520_ = v_a_3567_;
                                        v___y_3521_ = v___y_3539_;
                                        v___y_3522_ = v_privateSpecs_3540_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_dec(v_a_3567_);
                                        lean_dec(v___y_3539_);
                                        lean_dec_ref(v___x_3516_);
                                        lean_del_object(v___x_3491_);
                                        lean_del_object(v___x_3487_);
                                        lean_dec(v_fst_3485_);
                                        lean_del_object(v___x_3483_);
                                        lean_dec(v_fst_3481_);
                                        lean_dec(v___x_3461_);
                                        lean_dec(v___x_3460_);
                                        lean_dec_ref(v___x_3458_);
                                        lean_dec_ref(v_a_3457_);
                                        lean_dec(v_val_3456_);
                                        v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
                                        v_isSharedCheck_3584_ =
                                            (!lean_is_exclusive(v___x_3576_)) as u8;
                                        if v_isSharedCheck_3584_ == 0 {
                                            v___x_3579_ = v___x_3576_;
                                            v_isShared_3580_ = v_isSharedCheck_3584_;
                                            state = 15;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3577_);
                                            lean_dec(v___x_3576_);
                                            v___x_3579_ = lean_box(0);
                                            v_isShared_3580_ = v_isSharedCheck_3584_;
                                            state = 15;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_3563_);
                                    v___y_3520_ = v_a_3567_;
                                    v___y_3521_ = v___y_3539_;
                                    v___y_3522_ = v_privateSpecs_3540_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3567_);
                                lean_dec(v_a_3563_);
                                lean_dec(v___y_3539_);
                                lean_dec_ref(v___x_3516_);
                                lean_del_object(v___x_3491_);
                                lean_del_object(v___x_3487_);
                                lean_dec(v_fst_3485_);
                                lean_del_object(v___x_3483_);
                                lean_dec(v_fst_3481_);
                                lean_dec(v___x_3461_);
                                lean_dec(v___x_3460_);
                                lean_dec_ref(v___x_3458_);
                                lean_dec_ref(v_a_3457_);
                                lean_dec(v_val_3456_);
                                v_a_3585_ = lean_ctor_get(v___x_3568_, 0);
                                v_isSharedCheck_3592_ = (!lean_is_exclusive(v___x_3568_)) as u8;
                                if v_isSharedCheck_3592_ == 0 {
                                    v___x_3587_ = v___x_3568_;
                                    v_isShared_3588_ = v_isSharedCheck_3592_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_3585_);
                                    lean_dec(v___x_3568_);
                                    v___x_3587_ = lean_box(0);
                                    v_isShared_3588_ = v_isSharedCheck_3592_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3563_);
                            lean_dec_ref(v___x_3561_);
                            lean_dec(v___y_3539_);
                            lean_dec_ref(v___x_3537_);
                            lean_dec_ref(v___x_3516_);
                            lean_del_object(v___x_3491_);
                            lean_del_object(v___x_3487_);
                            lean_dec(v_fst_3485_);
                            lean_del_object(v___x_3483_);
                            lean_dec(v_fst_3481_);
                            lean_dec(v___x_3461_);
                            lean_dec(v___x_3460_);
                            lean_dec_ref(v___x_3458_);
                            lean_dec_ref(v_a_3457_);
                            lean_dec(v_val_3456_);
                            v_a_3593_ = lean_ctor_get(v___x_3566_, 0);
                            v_isSharedCheck_3600_ = (!lean_is_exclusive(v___x_3566_)) as u8;
                            if v_isSharedCheck_3600_ == 0 {
                                v___x_3595_ = v___x_3566_;
                                v_isShared_3596_ = v_isSharedCheck_3600_;
                                state = 19;
                                continue;
                            } else {
                                lean_inc(v_a_3593_);
                                lean_dec(v___x_3566_);
                                v___x_3595_ = lean_box(0);
                                v_isShared_3596_ = v_isSharedCheck_3600_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_3561_);
                        lean_dec(v___y_3539_);
                        lean_dec_ref(v___x_3537_);
                        lean_dec_ref(v___x_3516_);
                        lean_dec(v_a_3512_);
                        lean_del_object(v___x_3491_);
                        lean_del_object(v___x_3487_);
                        lean_dec(v_fst_3485_);
                        lean_del_object(v___x_3483_);
                        lean_dec(v_fst_3481_);
                        lean_dec(v___x_3461_);
                        lean_dec(v___x_3460_);
                        lean_dec_ref(v___x_3458_);
                        lean_dec_ref(v_a_3457_);
                        lean_dec(v_val_3456_);
                        v_a_3601_ = lean_ctor_get(v___x_3562_, 0);
                        v_isSharedCheck_3608_ = (!lean_is_exclusive(v___x_3562_)) as u8;
                        if v_isSharedCheck_3608_ == 0 {
                            v___x_3603_ = v___x_3562_;
                            v_isShared_3604_ = v_isSharedCheck_3608_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_3601_);
                            lean_dec(v___x_3562_);
                            v___x_3603_ = lean_box(0);
                            v_isShared_3604_ = v_isSharedCheck_3608_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_3547_);
                    lean_dec(v___y_3539_);
                    lean_dec_ref(v___x_3537_);
                    lean_dec(v_a_3512_);
                    lean_del_object(v___x_3491_);
                    lean_del_object(v___x_3487_);
                    lean_del_object(v___x_3483_);
                    v___x_3609_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6);
                    lean_inc(v_a_3518_);
                    v___x_3610_ = l_Lean_MessageData_ofName(v_a_3518_);
                    v___x_3611_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3611_, 0, v___x_3609_);
                    lean_ctor_set(v___x_3611_, 1, v___x_3610_);
                    v___x_3612_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8);
                    v___x_3613_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3613_, 0, v___x_3611_);
                    lean_ctor_set(v___x_3613_, 1, v___x_3612_);
                    lean_inc(v_val_3456_);
                    v___x_3614_ = l_Lean_MessageData_ofName(v_val_3456_);
                    v___x_3615_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3615_, 0, v___x_3613_);
                    lean_ctor_set(v___x_3615_, 1, v___x_3614_);
                    v___x_3616_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_3615_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
                    if lean_obj_tag(v___x_3616_) == 0 {
                        lean_dec_ref_known(v___x_3616_, 1);
                        v___x_3617_ = lean_box((v_privateSpecs_3540_) as usize);
                        v___x_3618_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3618_, 0, v___x_3617_);
                        lean_ctor_set(v___x_3618_, 1, v___x_3516_);
                        v___x_3619_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3619_, 0, v_fst_3485_);
                        lean_ctor_set(v___x_3619_, 1, v___x_3618_);
                        v___x_3620_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3620_, 0, v_fst_3481_);
                        lean_ctor_set(v___x_3620_, 1, v___x_3619_);
                        v_a_3472_ = v___x_3620_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v___x_3516_);
                        lean_dec(v_fst_3485_);
                        lean_dec(v_fst_3481_);
                        lean_dec(v___x_3461_);
                        lean_dec(v___x_3460_);
                        lean_dec_ref(v___x_3458_);
                        lean_dec_ref(v_a_3457_);
                        lean_dec(v_val_3456_);
                        v_a_3621_ = lean_ctor_get(v___x_3616_, 0);
                        v_isSharedCheck_3628_ = (!lean_is_exclusive(v___x_3616_)) as u8;
                        if v_isSharedCheck_3628_ == 0 {
                            v___x_3623_ = v___x_3616_;
                            v_isShared_3624_ = v_isSharedCheck_3628_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_3621_);
                            lean_dec(v___x_3616_);
                            v___x_3623_ = lean_box(0);
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
                    v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
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
                    v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
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
                    v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
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
                    v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
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
                    v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
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
                v_env_3637_ = lean_ctor_get(v___x_3635_, 0);
                lean_inc_ref(v_env_3637_);
                lean_dec(v___x_3635_);
                v_env_3638_ = lean_ctor_get(v___x_3636_, 0);
                lean_inc_ref(v_env_3638_);
                lean_dec(v___x_3636_);
                v___x_3639_ = l_Lean_Environment_header(v_env_3637_);
                lean_dec_ref(v_env_3637_);
                v_isModule_3640_ = lean_ctor_get_uint8(
                    v___x_3639_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 4) as u32,
                );
                lean_dec_ref(v___x_3639_);
                v___x_3641_ = l_Lean_Expr_constName_x21(v___x_3629_);
                lean_dec_ref(v___x_3629_);
                if v_isModule_3640_ == 0 {
                    lean_dec_ref(v_env_3638_);
                    v___x_3642_ = (lean_unbox(v_fst_3489_) as u8);
                    lean_dec(v_fst_3489_);
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
                    v___x_3644_ = (lean_unbox(v_a_3512_) as u8);
                    lean_inc(v___x_3641_);
                    v___x_3645_ =
                        l_Lean_Environment_find_x3f(v___x_3643_, v___x_3641_, v___x_3644_);
                    if lean_obj_tag(v___x_3645_) == 0 {
                        lean_dec(v_fst_3489_);
                        v___y_3539_ = v___x_3641_;
                        v_privateSpecs_3540_ = v___x_3496_;
                        v___y_3541_ = v___y_3631_;
                        v___y_3542_ = v___y_3632_;
                        v___y_3543_ = v___y_3633_;
                        v___y_3544_ = v___y_3634_;
                        state = 14;
                        continue;
                    } else {
                        v_val_3646_ = lean_ctor_get(v___x_3645_, 0);
                        lean_inc(v_val_3646_);
                        lean_dec_ref_known(v___x_3645_, 1);
                        v___x_3647_ = (lean_unbox(v_a_3512_) as u8);
                        v___x_3648_ = l_Lean_ConstantInfo_hasValue(v_val_3646_, v___x_3647_);
                        lean_dec(v_val_3646_);
                        if v___x_3648_ == 0 {
                            lean_dec(v_fst_3489_);
                            v___y_3539_ = v___x_3641_;
                            v_privateSpecs_3540_ = v___x_3496_;
                            v___y_3541_ = v___y_3631_;
                            v___y_3542_ = v___y_3632_;
                            v___y_3543_ = v___y_3633_;
                            v___y_3544_ = v___y_3634_;
                            state = 14;
                            continue;
                        } else {
                            v___x_3649_ = (lean_unbox(v_fst_3489_) as u8);
                            lean_dec(v_fst_3489_);
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
                v___x_3655_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10);
                lean_inc_ref(v___x_3629_);
                v___x_3656_ = l_Lean_MessageData_ofExpr(v___x_3629_);
                v___x_3657_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3657_, 0, v___x_3655_);
                lean_ctor_set(v___x_3657_, 1, v___x_3656_);
                v___x_3658_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12);
                v___x_3659_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3659_, 0, v___x_3657_);
                lean_ctor_set(v___x_3659_, 1, v___x_3658_);
                v___x_3660_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_3659_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3651_);
                if lean_obj_tag(v___x_3660_) == 0 {
                    lean_dec_ref_known(v___x_3660_, 1);
                    v___y_3631_ = v___y_3652_;
                    v___y_3632_ = v___y_3653_;
                    v___y_3633_ = v___y_3654_;
                    v___y_3634_ = v___y_3651_;
                    state = 25;
                    continue;
                } else {
                    lean_dec_ref(v___x_3629_);
                    lean_dec_ref(v___x_3537_);
                    lean_dec_ref(v___x_3516_);
                    lean_dec(v_a_3512_);
                    lean_del_object(v___x_3491_);
                    lean_dec(v_fst_3489_);
                    lean_del_object(v___x_3487_);
                    lean_dec(v_fst_3485_);
                    lean_del_object(v___x_3483_);
                    lean_dec(v_fst_3481_);
                    lean_dec(v___x_3461_);
                    lean_dec(v___x_3460_);
                    lean_dec_ref(v___x_3458_);
                    lean_dec_ref(v_a_3457_);
                    lean_dec(v_val_3456_);
                    v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
                    v_isSharedCheck_3668_ = (!lean_is_exclusive(v___x_3660_)) as u8;
                    if v_isSharedCheck_3668_ == 0 {
                        v___x_3663_ = v___x_3660_;
                        v_isShared_3664_ = v_isSharedCheck_3668_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_3661_);
                        lean_dec(v___x_3660_);
                        v___x_3663_ = lean_box(0);
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
                    v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
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
                    lean_dec_ref(v___x_3673_);
                    v___y_3651_ = v___y_3678_;
                    v___y_3652_ = v___y_3675_;
                    v___y_3653_ = v___y_3676_;
                    v___y_3654_ = v___y_3677_;
                    state = 26;
                    continue;
                } else {
                    v___x_3682_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(v_xs_3459_, v___x_3673_, v___x_3679_);
                    lean_dec_ref(v___x_3673_);
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
                    v___x_3690_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10);
                    lean_inc_ref(v___x_3629_);
                    v___x_3691_ = l_Lean_MessageData_ofExpr(v___x_3629_);
                    v___x_3692_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3692_, 0, v___x_3690_);
                    lean_ctor_set(v___x_3692_, 1, v___x_3691_);
                    v___x_3693_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14);
                    v___x_3694_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3694_, 0, v___x_3692_);
                    lean_ctor_set(v___x_3694_, 1, v___x_3693_);
                    v___x_3695_ = lean_box(0);
                    v___x_3696_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(v___x_3688_, v___x_3695_);
                    v___x_3697_ = l_Lean_MessageData_ofList(v___x_3696_);
                    v___x_3698_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3698_, 0, v___x_3694_);
                    lean_ctor_set(v___x_3698_, 1, v___x_3697_);
                    v___x_3699_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16);
                    v___x_3700_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3700_, 0, v___x_3698_);
                    lean_ctor_set(v___x_3700_, 1, v___x_3699_);
                    lean_inc(v___x_3461_);
                    v___x_3701_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(v___x_3461_, v___x_3695_);
                    v___x_3702_ = l_Lean_MessageData_ofList(v___x_3701_);
                    v___x_3703_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3703_, 0, v___x_3700_);
                    lean_ctor_set(v___x_3703_, 1, v___x_3702_);
                    v___x_3704_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_3703_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
                    if lean_obj_tag(v___x_3704_) == 0 {
                        lean_dec_ref_known(v___x_3704_, 1);
                        v___y_3675_ = v___y_3684_;
                        v___y_3676_ = v___y_3685_;
                        v___y_3677_ = v___y_3686_;
                        v___y_3678_ = v___y_3687_;
                        state = 29;
                        continue;
                    } else {
                        lean_dec_ref(v___x_3673_);
                        lean_dec_ref(v___x_3629_);
                        lean_dec_ref(v___x_3537_);
                        lean_dec_ref(v___x_3516_);
                        lean_dec(v_a_3512_);
                        lean_del_object(v___x_3491_);
                        lean_dec(v_fst_3489_);
                        lean_del_object(v___x_3487_);
                        lean_dec(v_fst_3485_);
                        lean_del_object(v___x_3483_);
                        lean_dec(v_fst_3481_);
                        lean_dec(v___x_3461_);
                        lean_dec(v___x_3460_);
                        lean_dec_ref(v___x_3458_);
                        lean_dec_ref(v_a_3457_);
                        lean_dec(v_val_3456_);
                        v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
                        v_isSharedCheck_3712_ = (!lean_is_exclusive(v___x_3704_)) as u8;
                        if v_isSharedCheck_3712_ == 0 {
                            v___x_3707_ = v___x_3704_;
                            v_isShared_3708_ = v_isSharedCheck_3712_;
                            state = 31;
                            continue;
                        } else {
                            lean_inc(v_a_3705_);
                            lean_dec(v___x_3704_);
                            v___x_3707_ = lean_box(0);
                            v_isShared_3708_ = v_isSharedCheck_3712_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_3688_);
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
                    v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
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
                    v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
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
                    lean_ctor_set(v___x_3487_, 1, v___x_3729_);
                    v___x_3731_ = v___x_3487_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_fst_3485_);
                    lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___x_3729_);
                    v___x_3731_ = v_reuseFailAlloc_3735_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_3484_ == 0 {
                    lean_ctor_set(v___x_3483_, 1, v___x_3731_);
                    v___x_3733_ = v___x_3483_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_fst_3481_);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___x_3731_);
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
                    v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
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
    mut v_val_3756_: *mut LeanObject,
    mut v_a_3757_: *mut LeanObject,
    mut v___x_3758_: *mut LeanObject,
    mut v_xs_3759_: *mut LeanObject,
    mut v___x_3760_: *mut LeanObject,
    mut v___x_3761_: *mut LeanObject,
    mut v_as_3762_: *mut LeanObject,
    mut v_sz_3763_: *mut LeanObject,
    mut v_i_3764_: *mut LeanObject,
    mut v_b_3765_: *mut LeanObject,
    mut v___y_3766_: *mut LeanObject,
    mut v___y_3767_: *mut LeanObject,
    mut v___y_3768_: *mut LeanObject,
    mut v___y_3769_: *mut LeanObject,
    mut v___y_3770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3771_: usize = 0;
    let mut v_i_boxed_3772_: usize = 0;
    let mut v_res_3773_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3771_ = lean_unbox_usize(v_sz_3763_);
    lean_dec(v_sz_3763_);
    v_i_boxed_3772_ = lean_unbox_usize(v_i_3764_);
    lean_dec(v_i_3764_);
    v_res_3773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(v_val_3756_, v_a_3757_, v___x_3758_, v_xs_3759_, v___x_3760_, v___x_3761_, v_as_3762_, v_sz_boxed_3771_, v_i_boxed_3772_, v_b_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
    lean_dec(v___y_3769_);
    lean_dec_ref(v___y_3768_);
    lean_dec(v___y_3767_);
    lean_dec_ref(v___y_3766_);
    lean_dec_ref(v_as_3762_);
    lean_dec_ref(v_xs_3759_);
    return v_res_3773_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6()
-> *mut LeanObject {
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    v___x_3784_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3;
    v___x_3785_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5;
    v___x_3786_ = l_Lean_Name_append(v___x_3785_, v___x_3784_);
    return v___x_3786_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8()
-> *mut LeanObject {
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    v___x_3788_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7;
    v___x_3789_ = l_Lean_stringToMessageData(v___x_3788_);
    return v___x_3789_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10()
-> *mut LeanObject {
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    v___x_3791_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9;
    v___x_3792_ = l_Lean_stringToMessageData(v___x_3791_);
    return v___x_3792_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12()
-> *mut LeanObject {
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    v___x_3794_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11;
    v___x_3795_ = l_Lean_stringToMessageData(v___x_3794_);
    return v___x_3795_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14()
-> *mut LeanObject {
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    v___x_3797_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13;
    v___x_3798_ = l_Lean_stringToMessageData(v___x_3797_);
    return v___x_3798_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18()
-> *mut LeanObject {
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    v___x_3802_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17;
    v___x_3803_ = l_Lean_stringToMessageData(v___x_3802_);
    return v___x_3803_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20()
-> *mut LeanObject {
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    v___x_3805_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__19;
    v___x_3806_ = l_Lean_stringToMessageData(v___x_3805_);
    return v___x_3806_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1(
    mut v_type_3807_: *mut LeanObject,
    mut v_val_3808_: *mut LeanObject,
    mut v_levelParams_3809_: *mut LeanObject,
    mut v_name_3810_: *mut LeanObject,
    mut v_val_3811_: *mut LeanObject,
    mut v___x_3812_: u8,
    mut v_instName_3813_: *mut LeanObject,
    mut v_a_3814_: *mut LeanObject,
    mut v_xs_3815_: *mut LeanObject,
    mut v_body_3816_: *mut LeanObject,
    mut v___y_3817_: *mut LeanObject,
    mut v___y_3818_: *mut LeanObject,
    mut v___y_3819_: *mut LeanObject,
    mut v___y_3820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: u8 = 0;
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldNames_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3878_: usize = 0;
    let mut v___x_3879_: usize = 0;
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3885_: u8 = 0;
    let mut v_fst_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v_fst_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3896_: u8 = 0;
    let mut v_fst_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3900_: u8 = 0;
    let mut v_inheritedTraceOptions_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3919_: usize = 0;
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3933_: u8 = 0;
    let mut v_unused_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_unused_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut v_unused_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3942_: u8 = 0;
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3957_: u8 = 0;
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3961_: u8 = 0;
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: u8 = 0;
    let mut v___x_3964_: u8 = 0;
    let mut v_a_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3968_: u8 = 0;
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut v_a_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3976_: u8 = 0;
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3979_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_3852_) == 0 {
                    v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
                    lean_inc(v_a_3853_);
                    lean_dec_ref_known(v___x_3852_, 1);
                    lean_inc_ref(v_body_3816_);
                    v___x_3854_ = l_Lean_Meta_isConstructorApp(
                        v_body_3816_,
                        v___y_3817_,
                        v___y_3818_,
                        v___y_3819_,
                        v___y_3820_,
                    );
                    if lean_obj_tag(v___x_3854_) == 0 {
                        v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
                        lean_inc(v_a_3855_);
                        lean_dec_ref_known(v___x_3854_, 1);
                        v___x_3856_ = lean_box(0);
                        lean_inc(v_levelParams_3809_);
                        v___x_3857_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__2(v_levelParams_3809_, v___x_3856_);
                        lean_inc(v___x_3857_);
                        v___x_3858_ = l_Lean_mkConst(v_name_3810_, v___x_3857_);
                        v___x_3859_ = l_Lean_mkAppN(v___x_3858_, v_xs_3815_);
                        v___x_3962_ = lean_array_get_size(v_xs_3815_);
                        v___x_3963_ = lean_nat_dec_eq(v___x_3962_, v_a_3814_);
                        if v___x_3963_ == 0 {
                            lean_dec_ref(v___x_3859_);
                            lean_dec(v___x_3857_);
                            lean_dec(v_a_3855_);
                            lean_dec(v_a_3853_);
                            lean_dec_ref(v_body_3816_);
                            lean_dec(v_levelParams_3809_);
                            lean_dec(v_val_3808_);
                            state = 14;
                            continue;
                        } else {
                            v___x_3964_ = (lean_unbox(v_a_3855_) as u8);
                            lean_dec(v_a_3855_);
                            if v___x_3964_ == 0 {
                                lean_dec_ref(v___x_3859_);
                                lean_dec(v___x_3857_);
                                lean_dec(v_a_3853_);
                                lean_dec_ref(v_body_3816_);
                                lean_dec(v_levelParams_3809_);
                                lean_dec(v_val_3808_);
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
                        lean_dec(v_a_3853_);
                        lean_dec_ref(v_body_3816_);
                        lean_dec(v_instName_3813_);
                        lean_dec(v_name_3810_);
                        lean_dec(v_levelParams_3809_);
                        lean_dec(v_val_3808_);
                        v_a_3965_ = lean_ctor_get(v___x_3854_, 0);
                        v_isSharedCheck_3972_ = (!lean_is_exclusive(v___x_3854_)) as u8;
                        if v_isSharedCheck_3972_ == 0 {
                            v___x_3967_ = v___x_3854_;
                            v_isShared_3968_ = v_isSharedCheck_3972_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_3965_);
                            lean_dec(v___x_3854_);
                            v___x_3967_ = lean_box(0);
                            v_isShared_3968_ = v_isSharedCheck_3972_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_body_3816_);
                    lean_dec(v_instName_3813_);
                    lean_dec(v_name_3810_);
                    lean_dec(v_levelParams_3809_);
                    lean_dec(v_val_3808_);
                    v_a_3973_ = lean_ctor_get(v___x_3852_, 0);
                    v_isSharedCheck_3980_ = (!lean_is_exclusive(v___x_3852_)) as u8;
                    if v_isSharedCheck_3980_ == 0 {
                        v___x_3975_ = v___x_3852_;
                        v_isShared_3976_ = v_isSharedCheck_3980_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_3973_);
                        lean_dec(v___x_3852_);
                        v___x_3975_ = lean_box(0);
                        v_isShared_3976_ = v_isSharedCheck_3980_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3826_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_3826_, 0, v_val_3808_);
                lean_ctor_set(v___x_3826_, 1, v___y_3824_);
                lean_ctor_set(v___x_3826_, 2, v___y_3825_);
                v___x_3827_ = (lean_unbox(v___y_3823_) as u8);
                lean_dec(v___y_3823_);
                lean_ctor_set_uint8(
                    v___x_3826_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3827_,
                );
                v___x_3828_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3828_, 0, v___x_3826_);
                return v___x_3828_;
            }
            2 => {
                lean_inc_ref(v___y_3839_);
                v___x_3840_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3840_, 0, v___y_3839_);
                v___x_3841_ = l_Lean_MessageData_ofFormat(v___x_3840_);
                v___x_3842_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3842_, 0, v___y_3834_);
                lean_ctor_set(v___x_3842_, 1, v___x_3841_);
                lean_inc(v___y_3833_);
                v___x_3843_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v___y_3833_, v___x_3842_, v___y_3835_, v___y_3830_, v___y_3837_, v___y_3831_);
                if lean_obj_tag(v___x_3843_) == 0 {
                    lean_dec_ref_known(v___x_3843_, 1);
                    v___y_3823_ = v___y_3832_;
                    v___y_3824_ = v___y_3836_;
                    v___y_3825_ = v___y_3838_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_3838_);
                    lean_dec(v___y_3836_);
                    lean_dec(v___y_3832_);
                    lean_dec(v_val_3808_);
                    v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
                    v_isSharedCheck_3851_ = (!lean_is_exclusive(v___x_3843_)) as u8;
                    if v_isSharedCheck_3851_ == 0 {
                        v___x_3846_ = v___x_3843_;
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3844_);
                        lean_dec(v___x_3843_);
                        v___x_3846_ = lean_box(0);
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
                    v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
                    v___x_3849_ = v_reuseFailAlloc_3850_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3849_;
            }
            5 => {
                v_fieldNames_3865_ = lean_ctor_get(v_val_3811_, 1);
                v___x_3866_ = lean_unsigned_to_nat(0);
                v___x_3867_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0;
                v___x_3868_ = lean_array_get_size(v_fieldNames_3865_);
                v_dummy_3869_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0);
                v___x_3870_ = lean_mk_array(v___x_3868_, v_dummy_3869_);
                v___x_3871_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(
                    v___x_3868_,
                    v_body_3816_,
                    v___x_3870_,
                );
                v___x_3872_ = lean_array_get_size(v___x_3871_);
                v___x_3873_ = l_Array_toSubarray___redArg(v___x_3871_, v___x_3866_, v___x_3872_);
                v___x_3874_ = lean_box((v___x_3812_) as usize);
                v___x_3875_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3875_, 0, v___x_3874_);
                lean_ctor_set(v___x_3875_, 1, v___x_3873_);
                v___x_3876_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3876_, 0, v___x_3867_);
                lean_ctor_set(v___x_3876_, 1, v___x_3875_);
                v___x_3877_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3877_, 0, v___x_3867_);
                lean_ctor_set(v___x_3877_, 1, v___x_3876_);
                v_sz_3878_ = lean_array_size(v_fieldNames_3865_);
                v___x_3879_ = 0usize;
                lean_inc(v_val_3808_);
                v___x_3880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(v_val_3808_, v_a_3853_, v___x_3859_, v_xs_3815_, v_levelParams_3809_, v___x_3857_, v_fieldNames_3865_, v_sz_3878_, v___x_3879_, v___x_3877_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
                if lean_obj_tag(v___x_3880_) == 0 {
                    v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
                    lean_inc(v_a_3881_);
                    lean_dec_ref_known(v___x_3880_, 1);
                    v_snd_3882_ = lean_ctor_get(v_a_3881_, 1);
                    lean_inc(v_snd_3882_);
                    v_snd_3883_ = lean_ctor_get(v_snd_3882_, 1);
                    lean_inc(v_snd_3883_);
                    v_options_3884_ = lean_ctor_get(v___y_3863_, 2);
                    v_hasTrace_3885_ = lean_ctor_get_uint8(
                        v_options_3884_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3885_ == 0 {
                        lean_dec(v_instName_3813_);
                        v_fst_3886_ = lean_ctor_get(v_a_3881_, 0);
                        lean_inc(v_fst_3886_);
                        lean_dec(v_a_3881_);
                        v_fst_3887_ = lean_ctor_get(v_snd_3882_, 0);
                        lean_inc(v_fst_3887_);
                        lean_dec(v_snd_3882_);
                        v_fst_3888_ = lean_ctor_get(v_snd_3883_, 0);
                        lean_inc(v_fst_3888_);
                        lean_dec(v_snd_3883_);
                        v___y_3823_ = v_fst_3888_;
                        v___y_3824_ = v_fst_3886_;
                        v___y_3825_ = v_fst_3887_;
                        state = 1;
                        continue;
                    } else {
                        v_fst_3889_ = lean_ctor_get(v_a_3881_, 0);
                        v_isSharedCheck_3937_ = (!lean_is_exclusive(v_a_3881_)) as u8;
                        if v_isSharedCheck_3937_ == 0 {
                            v_unused_3938_ = lean_ctor_get(v_a_3881_, 1);
                            lean_dec(v_unused_3938_);
                            v___x_3891_ = v_a_3881_;
                            v_isShared_3892_ = v_isSharedCheck_3937_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_fst_3889_);
                            lean_dec(v_a_3881_);
                            v___x_3891_ = lean_box(0);
                            v_isShared_3892_ = v_isSharedCheck_3937_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_instName_3813_);
                    lean_dec(v_val_3808_);
                    v_a_3939_ = lean_ctor_get(v___x_3880_, 0);
                    v_isSharedCheck_3946_ = (!lean_is_exclusive(v___x_3880_)) as u8;
                    if v_isSharedCheck_3946_ == 0 {
                        v___x_3941_ = v___x_3880_;
                        v_isShared_3942_ = v_isSharedCheck_3946_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_3939_);
                        lean_dec(v___x_3880_);
                        v___x_3941_ = lean_box(0);
                        v_isShared_3942_ = v_isSharedCheck_3946_;
                        state = 12;
                        continue;
                    }
                }
            }
            6 => {
                v_fst_3893_ = lean_ctor_get(v_snd_3882_, 0);
                v_isSharedCheck_3935_ = (!lean_is_exclusive(v_snd_3882_)) as u8;
                if v_isSharedCheck_3935_ == 0 {
                    v_unused_3936_ = lean_ctor_get(v_snd_3882_, 1);
                    lean_dec(v_unused_3936_);
                    v___x_3895_ = v_snd_3882_;
                    v_isShared_3896_ = v_isSharedCheck_3935_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_fst_3893_);
                    lean_dec(v_snd_3882_);
                    v___x_3895_ = lean_box(0);
                    v_isShared_3896_ = v_isSharedCheck_3935_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_3897_ = lean_ctor_get(v_snd_3883_, 0);
                v_isSharedCheck_3933_ = (!lean_is_exclusive(v_snd_3883_)) as u8;
                if v_isSharedCheck_3933_ == 0 {
                    v_unused_3934_ = lean_ctor_get(v_snd_3883_, 1);
                    lean_dec(v_unused_3934_);
                    v___x_3899_ = v_snd_3883_;
                    v_isShared_3900_ = v_isSharedCheck_3933_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_fst_3897_);
                    lean_dec(v_snd_3883_);
                    v___x_3899_ = lean_box(0);
                    v_isShared_3900_ = v_isSharedCheck_3933_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_inheritedTraceOptions_3901_ = lean_ctor_get(v___y_3863_, 13);
                v___x_3902_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3;
                v___x_3903_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6);
                v___x_3904_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_3901_,
                    v_options_3884_,
                    v___x_3903_,
                );
                if v___x_3904_ == 0 {
                    lean_del_object(v___x_3899_);
                    lean_del_object(v___x_3895_);
                    lean_del_object(v___x_3891_);
                    lean_dec(v_instName_3813_);
                    v___y_3823_ = v_fst_3897_;
                    v___y_3824_ = v_fst_3889_;
                    v___y_3825_ = v_fst_3893_;
                    state = 1;
                    continue;
                } else {
                    v___x_3905_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8);
                    v___x_3906_ = l_Lean_MessageData_ofName(v_instName_3813_);
                    if v_isShared_3900_ == 0 {
                        lean_ctor_set_tag(v___x_3899_, 7);
                        lean_ctor_set(v___x_3899_, 1, v___x_3906_);
                        lean_ctor_set(v___x_3899_, 0, v___x_3905_);
                        v___x_3908_ = v___x_3899_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3932_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3905_);
                        lean_ctor_set(v_reuseFailAlloc_3932_, 1, v___x_3906_);
                        v___x_3908_ = v_reuseFailAlloc_3932_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3909_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10);
                if v_isShared_3896_ == 0 {
                    lean_ctor_set_tag(v___x_3895_, 7);
                    lean_ctor_set(v___x_3895_, 1, v___x_3909_);
                    lean_ctor_set(v___x_3895_, 0, v___x_3908_);
                    v___x_3911_ = v___x_3895_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3908_);
                    lean_ctor_set(v_reuseFailAlloc_3931_, 1, v___x_3909_);
                    v___x_3911_ = v_reuseFailAlloc_3931_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                lean_inc(v_fst_3889_);
                v___x_3912_ = lean_array_to_list(v_fst_3889_);
                v___x_3913_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(v___x_3912_, v___x_3856_);
                v___x_3914_ = l_Lean_MessageData_ofList(v___x_3913_);
                if v_isShared_3892_ == 0 {
                    lean_ctor_set_tag(v___x_3891_, 7);
                    lean_ctor_set(v___x_3891_, 1, v___x_3914_);
                    lean_ctor_set(v___x_3891_, 0, v___x_3911_);
                    v___x_3916_ = v___x_3891_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3911_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 1, v___x_3914_);
                    v___x_3916_ = v_reuseFailAlloc_3930_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3917_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12);
                v___x_3918_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3918_, 0, v___x_3916_);
                lean_ctor_set(v___x_3918_, 1, v___x_3917_);
                v_sz_3919_ = lean_array_size(v_fst_3893_);
                lean_inc(v_fst_3893_);
                v___x_3920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9(v_sz_3919_, v___x_3879_, v_fst_3893_);
                v___x_3921_ = lean_array_to_list(v___x_3920_);
                v___x_3922_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10(v___x_3921_, v___x_3856_);
                v___x_3923_ = l_Lean_MessageData_ofList(v___x_3922_);
                v___x_3924_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3924_, 0, v___x_3918_);
                lean_ctor_set(v___x_3924_, 1, v___x_3923_);
                v___x_3925_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14);
                v___x_3926_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3926_, 0, v___x_3924_);
                lean_ctor_set(v___x_3926_, 1, v___x_3925_);
                v___x_3927_ = (lean_unbox(v_fst_3897_) as u8);
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
                    v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
                    v___x_3944_ = v_reuseFailAlloc_3945_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3944_;
            }
            14 => {
                v___x_3948_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18);
                v___x_3949_ = l_Lean_MessageData_ofConstName(v_instName_3813_, v___x_3812_);
                v___x_3950_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                lean_ctor_set(v___x_3950_, 1, v___x_3949_);
                v___x_3951_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20);
                v___x_3952_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3952_, 0, v___x_3950_);
                lean_ctor_set(v___x_3952_, 1, v___x_3951_);
                v___x_3953_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_3952_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
                v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
                v_isSharedCheck_3961_ = (!lean_is_exclusive(v___x_3953_)) as u8;
                if v_isSharedCheck_3961_ == 0 {
                    v___x_3956_ = v___x_3953_;
                    v_isShared_3957_ = v_isSharedCheck_3961_;
                    state = 15;
                    continue;
                } else {
                    lean_inc(v_a_3954_);
                    lean_dec(v___x_3953_);
                    v___x_3956_ = lean_box(0);
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
                    v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
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
                    v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
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
                    v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
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
    mut v_type_3981_: *mut LeanObject,
    mut v_val_3982_: *mut LeanObject,
    mut v_levelParams_3983_: *mut LeanObject,
    mut v_name_3984_: *mut LeanObject,
    mut v_val_3985_: *mut LeanObject,
    mut v___x_3986_: *mut LeanObject,
    mut v_instName_3987_: *mut LeanObject,
    mut v_a_3988_: *mut LeanObject,
    mut v_xs_3989_: *mut LeanObject,
    mut v_body_3990_: *mut LeanObject,
    mut v___y_3991_: *mut LeanObject,
    mut v___y_3992_: *mut LeanObject,
    mut v___y_3993_: *mut LeanObject,
    mut v___y_3994_: *mut LeanObject,
    mut v___y_3995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_20080__boxed_3996_: u8 = 0;
    let mut v_res_3997_: *mut LeanObject = core::ptr::null_mut();
    v___x_20080__boxed_3996_ = (lean_unbox(v___x_3986_) as u8);
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
    lean_dec(v___y_3994_);
    lean_dec_ref(v___y_3993_);
    lean_dec(v___y_3992_);
    lean_dec_ref(v___y_3991_);
    lean_dec_ref(v_xs_3989_);
    lean_dec(v_a_3988_);
    lean_dec_ref(v_val_3985_);
    return v_res_3997_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    v___x_3998_ = l_instMonadEIO(lean_box(0));
    return v___x_3998_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(
    mut v_msg_4003_: *mut LeanObject,
    mut v___y_4004_: *mut LeanObject,
    mut v___y_4005_: *mut LeanObject,
    mut v___y_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v_toFunctor_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4021_: u8 = 0;
    let mut v___f_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4038_: u8 = 0;
    let mut v_toFunctor_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4045_: u8 = 0;
    let mut v___f_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_17799__overap_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4064_: u8 = 0;
    let mut v_unused_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4066_: u8 = 0;
    let mut v_unused_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4070_: u8 = 0;
    let mut v_unused_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4072_: u8 = 0;
    let mut v_unused_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4009_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0_once), _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0);
                v___x_4010_ = l_StateRefT_x27_instMonad___redArg(v___x_4009_);
                v_toApplicative_4011_ = lean_ctor_get(v___x_4010_, 0);
                v_isSharedCheck_4072_ = (!lean_is_exclusive(v___x_4010_)) as u8;
                if v_isSharedCheck_4072_ == 0 {
                    v_unused_4073_ = lean_ctor_get(v___x_4010_, 1);
                    lean_dec(v_unused_4073_);
                    v___x_4013_ = v___x_4010_;
                    v_isShared_4014_ = v_isSharedCheck_4072_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4011_);
                    lean_dec(v___x_4010_);
                    v___x_4013_ = lean_box(0);
                    v_isShared_4014_ = v_isSharedCheck_4072_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4015_ = lean_ctor_get(v_toApplicative_4011_, 0);
                v_toSeq_4016_ = lean_ctor_get(v_toApplicative_4011_, 2);
                v_toSeqLeft_4017_ = lean_ctor_get(v_toApplicative_4011_, 3);
                v_toSeqRight_4018_ = lean_ctor_get(v_toApplicative_4011_, 4);
                v_isSharedCheck_4070_ = (!lean_is_exclusive(v_toApplicative_4011_)) as u8;
                if v_isSharedCheck_4070_ == 0 {
                    v_unused_4071_ = lean_ctor_get(v_toApplicative_4011_, 1);
                    lean_dec(v_unused_4071_);
                    v___x_4020_ = v_toApplicative_4011_;
                    v_isShared_4021_ = v_isSharedCheck_4070_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4018_);
                    lean_inc(v_toSeqLeft_4017_);
                    lean_inc(v_toSeq_4016_);
                    lean_inc(v_toFunctor_4015_);
                    lean_dec(v_toApplicative_4011_);
                    v___x_4020_ = lean_box(0);
                    v_isShared_4021_ = v_isSharedCheck_4070_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4022_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1;
                v___f_4023_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_4015_);
                v___f_4024_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4024_, 0, v_toFunctor_4015_);
                v___f_4025_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4025_, 0, v_toFunctor_4015_);
                v___x_4026_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4026_, 0, v___f_4024_);
                lean_ctor_set(v___x_4026_, 1, v___f_4025_);
                v___f_4027_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4027_, 0, v_toSeqRight_4018_);
                v___f_4028_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4028_, 0, v_toSeqLeft_4017_);
                v___f_4029_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4029_, 0, v_toSeq_4016_);
                if v_isShared_4021_ == 0 {
                    lean_ctor_set(v___x_4020_, 4, v___f_4027_);
                    lean_ctor_set(v___x_4020_, 3, v___f_4028_);
                    lean_ctor_set(v___x_4020_, 2, v___f_4029_);
                    lean_ctor_set(v___x_4020_, 1, v___f_4022_);
                    lean_ctor_set(v___x_4020_, 0, v___x_4026_);
                    v___x_4031_ = v___x_4020_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4026_);
                    lean_ctor_set(v_reuseFailAlloc_4069_, 1, v___f_4022_);
                    lean_ctor_set(v_reuseFailAlloc_4069_, 2, v___f_4029_);
                    lean_ctor_set(v_reuseFailAlloc_4069_, 3, v___f_4028_);
                    lean_ctor_set(v_reuseFailAlloc_4069_, 4, v___f_4027_);
                    v___x_4031_ = v_reuseFailAlloc_4069_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4014_ == 0 {
                    lean_ctor_set(v___x_4013_, 1, v___f_4023_);
                    lean_ctor_set(v___x_4013_, 0, v___x_4031_);
                    v___x_4033_ = v___x_4013_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4031_);
                    lean_ctor_set(v_reuseFailAlloc_4068_, 1, v___f_4023_);
                    v___x_4033_ = v_reuseFailAlloc_4068_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4034_ = l_StateRefT_x27_instMonad___redArg(v___x_4033_);
                v_toApplicative_4035_ = lean_ctor_get(v___x_4034_, 0);
                v_isSharedCheck_4066_ = (!lean_is_exclusive(v___x_4034_)) as u8;
                if v_isSharedCheck_4066_ == 0 {
                    v_unused_4067_ = lean_ctor_get(v___x_4034_, 1);
                    lean_dec(v_unused_4067_);
                    v___x_4037_ = v___x_4034_;
                    v_isShared_4038_ = v_isSharedCheck_4066_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4035_);
                    lean_dec(v___x_4034_);
                    v___x_4037_ = lean_box(0);
                    v_isShared_4038_ = v_isSharedCheck_4066_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4039_ = lean_ctor_get(v_toApplicative_4035_, 0);
                v_toSeq_4040_ = lean_ctor_get(v_toApplicative_4035_, 2);
                v_toSeqLeft_4041_ = lean_ctor_get(v_toApplicative_4035_, 3);
                v_toSeqRight_4042_ = lean_ctor_get(v_toApplicative_4035_, 4);
                v_isSharedCheck_4064_ = (!lean_is_exclusive(v_toApplicative_4035_)) as u8;
                if v_isSharedCheck_4064_ == 0 {
                    v_unused_4065_ = lean_ctor_get(v_toApplicative_4035_, 1);
                    lean_dec(v_unused_4065_);
                    v___x_4044_ = v_toApplicative_4035_;
                    v_isShared_4045_ = v_isSharedCheck_4064_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4042_);
                    lean_inc(v_toSeqLeft_4041_);
                    lean_inc(v_toSeq_4040_);
                    lean_inc(v_toFunctor_4039_);
                    lean_dec(v_toApplicative_4035_);
                    v___x_4044_ = lean_box(0);
                    v_isShared_4045_ = v_isSharedCheck_4064_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4046_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3;
                v___f_4047_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4;
                lean_inc_ref(v_toFunctor_4039_);
                v___f_4048_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4048_, 0, v_toFunctor_4039_);
                v___f_4049_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4049_, 0, v_toFunctor_4039_);
                v___x_4050_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4050_, 0, v___f_4048_);
                lean_ctor_set(v___x_4050_, 1, v___f_4049_);
                v___f_4051_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4051_, 0, v_toSeqRight_4042_);
                v___f_4052_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4052_, 0, v_toSeqLeft_4041_);
                v___f_4053_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4053_, 0, v_toSeq_4040_);
                if v_isShared_4045_ == 0 {
                    lean_ctor_set(v___x_4044_, 4, v___f_4051_);
                    lean_ctor_set(v___x_4044_, 3, v___f_4052_);
                    lean_ctor_set(v___x_4044_, 2, v___f_4053_);
                    lean_ctor_set(v___x_4044_, 1, v___f_4046_);
                    lean_ctor_set(v___x_4044_, 0, v___x_4050_);
                    v___x_4055_ = v___x_4044_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4050_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 1, v___f_4046_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 2, v___f_4053_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 3, v___f_4052_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 4, v___f_4051_);
                    v___x_4055_ = v_reuseFailAlloc_4063_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4038_ == 0 {
                    lean_ctor_set(v___x_4037_, 1, v___f_4047_);
                    lean_ctor_set(v___x_4037_, 0, v___x_4055_);
                    v___x_4057_ = v___x_4037_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4055_);
                    lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___f_4047_);
                    v___x_4057_ = v_reuseFailAlloc_4062_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4058_ = lean_box(0);
                v___x_4059_ = l_instInhabitedOfMonad___redArg(v___x_4057_, v___x_4058_);
                v___x_17799__overap_4060_ = lean_panic_fn_borrowed(v___x_4059_, v_msg_4003_);
                lean_dec(v___x_4059_);
                lean_inc(v___y_4007_);
                lean_inc_ref(v___y_4006_);
                lean_inc(v___y_4005_);
                lean_inc_ref(v___y_4004_);
                v___x_4061_ = lean_apply_5(
                    v___x_17799__overap_4060_,
                    v___y_4004_,
                    v___y_4005_,
                    v___y_4006_,
                    v___y_4007_,
                    lean_box(0),
                );
                return v___x_4061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___boxed(
    mut v_msg_4074_: *mut LeanObject,
    mut v___y_4075_: *mut LeanObject,
    mut v___y_4076_: *mut LeanObject,
    mut v___y_4077_: *mut LeanObject,
    mut v___y_4078_: *mut LeanObject,
    mut v___y_4079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4080_: *mut LeanObject = core::ptr::null_mut();
    v_res_4080_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(v_msg_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
    lean_dec(v___y_4078_);
    lean_dec_ref(v___y_4077_);
    lean_dec(v___y_4076_);
    lean_dec_ref(v___y_4075_);
    return v_res_4080_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    v___x_4082_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0;
    v___x_4083_ = l_Lean_stringToMessageData(v___x_4082_);
    return v___x_4083_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    v___x_4085_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2;
    v___x_4086_ = l_Lean_stringToMessageData(v___x_4085_);
    return v___x_4086_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7()
-> *mut LeanObject {
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    v___x_4090_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6;
    v___x_4091_ = lean_unsigned_to_nat(11);
    v___x_4092_ = lean_unsigned_to_nat(115);
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
    mut v_constName_4096_: *mut LeanObject,
    mut v___y_4097_: *mut LeanObject,
    mut v___y_4098_: *mut LeanObject,
    mut v___y_4099_: *mut LeanObject,
    mut v___y_4100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: u8 = 0;
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: u8 = 0;
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_4115_: u8 = 0;
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4120_: u8 = 0;
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4124_: u8 = 0;
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4130_: u8 = 0;
    let mut v_val_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4135_: u8 = 0;
    let mut v_a_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4139_: u8 = 0;
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4143_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4110_ = lean_st_ref_get(v___y_4100_);
                v_env_4111_ = lean_ctor_get(v___x_4110_, 0);
                lean_inc_ref(v_env_4111_);
                lean_dec(v___x_4110_);
                v___x_4112_ = 0;
                lean_inc(v_constName_4096_);
                v___x_4113_ =
                    l_Lean_Environment_findAsync_x3f(v_env_4111_, v_constName_4096_, v___x_4112_);
                if lean_obj_tag(v___x_4113_) == 1 {
                    v_val_4114_ = lean_ctor_get(v___x_4113_, 0);
                    lean_inc(v_val_4114_);
                    lean_dec_ref_known(v___x_4113_, 1);
                    v_kind_4115_ = lean_ctor_get_uint8(
                        v_val_4114_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    if v_kind_4115_ == 0 {
                        v___x_4116_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4114_);
                        if lean_obj_tag(v___x_4116_) == 1 {
                            lean_dec(v_constName_4096_);
                            v_val_4117_ = lean_ctor_get(v___x_4116_, 0);
                            v_isSharedCheck_4124_ = (!lean_is_exclusive(v___x_4116_)) as u8;
                            if v_isSharedCheck_4124_ == 0 {
                                v___x_4119_ = v___x_4116_;
                                v_isShared_4120_ = v_isSharedCheck_4124_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_val_4117_);
                                lean_dec(v___x_4116_);
                                v___x_4119_ = lean_box(0);
                                v_isShared_4120_ = v_isSharedCheck_4124_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_4116_);
                            v___x_4125_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7_once), _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7);
                            v___x_4126_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(v___x_4125_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
                            if lean_obj_tag(v___x_4126_) == 0 {
                                v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
                                v_isSharedCheck_4135_ = (!lean_is_exclusive(v___x_4126_)) as u8;
                                if v_isSharedCheck_4135_ == 0 {
                                    v___x_4129_ = v___x_4126_;
                                    v_isShared_4130_ = v_isSharedCheck_4135_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_4127_);
                                    lean_dec(v___x_4126_);
                                    v___x_4129_ = lean_box(0);
                                    v_isShared_4130_ = v_isSharedCheck_4135_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v_constName_4096_);
                                v_a_4136_ = lean_ctor_get(v___x_4126_, 0);
                                v_isSharedCheck_4143_ = (!lean_is_exclusive(v___x_4126_)) as u8;
                                if v_isSharedCheck_4143_ == 0 {
                                    v___x_4138_ = v___x_4126_;
                                    v_isShared_4139_ = v_isSharedCheck_4143_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_4136_);
                                    lean_dec(v___x_4126_);
                                    v___x_4138_ = lean_box(0);
                                    v_isShared_4139_ = v_isSharedCheck_4143_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_val_4114_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4113_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4103_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once), _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1);
                v___x_4104_ = 0;
                v___x_4105_ = l_Lean_MessageData_ofConstName(v_constName_4096_, v___x_4104_);
                v___x_4106_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4106_, 0, v___x_4103_);
                lean_ctor_set(v___x_4106_, 1, v___x_4105_);
                v___x_4107_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3_once), _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3);
                v___x_4108_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4108_, 0, v___x_4106_);
                lean_ctor_set(v___x_4108_, 1, v___x_4107_);
                v___x_4109_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_4108_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
                return v___x_4109_;
            }
            2 => {
                if v_isShared_4120_ == 0 {
                    lean_ctor_set_tag(v___x_4119_, 0);
                    v___x_4122_ = v___x_4119_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_val_4117_);
                    v___x_4122_ = v_reuseFailAlloc_4123_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4122_;
            }
            4 => {
                if lean_obj_tag(v_a_4127_) == 0 {
                    lean_del_object(v___x_4129_);
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_constName_4096_);
                    v_val_4131_ = lean_ctor_get(v_a_4127_, 0);
                    lean_inc(v_val_4131_);
                    lean_dec_ref_known(v_a_4127_, 1);
                    if v_isShared_4130_ == 0 {
                        lean_ctor_set(v___x_4129_, 0, v_val_4131_);
                        v___x_4133_ = v___x_4129_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_val_4131_);
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
                    v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
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
    mut v_constName_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
    mut v___y_4146_: *mut LeanObject,
    mut v___y_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4150_: *mut LeanObject = core::ptr::null_mut();
    v_res_4150_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0(v_constName_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
    lean_dec(v___y_4148_);
    lean_dec_ref(v___y_4147_);
    lean_dec(v___y_4146_);
    lean_dec_ref(v___y_4145_);
    return v_res_4150_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2()
-> *mut LeanObject {
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    v___x_4153_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__1;
    v___x_4154_ = l_Lean_stringToMessageData(v___x_4153_);
    return v___x_4154_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4()
-> *mut LeanObject {
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    v___x_4156_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__3;
    v___x_4157_ = l_Lean_stringToMessageData(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6()
-> *mut LeanObject {
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    v___x_4159_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__5;
    v___x_4160_ = l_Lean_stringToMessageData(v___x_4159_);
    return v___x_4160_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8()
-> *mut LeanObject {
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    v___x_4162_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__7;
    v___x_4163_ = l_Lean_stringToMessageData(v___x_4162_);
    return v___x_4163_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(
    mut v_instName_4164_: *mut LeanObject,
    mut v_a_4165_: *mut LeanObject,
    mut v_a_4166_: *mut LeanObject,
    mut v_a_4167_: *mut LeanObject,
    mut v_a_4168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: u8 = 0;
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4200_: u8 = 0;
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: u8 = 0;
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4220_: u8 = 0;
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4224_: u8 = 0;
    let mut v_a_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4228_: u8 = 0;
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4232_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_instName_4164_);
                v___x_4170_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0(v_instName_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
                if lean_obj_tag(v___x_4170_) == 0 {
                    v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
                    lean_inc(v_a_4171_);
                    lean_dec_ref_known(v___x_4170_, 1);
                    v_toConstantVal_4172_ = lean_ctor_get(v_a_4171_, 0);
                    lean_inc_ref(v_toConstantVal_4172_);
                    v_value_4173_ = lean_ctor_get(v_a_4171_, 1);
                    lean_inc_ref(v_value_4173_);
                    lean_dec(v_a_4171_);
                    v_name_4174_ = lean_ctor_get(v_toConstantVal_4172_, 0);
                    lean_inc(v_name_4174_);
                    v_levelParams_4175_ = lean_ctor_get(v_toConstantVal_4172_, 1);
                    lean_inc(v_levelParams_4175_);
                    v_type_4176_ = lean_ctor_get(v_toConstantVal_4172_, 2);
                    lean_inc_ref_n(v_type_4176_, 2);
                    lean_dec_ref(v_toConstantVal_4172_);
                    v___x_4177_ = l_Lean_Meta_isClass_x3f(
                        v_type_4176_,
                        v_a_4165_,
                        v_a_4166_,
                        v_a_4167_,
                        v_a_4168_,
                    );
                    if lean_obj_tag(v___x_4177_) == 0 {
                        v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
                        lean_inc(v_a_4178_);
                        lean_dec_ref_known(v___x_4177_, 1);
                        if lean_obj_tag(v_a_4178_) == 1 {
                            v_val_4179_ = lean_ctor_get(v_a_4178_, 0);
                            lean_inc(v_val_4179_);
                            lean_dec_ref_known(v_a_4178_, 1);
                            v___f_4180_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__0;
                            v___x_4181_ = 0;
                            lean_inc_ref(v_type_4176_);
                            v___x_4182_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(v_type_4176_, v___f_4180_, v___x_4181_, v___x_4181_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
                            if lean_obj_tag(v___x_4182_) == 0 {
                                v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
                                lean_inc(v_a_4183_);
                                lean_dec_ref_known(v___x_4182_, 1);
                                v___x_4184_ = lean_st_ref_get(v_a_4168_);
                                v_env_4185_ = lean_ctor_get(v___x_4184_, 0);
                                lean_inc_ref(v_env_4185_);
                                lean_dec(v___x_4184_);
                                lean_inc(v_val_4179_);
                                v___x_4186_ = l_Lean_getStructureInfo_x3f(v_env_4185_, v_val_4179_);
                                if lean_obj_tag(v___x_4186_) == 1 {
                                    v_val_4187_ = lean_ctor_get(v___x_4186_, 0);
                                    lean_inc(v_val_4187_);
                                    lean_dec_ref_known(v___x_4186_, 1);
                                    v___x_4188_ = lean_box((v___x_4181_) as usize);
                                    v___f_4189_ = lean_alloc_closure(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___boxed as *mut core::ffi::c_void, 15, 8);
                                    lean_closure_set(v___f_4189_, 0, v_type_4176_);
                                    lean_closure_set(v___f_4189_, 1, v_val_4179_);
                                    lean_closure_set(v___f_4189_, 2, v_levelParams_4175_);
                                    lean_closure_set(v___f_4189_, 3, v_name_4174_);
                                    lean_closure_set(v___f_4189_, 4, v_val_4187_);
                                    lean_closure_set(v___f_4189_, 5, v___x_4188_);
                                    lean_closure_set(v___f_4189_, 6, v_instName_4164_);
                                    lean_closure_set(v___f_4189_, 7, v_a_4183_);
                                    v___x_4190_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(v_value_4173_, v___f_4189_, v___x_4181_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
                                    return v___x_4190_;
                                } else {
                                    lean_dec(v___x_4186_);
                                    lean_dec(v_a_4183_);
                                    lean_dec_ref(v_type_4176_);
                                    lean_dec(v_levelParams_4175_);
                                    lean_dec(v_name_4174_);
                                    lean_dec_ref(v_value_4173_);
                                    lean_dec(v_instName_4164_);
                                    v___x_4191_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once), _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1);
                                    v___x_4192_ =
                                        l_Lean_MessageData_ofConstName(v_val_4179_, v___x_4181_);
                                    v___x_4193_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4193_, 0, v___x_4191_);
                                    lean_ctor_set(v___x_4193_, 1, v___x_4192_);
                                    v___x_4194_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2);
                                    v___x_4195_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4195_, 0, v___x_4193_);
                                    lean_ctor_set(v___x_4195_, 1, v___x_4194_);
                                    v___x_4196_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_4195_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
                                    return v___x_4196_;
                                }
                            } else {
                                lean_dec(v_val_4179_);
                                lean_dec_ref(v_type_4176_);
                                lean_dec(v_levelParams_4175_);
                                lean_dec(v_name_4174_);
                                lean_dec_ref(v_value_4173_);
                                lean_dec(v_instName_4164_);
                                v_a_4197_ = lean_ctor_get(v___x_4182_, 0);
                                v_isSharedCheck_4204_ = (!lean_is_exclusive(v___x_4182_)) as u8;
                                if v_isSharedCheck_4204_ == 0 {
                                    v___x_4199_ = v___x_4182_;
                                    v_isShared_4200_ = v_isSharedCheck_4204_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_4197_);
                                    lean_dec(v___x_4182_);
                                    v___x_4199_ = lean_box(0);
                                    v_isShared_4200_ = v_isSharedCheck_4204_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_4178_);
                            lean_dec(v_levelParams_4175_);
                            lean_dec(v_name_4174_);
                            lean_dec_ref(v_value_4173_);
                            v___x_4205_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4);
                            v___x_4206_ = 0;
                            v___x_4207_ =
                                l_Lean_MessageData_ofConstName(v_instName_4164_, v___x_4206_);
                            v___x_4208_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4208_, 0, v___x_4205_);
                            lean_ctor_set(v___x_4208_, 1, v___x_4207_);
                            v___x_4209_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6);
                            v___x_4210_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4210_, 0, v___x_4208_);
                            lean_ctor_set(v___x_4210_, 1, v___x_4209_);
                            v___x_4211_ = lean_unsigned_to_nat(30);
                            v___x_4212_ = l_Lean_inlineExpr(v_type_4176_, v___x_4211_);
                            v___x_4213_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4213_, 0, v___x_4210_);
                            lean_ctor_set(v___x_4213_, 1, v___x_4212_);
                            v___x_4214_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8);
                            v___x_4215_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4215_, 0, v___x_4213_);
                            lean_ctor_set(v___x_4215_, 1, v___x_4214_);
                            v___x_4216_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_4215_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
                            return v___x_4216_;
                        }
                    } else {
                        lean_dec_ref(v_type_4176_);
                        lean_dec(v_levelParams_4175_);
                        lean_dec(v_name_4174_);
                        lean_dec_ref(v_value_4173_);
                        lean_dec(v_instName_4164_);
                        v_a_4217_ = lean_ctor_get(v___x_4177_, 0);
                        v_isSharedCheck_4224_ = (!lean_is_exclusive(v___x_4177_)) as u8;
                        if v_isSharedCheck_4224_ == 0 {
                            v___x_4219_ = v___x_4177_;
                            v_isShared_4220_ = v_isSharedCheck_4224_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4217_);
                            lean_dec(v___x_4177_);
                            v___x_4219_ = lean_box(0);
                            v_isShared_4220_ = v_isSharedCheck_4224_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_instName_4164_);
                    v_a_4225_ = lean_ctor_get(v___x_4170_, 0);
                    v_isSharedCheck_4232_ = (!lean_is_exclusive(v___x_4170_)) as u8;
                    if v_isSharedCheck_4232_ == 0 {
                        v___x_4227_ = v___x_4170_;
                        v_isShared_4228_ = v_isSharedCheck_4232_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4225_);
                        lean_dec(v___x_4170_);
                        v___x_4227_ = lean_box(0);
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
                    v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
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
                    v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
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
                    v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
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
    mut v_instName_4233_: *mut LeanObject,
    mut v_a_4234_: *mut LeanObject,
    mut v_a_4235_: *mut LeanObject,
    mut v_a_4236_: *mut LeanObject,
    mut v_a_4237_: *mut LeanObject,
    mut v_a_4238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4239_: *mut LeanObject = core::ptr::null_mut();
    v_res_4239_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(
        v_instName_4233_,
        v_a_4234_,
        v_a_4235_,
        v_a_4236_,
        v_a_4237_,
    );
    lean_dec(v_a_4237_);
    lean_dec_ref(v_a_4236_);
    lean_dec(v_a_4235_);
    lean_dec_ref(v_a_4234_);
    return v_res_4239_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3(
    mut v_00_u03b1_4240_: *mut LeanObject,
    mut v_msg_4241_: *mut LeanObject,
    mut v___y_4242_: *mut LeanObject,
    mut v___y_4243_: *mut LeanObject,
    mut v___y_4244_: *mut LeanObject,
    mut v___y_4245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    v___x_4247_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v_msg_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
    return v___x_4247_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___boxed(
    mut v_00_u03b1_4248_: *mut LeanObject,
    mut v_msg_4249_: *mut LeanObject,
    mut v___y_4250_: *mut LeanObject,
    mut v___y_4251_: *mut LeanObject,
    mut v___y_4252_: *mut LeanObject,
    mut v___y_4253_: *mut LeanObject,
    mut v___y_4254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4255_: *mut LeanObject = core::ptr::null_mut();
    v_res_4255_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3(v_00_u03b1_4248_, v_msg_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
    lean_dec(v___y_4253_);
    lean_dec_ref(v___y_4252_);
    lean_dec(v___y_4251_);
    lean_dec_ref(v___y_4250_);
    return v_res_4255_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4(
    mut v_xs_4256_: *mut LeanObject,
    mut v_ys_4257_: *mut LeanObject,
    mut v_hsz_4258_: *mut LeanObject,
    mut v_x_4259_: *mut LeanObject,
    mut v_x_4260_: *mut LeanObject,
) -> u8 {
    let mut v___x_4261_: u8 = 0;
    v___x_4261_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(v_xs_4256_, v_ys_4257_, v_x_4259_);
    return v___x_4261_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___boxed(
    mut v_xs_4262_: *mut LeanObject,
    mut v_ys_4263_: *mut LeanObject,
    mut v_hsz_4264_: *mut LeanObject,
    mut v_x_4265_: *mut LeanObject,
    mut v_x_4266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4267_: u8 = 0;
    let mut v_r_4268_: *mut LeanObject = core::ptr::null_mut();
    v_res_4267_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4(v_xs_4262_, v_ys_4263_, v_hsz_4264_, v_x_4265_, v_x_4266_);
    lean_dec_ref(v_ys_4263_);
    lean_dec_ref(v_xs_4262_);
    v_r_4268_ = lean_box((v_res_4267_) as usize);
    return v_r_4268_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1() -> u64
{
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: u64 = 0;
    v___x_4280_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0;
    v___x_4281_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4280_);
    return v___x_4281_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4282_: u64 = 0;
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    v___x_4282_ = lean_uint64_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1,
    );
    v___x_4283_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0;
    v___x_4284_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_4284_, 0, v___x_4283_);
    lean_ctor_set_uint64(
        v___x_4284_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4282_,
    );
    return v___x_4284_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    v___x_4285_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4285_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    v___x_4286_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3,
    );
    v___x_4287_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4287_, 0, v___x_4286_);
    return v___x_4287_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    v___x_4288_ = lean_unsigned_to_nat(32);
    v___x_4289_ = lean_mk_empty_array_with_capacity(v___x_4288_);
    v___x_4290_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4290_, 0, v___x_4289_);
    return v___x_4290_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_4291_: usize = 0;
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    v___x_4291_ = 5usize;
    v___x_4292_ = lean_unsigned_to_nat(0);
    v___x_4293_ = lean_unsigned_to_nat(32);
    v___x_4294_ = lean_mk_empty_array_with_capacity(v___x_4293_);
    v___x_4295_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5,
    );
    v___x_4296_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4296_, 0, v___x_4295_);
    lean_ctor_set(v___x_4296_, 1, v___x_4294_);
    lean_ctor_set(v___x_4296_, 2, v___x_4292_);
    lean_ctor_set(v___x_4296_, 3, v___x_4292_);
    lean_ctor_set_usize(v___x_4296_, 4, v___x_4291_);
    return v___x_4296_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    v___x_4297_ = lean_box(1);
    v___x_4298_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6,
    );
    v___x_4299_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4,
    );
    v___x_4300_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4300_, 0, v___x_4299_);
    lean_ctor_set(v___x_4300_, 1, v___x_4298_);
    lean_ctor_set(v___x_4300_, 2, v___x_4297_);
    return v___x_4300_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_4303_: u8 = 0;
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: u8 = 0;
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    v___x_4303_ = 1;
    v___x_4304_ = lean_unsigned_to_nat(0);
    v___x_4305_ = lean_box(0);
    v___x_4306_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8;
    v___x_4307_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7,
    );
    v___x_4308_ = lean_box(1);
    v___x_4309_ = 0;
    v___x_4310_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2,
    );
    v___x_4311_ = lean_alloc_ctor(0, 7, (4) as u32);
    lean_ctor_set(v___x_4311_, 0, v___x_4310_);
    lean_ctor_set(v___x_4311_, 1, v___x_4308_);
    lean_ctor_set(v___x_4311_, 2, v___x_4307_);
    lean_ctor_set(v___x_4311_, 3, v___x_4306_);
    lean_ctor_set(v___x_4311_, 4, v___x_4305_);
    lean_ctor_set(v___x_4311_, 5, v___x_4304_);
    lean_ctor_set(v___x_4311_, 6, v___x_4305_);
    lean_ctor_set_uint8(
        v___x_4311_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
        v___x_4309_,
    );
    lean_ctor_set_uint8(
        v___x_4311_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
        v___x_4309_,
    );
    lean_ctor_set_uint8(
        v___x_4311_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
        v___x_4309_,
    );
    lean_ctor_set_uint8(
        v___x_4311_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
        v___x_4303_,
    );
    return v___x_4311_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10()
-> *mut LeanObject {
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    v___x_4312_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4,
    );
    v___x_4313_ = lean_unsigned_to_nat(0);
    v___x_4314_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_4314_, 0, v___x_4313_);
    lean_ctor_set(v___x_4314_, 1, v___x_4313_);
    lean_ctor_set(v___x_4314_, 2, v___x_4313_);
    lean_ctor_set(v___x_4314_, 3, v___x_4313_);
    lean_ctor_set(v___x_4314_, 4, v___x_4312_);
    lean_ctor_set(v___x_4314_, 5, v___x_4312_);
    lean_ctor_set(v___x_4314_, 6, v___x_4312_);
    lean_ctor_set(v___x_4314_, 7, v___x_4312_);
    lean_ctor_set(v___x_4314_, 8, v___x_4312_);
    lean_ctor_set(v___x_4314_, 9, v___x_4312_);
    return v___x_4314_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    v___x_4315_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4,
    );
    v___x_4316_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_4316_, 0, v___x_4315_);
    lean_ctor_set(v___x_4316_, 1, v___x_4315_);
    lean_ctor_set(v___x_4316_, 2, v___x_4315_);
    lean_ctor_set(v___x_4316_, 3, v___x_4315_);
    lean_ctor_set(v___x_4316_, 4, v___x_4315_);
    lean_ctor_set(v___x_4316_, 5, v___x_4315_);
    return v___x_4316_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12()
-> *mut LeanObject {
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    v___x_4317_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4,
    );
    v___x_4318_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_4318_, 0, v___x_4317_);
    lean_ctor_set(v___x_4318_, 1, v___x_4317_);
    lean_ctor_set(v___x_4318_, 2, v___x_4317_);
    lean_ctor_set(v___x_4318_, 3, v___x_4317_);
    lean_ctor_set(v___x_4318_, 4, v___x_4317_);
    return v___x_4318_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    v___x_4319_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12,
    );
    v___x_4320_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6,
    );
    v___x_4321_ = lean_box(1);
    v___x_4322_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11,
    );
    v___x_4323_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10,
    );
    v___x_4324_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_4324_, 0, v___x_4323_);
    lean_ctor_set(v___x_4324_, 1, v___x_4322_);
    lean_ctor_set(v___x_4324_, 2, v___x_4321_);
    lean_ctor_set(v___x_4324_, 3, v___x_4320_);
    lean_ctor_set(v___x_4324_, 4, v___x_4319_);
    return v___x_4324_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(
    mut v_instName_4325_: *mut LeanObject,
    mut v_a_4326_: *mut LeanObject,
    mut v_a_4327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_clsName_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_privateSpecs_4332_: u8 = 0;
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4345_: u8 = 0;
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4349_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4335_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9);
                v___x_4336_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13);
                v___x_4337_ = lean_st_mk_ref(v___x_4336_);
                v___x_4338_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(
                    v_instName_4325_,
                    v___x_4335_,
                    v___x_4337_,
                    v_a_4326_,
                    v_a_4327_,
                );
                if lean_obj_tag(v___x_4338_) == 0 {
                    v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
                    lean_inc(v_a_4339_);
                    lean_dec_ref_known(v___x_4338_, 1);
                    v___x_4340_ = lean_st_ref_get(v___x_4337_);
                    lean_dec(v___x_4337_);
                    lean_dec(v___x_4340_);
                    v_a_4330_ = v_a_4339_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_4337_);
                    if lean_obj_tag(v___x_4338_) == 0 {
                        v_a_4341_ = lean_ctor_get(v___x_4338_, 0);
                        lean_inc(v_a_4341_);
                        lean_dec_ref_known(v___x_4338_, 1);
                        v_a_4330_ = v_a_4341_;
                        state = 1;
                        continue;
                    } else {
                        v_a_4342_ = lean_ctor_get(v___x_4338_, 0);
                        v_isSharedCheck_4349_ = (!lean_is_exclusive(v___x_4338_)) as u8;
                        if v_isSharedCheck_4349_ == 0 {
                            v___x_4344_ = v___x_4338_;
                            v_isShared_4345_ = v_isSharedCheck_4349_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4342_);
                            lean_dec(v___x_4338_);
                            v___x_4344_ = lean_box(0);
                            v_isShared_4345_ = v_isSharedCheck_4349_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_clsName_4331_ = lean_ctor_get(v_a_4330_, 0);
                lean_inc(v_clsName_4331_);
                v_privateSpecs_4332_ = lean_ctor_get_uint8(
                    v_a_4330_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_a_4330_);
                v___x_4333_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4333_, 0, v_clsName_4331_);
                lean_ctor_set_uint8(
                    v___x_4333_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_privateSpecs_4332_,
                );
                v___x_4334_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4334_, 0, v___x_4333_);
                return v___x_4334_;
            }
            2 => {
                if v_isShared_4345_ == 0 {
                    v___x_4347_ = v___x_4344_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
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
    mut v_instName_4350_: *mut LeanObject,
    mut v_a_4351_: *mut LeanObject,
    mut v_a_4352_: *mut LeanObject,
    mut v_a_4353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4354_: *mut LeanObject = core::ptr::null_mut();
    v_res_4354_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(
        v_instName_4350_,
        v_a_4351_,
        v_a_4352_,
    );
    lean_dec(v_a_4352_);
    lean_dec_ref(v_a_4351_);
    return v_res_4354_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getParam(
    mut v_instName_4355_: *mut LeanObject,
    mut v___stx_4356_: *mut LeanObject,
    mut v_a_4357_: *mut LeanObject,
    mut v_a_4358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    v___x_4360_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(
        v_instName_4355_,
        v_a_4357_,
        v_a_4358_,
    );
    return v___x_4360_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___boxed(
    mut v_instName_4361_: *mut LeanObject,
    mut v___stx_4362_: *mut LeanObject,
    mut v_a_4363_: *mut LeanObject,
    mut v_a_4364_: *mut LeanObject,
    mut v_a_4365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4366_: *mut LeanObject = core::ptr::null_mut();
    v_res_4366_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam(
        v_instName_4361_,
        v___stx_4362_,
        v_a_4363_,
        v_a_4364_,
    );
    lean_dec(v_a_4364_);
    lean_dec_ref(v_a_4363_);
    lean_dec(v___stx_4362_);
    return v_res_4366_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(
    mut v_x_4367_: *mut LeanObject,
    mut v_x_4368_: *mut LeanObject,
    mut v_x_4369_: *mut LeanObject,
    mut v___y_4370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    v___x_4372_ = lean_box(0);
    v___x_4373_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4373_, 0, v___x_4372_);
    return v___x_4373_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(
    mut v_x_4374_: *mut LeanObject,
    mut v_x_4375_: *mut LeanObject,
    mut v_x_4376_: *mut LeanObject,
    mut v___y_4377_: *mut LeanObject,
    mut v___y_4378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4379_: *mut LeanObject = core::ptr::null_mut();
    v_res_4379_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(v_x_4374_, v_x_4375_, v_x_4376_, v___y_4377_);
    lean_dec(v___y_4377_);
    lean_dec_ref(v_x_4376_);
    lean_dec_ref(v_x_4375_);
    lean_dec(v_x_4374_);
    return v_res_4379_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(
    mut v___x_4380_: u8,
    mut v_env_4381_: *mut LeanObject,
    mut v_n_4382_: *mut LeanObject,
    mut v_x_4383_: *mut LeanObject,
) -> u8 {
    let mut v___x_4384_: u8 = 0;
    v___x_4384_ = l_Lean_Environment_contains(v_env_4381_, v_n_4382_, v___x_4380_);
    return v___x_4384_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(
    mut v___x_4385_: *mut LeanObject,
    mut v_env_4386_: *mut LeanObject,
    mut v_n_4387_: *mut LeanObject,
    mut v_x_4388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_120__boxed_4389_: u8 = 0;
    let mut v_res_4390_: u8 = 0;
    let mut v_r_4391_: *mut LeanObject = core::ptr::null_mut();
    v___x_120__boxed_4389_ = (lean_unbox(v___x_4385_) as u8);
    v_res_4390_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(v___x_120__boxed_4389_, v_env_4386_, v_n_4387_, v_x_4388_);
    lean_dec_ref(v_x_4388_);
    v_r_4391_ = lean_box((v_res_4390_) as usize);
    return v_r_4391_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    v___x_4437_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__17_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_;
    v___x_4438_ = l_Lean_registerParametricAttribute___redArg(v___x_4437_);
    return v___x_4438_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(
    mut v_a_4439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4440_: *mut LeanObject = core::ptr::null_mut();
    v_res_4440_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_();
    return v_res_4440_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1()
-> *mut LeanObject {
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    v___x_4443_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_;
    v___x_4444_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__0;
    v___x_4445_ = l_Lean_addBuiltinDocString(v___x_4443_, v___x_4444_);
    return v___x_4445_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___boxed(
    mut v_a_4446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4447_: *mut LeanObject = core::ptr::null_mut();
    v_res_4447_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1();
    return v_res_4447_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3()
-> *mut LeanObject {
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    v___x_4474_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_;
    v___x_4475_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___closed__6;
    v___x_4476_ = l_Lean_addBuiltinDeclarationRanges(v___x_4474_, v___x_4475_);
    return v___x_4476_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3___boxed(
    mut v_a_4477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4478_: *mut LeanObject = core::ptr::null_mut();
    v_res_4478_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3();
    return v_res_4478_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    v___x_4488_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_;
    v___x_4489_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_;
    v___x_4490_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_;
    v___x_4491_ = l_Lean_Meta_registerSimpAttr(v___x_4488_, v___x_4489_, v___x_4490_);
    return v___x_4491_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2____boxed(
    mut v_a_4492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4493_: *mut LeanObject = core::ptr::null_mut();
    v_res_4493_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_();
    return v_res_4493_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
    mut v_env_4494_: *mut LeanObject,
    mut v_instName_4495_: *mut LeanObject,
    mut v_privateSpecs_4496_: u8,
    mut v_suffix_4497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_thmName_4498_: *mut LeanObject = core::ptr::null_mut();
    v_thmName_4498_ = l_Lean_Name_str___override(v_instName_4495_, v_suffix_4497_);
    if v_privateSpecs_4496_ == 0 {
        return v_thmName_4498_;
    } else {
        let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
        v___x_4499_ = l_Lean_mkPrivateName(v_env_4494_, v_thmName_4498_);
        return v___x_4499_;
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName___boxed(
    mut v_env_4500_: *mut LeanObject,
    mut v_instName_4501_: *mut LeanObject,
    mut v_privateSpecs_4502_: *mut LeanObject,
    mut v_suffix_4503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_privateSpecs_boxed_4504_: u8 = 0;
    let mut v_res_4505_: *mut LeanObject = core::ptr::null_mut();
    v_privateSpecs_boxed_4504_ = (lean_unbox(v_privateSpecs_4502_) as u8);
    v_res_4505_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
        v_env_4500_,
        v_instName_4501_,
        v_privateSpecs_boxed_4504_,
        v_suffix_4503_,
    );
    lean_dec_ref(v_env_4500_);
    return v_res_4505_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0___redArg(
    mut v_p_4506_: *mut LeanObject,
    mut v_s_4507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: u8 = 0;
    v___x_4508_ = lean_string_utf8_byte_size(v_s_4507_);
    v___x_4509_ = lean_string_utf8_byte_size(v_p_4506_);
    v___x_4510_ = lean_nat_dec_le(v___x_4509_, v___x_4508_);
    if v___x_4510_ == 0 {
        let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_4507_);
        v___x_4511_ = lean_box(0);
        return v___x_4511_;
    } else {
        let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4513_: u8 = 0;
        v___x_4512_ = lean_unsigned_to_nat(0);
        v___x_4513_ =
            lean_string_memcmp(v_s_4507_, v_p_4506_, v___x_4512_, v___x_4512_, v___x_4509_);
        if v___x_4513_ == 0 {
            let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_s_4507_);
            v___x_4514_ = lean_box(0);
            return v___x_4514_;
        } else {
            let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_s_4507_);
            v___x_4515_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4515_, 0, v_s_4507_);
            lean_ctor_set(v___x_4515_, 1, v___x_4512_);
            lean_ctor_set(v___x_4515_, 2, v___x_4508_);
            v___x_4516_ = l_String_Slice_pos_x21(v___x_4515_, v___x_4509_);
            lean_dec_ref_known(v___x_4515_, 3);
            v___x_4517_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4517_, 0, v_s_4507_);
            lean_ctor_set(v___x_4517_, 1, v___x_4516_);
            lean_ctor_set(v___x_4517_, 2, v___x_4508_);
            v___x_4518_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_4518_, 0, v___x_4517_);
            return v___x_4518_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0___redArg___boxed(
    mut v_p_4519_: *mut LeanObject,
    mut v_s_4520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4521_: *mut LeanObject = core::ptr::null_mut();
    v_res_4521_ = l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0___redArg(v_p_4519_, v_s_4520_);
    lean_dec_ref(v_p_4519_);
    return v_res_4521_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0(
    mut v_p_4522_: *mut LeanObject,
    mut v_s_4523_: *mut LeanObject,
    mut v_pat_4524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    v___x_4525_ = l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0___redArg(v_p_4522_, v_s_4523_);
    return v___x_4525_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0___boxed(
    mut v_p_4526_: *mut LeanObject,
    mut v_s_4527_: *mut LeanObject,
    mut v_pat_4528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4529_: *mut LeanObject = core::ptr::null_mut();
    v_res_4529_ = l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0(v_p_4526_, v_s_4527_, v_pat_4528_);
    lean_dec_ref(v_pat_4528_);
    lean_dec_ref(v_p_4526_);
    return v_res_4529_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(
    mut v_s_4530_: *mut LeanObject,
    mut v_p_4531_: *mut LeanObject,
) -> u8 {
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    v___x_4532_ = l_String_dropPrefix_x3f___at___00__private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber_spec__0___redArg(v_p_4531_, v_s_4530_);
    if lean_obj_tag(v___x_4532_) == 0 {
        let mut v___x_4533_: u8 = 0;
        v___x_4533_ = 0;
        return v___x_4533_;
    } else {
        let mut v_val_4534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4535_: u8 = 0;
        v_val_4534_ = lean_ctor_get(v___x_4532_, 0);
        lean_inc(v_val_4534_);
        lean_dec_ref_known(v___x_4532_, 1);
        v___x_4535_ = l_String_Slice_isNat(v_val_4534_);
        lean_dec(v_val_4534_);
        return v___x_4535_;
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber___boxed(
    mut v_s_4536_: *mut LeanObject,
    mut v_p_4537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4538_: u8 = 0;
    let mut v_r_4539_: *mut LeanObject = core::ptr::null_mut();
    v_res_4538_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(v_s_4536_, v_p_4537_);
    lean_dec_ref(v_p_4537_);
    v_r_4539_ = lean_box((v_res_4538_) as usize);
    return v_r_4539_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(
    mut v_fieldName_4542_: *mut LeanObject,
    mut v_s_4543_: *mut LeanObject,
) -> u8 {
    let mut v___x_4544_: u8 = 0;
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: u8 = 0;
    v___x_4544_ = 1;
    v___x_4545_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_fieldName_4542_,
        v___x_4544_,
    );
    v___x_4546_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0;
    lean_inc_ref(v___x_4545_);
    v___x_4547_ = lean_string_append(v___x_4545_, v___x_4546_);
    v___x_4548_ = lean_string_dec_eq(v_s_4543_, v___x_4547_);
    lean_dec_ref(v___x_4547_);
    if v___x_4548_ == 0 {
        let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4551_: u8 = 0;
        v___x_4549_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1;
        v___x_4550_ = lean_string_append(v___x_4545_, v___x_4549_);
        v___x_4551_ = l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(
            v_s_4543_,
            v___x_4550_,
        );
        lean_dec_ref(v___x_4550_);
        return v___x_4551_;
    } else {
        lean_dec_ref(v___x_4545_);
        lean_dec_ref(v_s_4543_);
        return v___x_4548_;
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___boxed(
    mut v_fieldName_4552_: *mut LeanObject,
    mut v_s_4553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4554_: u8 = 0;
    let mut v_r_4555_: *mut LeanObject = core::ptr::null_mut();
    v_res_4554_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(v_fieldName_4552_, v_s_4553_);
    v_r_4555_ = lean_box((v_res_4554_) as usize);
    return v_r_4555_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(
    mut v_str_4559_: *mut LeanObject,
    mut v_val_4560_: *mut LeanObject,
    mut v_env_4561_: *mut LeanObject,
    mut v_p_4562_: *mut LeanObject,
    mut v_name_4563_: *mut LeanObject,
    mut v_as_4564_: *mut LeanObject,
    mut v_sz_4565_: usize,
    mut v_i_4566_: usize,
    mut v_b_4567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: usize = 0;
    let mut v___x_4571_: usize = 0;
    let mut v___x_4573_: u8 = 0;
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: u8 = 0;
    let mut v_privateSpecs_4579_: u8 = 0;
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: u8 = 0;
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4573_ = lean_usize_dec_lt(v_i_4566_, v_sz_4565_);
                if v___x_4573_ == 0 {
                    lean_dec(v_p_4562_);
                    lean_dec_ref(v_str_4559_);
                    v___x_4574_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4574_, 0, v_b_4567_);
                    return v___x_4574_;
                } else {
                    lean_dec_ref(v_b_4567_);
                    v___x_4575_ = lean_box(0);
                    v___x_4576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0;
                    v_a_4577_ = lean_array_uget_borrowed(v_as_4564_, v_i_4566_);
                    lean_inc_ref(v_str_4559_);
                    lean_inc(v_a_4577_);
                    v___x_4578_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(
                        v_a_4577_,
                        v_str_4559_,
                    );
                    if v___x_4578_ == 0 {
                        v_a_4569_ = v___x_4576_;
                        state = 1;
                        continue;
                    } else {
                        v_privateSpecs_4579_ = lean_ctor_get_uint8(
                            v_val_4560_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        lean_inc_ref(v_str_4559_);
                        lean_inc(v_p_4562_);
                        v___x_4580_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                            v_env_4561_,
                            v_p_4562_,
                            v_privateSpecs_4579_,
                            v_str_4559_,
                        );
                        v___x_4581_ = lean_name_eq(v_name_4563_, v___x_4580_);
                        lean_dec(v___x_4580_);
                        if v___x_4581_ == 0 {
                            v_a_4569_ = v___x_4576_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_str_4559_);
                            v___x_4582_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_4582_, 0, v_p_4562_);
                            v___x_4583_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_4583_, 0, v___x_4582_);
                            lean_ctor_set(v___x_4583_, 1, v___x_4575_);
                            v___x_4584_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_4584_, 0, v___x_4583_);
                            return v___x_4584_;
                        }
                    }
                }
            }
            1 => {
                v___x_4570_ = 1usize;
                v___x_4571_ = lean_usize_add(v_i_4566_, v___x_4570_);
                lean_inc_ref(v_a_4569_);
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
    mut v_str_4585_: *mut LeanObject,
    mut v_val_4586_: *mut LeanObject,
    mut v_env_4587_: *mut LeanObject,
    mut v_p_4588_: *mut LeanObject,
    mut v_name_4589_: *mut LeanObject,
    mut v_as_4590_: *mut LeanObject,
    mut v_sz_4591_: *mut LeanObject,
    mut v_i_4592_: *mut LeanObject,
    mut v_b_4593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4594_: usize = 0;
    let mut v_i_boxed_4595_: usize = 0;
    let mut v_res_4596_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4594_ = lean_unbox_usize(v_sz_4591_);
    lean_dec(v_sz_4591_);
    v_i_boxed_4595_ = lean_unbox_usize(v_i_4592_);
    lean_dec(v_i_4592_);
    v_res_4596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(v_str_4585_, v_val_4586_, v_env_4587_, v_p_4588_, v_name_4589_, v_as_4590_, v_sz_boxed_4594_, v_i_boxed_4595_, v_b_4593_);
    lean_dec_ref(v_as_4590_);
    lean_dec(v_name_4589_);
    lean_dec_ref(v_env_4587_);
    lean_dec_ref(v_val_4586_);
    return v_res_4596_;
}
pub unsafe fn l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(
    mut v_env_4597_: *mut LeanObject,
    mut v_str_4598_: *mut LeanObject,
    mut v_name_4599_: *mut LeanObject,
    mut v_x_4600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_clsName_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4612_: usize = 0;
    let mut v___x_4613_: usize = 0;
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4600_) == 0 {
                    lean_dec_ref(v_str_4598_);
                    lean_dec_ref(v_env_4597_);
                    v___x_4601_ = lean_box(0);
                    return v___x_4601_;
                } else {
                    v_head_4602_ = lean_ctor_get(v_x_4600_, 0);
                    lean_inc_n(v_head_4602_, 2);
                    v_tail_4603_ = lean_ctor_get(v_x_4600_, 1);
                    lean_inc(v_tail_4603_);
                    lean_dec_ref_known(v_x_4600_, 2);
                    v___x_4604_ = l_Lean_instInhabitedMethodSpecsAttrData_default;
                    v___x_4605_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
                    lean_inc_ref(v_env_4597_);
                    v___x_4606_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
                        v___x_4604_,
                        v___x_4605_,
                        v_env_4597_,
                        v_head_4602_,
                    );
                    if lean_obj_tag(v___x_4606_) == 0 {
                        lean_dec(v_head_4602_);
                        v_x_4600_ = v_tail_4603_;
                        state = 0;
                        continue;
                    } else {
                        v_val_4608_ = lean_ctor_get(v___x_4606_, 0);
                        lean_inc(v_val_4608_);
                        lean_dec_ref_known(v___x_4606_, 1);
                        v_clsName_4609_ = lean_ctor_get(v_val_4608_, 0);
                        lean_inc(v_clsName_4609_);
                        lean_inc_ref(v_env_4597_);
                        v___x_4610_ = l_Lean_getStructureFields(v_env_4597_, v_clsName_4609_);
                        v___x_4611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0;
                        v_sz_4612_ = lean_array_size(v___x_4610_);
                        v___x_4613_ = 0usize;
                        lean_inc_ref(v_str_4598_);
                        v___x_4614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(v_str_4598_, v_val_4608_, v_env_4597_, v_head_4602_, v_name_4599_, v___x_4610_, v_sz_4612_, v___x_4613_, v___x_4611_);
                        lean_dec_ref(v___x_4610_);
                        lean_dec(v_val_4608_);
                        if lean_obj_tag(v___x_4614_) == 0 {
                            v_x_4600_ = v_tail_4603_;
                            state = 0;
                            continue;
                        } else {
                            v_val_4616_ = lean_ctor_get(v___x_4614_, 0);
                            lean_inc(v_val_4616_);
                            lean_dec_ref_known(v___x_4614_, 1);
                            v_fst_4617_ = lean_ctor_get(v_val_4616_, 0);
                            lean_inc(v_fst_4617_);
                            lean_dec(v_val_4616_);
                            if lean_obj_tag(v_fst_4617_) == 0 {
                                v_x_4600_ = v_tail_4603_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_tail_4603_);
                                lean_dec_ref(v_str_4598_);
                                lean_dec_ref(v_env_4597_);
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
    mut v_env_4619_: *mut LeanObject,
    mut v_str_4620_: *mut LeanObject,
    mut v_name_4621_: *mut LeanObject,
    mut v_x_4622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4623_: *mut LeanObject = core::ptr::null_mut();
    v_res_4623_ =
        l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(
            v_env_4619_,
            v_str_4620_,
            v_name_4621_,
            v_x_4622_,
        );
    lean_dec(v_name_4621_);
    return v_res_4623_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(
    mut v_env_4624_: *mut LeanObject,
    mut v_name_4625_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_name_4625_) == 1 {
        let mut v_pre_4626_: *mut LeanObject = core::ptr::null_mut();
        let mut v_str_4627_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
        v_pre_4626_ = lean_ctor_get(v_name_4625_, 0);
        v_str_4627_ = lean_ctor_get(v_name_4625_, 1);
        lean_inc_ref(v_str_4627_);
        lean_inc_n(v_pre_4626_, 2);
        v___x_4628_ = l_Lean_privateToUserName(v_pre_4626_);
        v___x_4629_ = lean_box(0);
        v___x_4630_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4630_, 0, v___x_4628_);
        lean_ctor_set(v___x_4630_, 1, v___x_4629_);
        v___x_4631_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4631_, 0, v_pre_4626_);
        lean_ctor_set(v___x_4631_, 1, v___x_4630_);
        v___x_4632_ =
            l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(
                v_env_4624_,
                v_str_4627_,
                v_name_4625_,
                v___x_4631_,
            );
        lean_dec_ref_known(v_name_4625_, 2);
        return v___x_4632_;
    } else {
        let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_name_4625_);
        lean_dec_ref(v_env_4624_);
        v___x_4633_ = lean_box(0);
        return v___x_4633_;
    }
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    v___x_4634_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4634_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    v___x_4635_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_4636_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4636_, 0, v___x_4635_);
    return v___x_4636_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    v___x_4637_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_4638_ = lean_unsigned_to_nat(0);
    v___x_4639_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_4639_, 0, v___x_4638_);
    lean_ctor_set(v___x_4639_, 1, v___x_4638_);
    lean_ctor_set(v___x_4639_, 2, v___x_4638_);
    lean_ctor_set(v___x_4639_, 3, v___x_4638_);
    lean_ctor_set(v___x_4639_, 4, v___x_4637_);
    lean_ctor_set(v___x_4639_, 5, v___x_4637_);
    lean_ctor_set(v___x_4639_, 6, v___x_4637_);
    lean_ctor_set(v___x_4639_, 7, v___x_4637_);
    lean_ctor_set(v___x_4639_, 8, v___x_4637_);
    lean_ctor_set(v___x_4639_, 9, v___x_4637_);
    return v___x_4639_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    v___x_4640_ = lean_box(1);
    v___x_4641_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6,
    );
    v___x_4642_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_4643_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4643_, 0, v___x_4642_);
    lean_ctor_set(v___x_4643_, 1, v___x_4641_);
    lean_ctor_set(v___x_4643_, 2, v___x_4640_);
    return v___x_4643_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    v___x_4645_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
    v___x_4646_ = l_Lean_stringToMessageData(v___x_4645_);
    return v___x_4646_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    v___x_4648_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_4649_ = l_Lean_stringToMessageData(v___x_4648_);
    return v___x_4649_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    v___x_4651_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_4652_ = l_Lean_stringToMessageData(v___x_4651_);
    return v___x_4652_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    v___x_4654_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_4655_ = l_Lean_stringToMessageData(v___x_4654_);
    return v___x_4655_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    v___x_4657_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_4658_ = l_Lean_stringToMessageData(v___x_4657_);
    return v___x_4658_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    v___x_4660_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_4661_ = l_Lean_stringToMessageData(v___x_4660_);
    return v___x_4661_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    v___x_4663_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_4664_ = l_Lean_stringToMessageData(v___x_4663_);
    return v___x_4664_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_4665_: *mut LeanObject,
    mut v_declHint_4666_: *mut LeanObject,
    mut v___y_4667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: u8 = 0;
    let mut v_isExporting_4672_: u8 = 0;
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: u8 = 0;
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4694_: u8 = 0;
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: u8 = 0;
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4726_: u8 = 0;
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4669_ = lean_st_ref_get(v___y_4667_);
                v_env_4670_ = lean_ctor_get(v___x_4669_, 0);
                lean_inc_ref(v_env_4670_);
                lean_dec(v___x_4669_);
                v___x_4671_ = l_Lean_Name_isAnonymous(v_declHint_4666_);
                if v___x_4671_ == 0 {
                    v_isExporting_4672_ = lean_ctor_get_uint8(
                        v_env_4670_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4672_ == 0 {
                        lean_dec_ref(v_env_4670_);
                        lean_dec(v_declHint_4666_);
                        v___x_4673_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4673_, 0, v_msg_4665_);
                        return v___x_4673_;
                    } else {
                        lean_inc_ref(v_env_4670_);
                        v___x_4674_ = l_Lean_Environment_setExporting(v_env_4670_, v___x_4671_);
                        lean_inc(v_declHint_4666_);
                        lean_inc_ref(v___x_4674_);
                        v___x_4675_ = l_Lean_Environment_contains(
                            v___x_4674_,
                            v_declHint_4666_,
                            v_isExporting_4672_,
                        );
                        if v___x_4675_ == 0 {
                            lean_dec_ref(v___x_4674_);
                            lean_dec_ref(v_env_4670_);
                            lean_dec(v_declHint_4666_);
                            v___x_4676_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4676_, 0, v_msg_4665_);
                            return v___x_4676_;
                        } else {
                            v___x_4677_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_4678_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
                            v___x_4679_ = l_Lean_Options_empty;
                            v___x_4680_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_4680_, 0, v___x_4674_);
                            lean_ctor_set(v___x_4680_, 1, v___x_4677_);
                            lean_ctor_set(v___x_4680_, 2, v___x_4678_);
                            lean_ctor_set(v___x_4680_, 3, v___x_4679_);
                            lean_inc(v_declHint_4666_);
                            v___x_4681_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4666_, v___x_4671_);
                            v_c_4682_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_4682_, 0, v___x_4680_);
                            lean_ctor_set(v_c_4682_, 1, v___x_4681_);
                            v___x_4683_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4670_,
                                v_declHint_4666_,
                            );
                            if lean_obj_tag(v___x_4683_) == 0 {
                                lean_dec_ref(v_env_4670_);
                                lean_dec(v_declHint_4666_);
                                v___x_4684_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                                v___x_4685_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4685_, 0, v___x_4684_);
                                lean_ctor_set(v___x_4685_, 1, v_c_4682_);
                                v___x_4686_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_4687_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4687_, 0, v___x_4685_);
                                lean_ctor_set(v___x_4687_, 1, v___x_4686_);
                                v___x_4688_ = l_Lean_MessageData_note(v___x_4687_);
                                v___x_4689_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4689_, 0, v_msg_4665_);
                                lean_ctor_set(v___x_4689_, 1, v___x_4688_);
                                v___x_4690_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_4690_, 0, v___x_4689_);
                                return v___x_4690_;
                            } else {
                                v_val_4691_ = lean_ctor_get(v___x_4683_, 0);
                                v_isSharedCheck_4726_ = (!lean_is_exclusive(v___x_4683_)) as u8;
                                if v_isSharedCheck_4726_ == 0 {
                                    v___x_4693_ = v___x_4683_;
                                    v_isShared_4694_ = v_isSharedCheck_4726_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_4691_);
                                    lean_dec(v___x_4683_);
                                    v___x_4693_ = lean_box(0);
                                    v_isShared_4694_ = v_isSharedCheck_4726_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_4670_);
                    lean_dec(v_declHint_4666_);
                    v___x_4727_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4727_, 0, v_msg_4665_);
                    return v___x_4727_;
                }
            }
            1 => {
                v___x_4695_ = lean_box(0);
                v___x_4696_ = l_Lean_Environment_header(v_env_4670_);
                lean_dec_ref(v_env_4670_);
                v___x_4697_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4696_);
                v_mod_4698_ = lean_array_get(v___x_4695_, v___x_4697_, v_val_4691_);
                lean_dec(v_val_4691_);
                lean_dec_ref(v___x_4697_);
                v___x_4699_ = l_Lean_isPrivateName(v_declHint_4666_);
                lean_dec(v_declHint_4666_);
                if v___x_4699_ == 0 {
                    v___x_4700_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                    v___x_4701_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4701_, 0, v___x_4700_);
                    lean_ctor_set(v___x_4701_, 1, v_c_4682_);
                    v___x_4702_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_4703_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4703_, 0, v___x_4701_);
                    lean_ctor_set(v___x_4703_, 1, v___x_4702_);
                    v___x_4704_ = l_Lean_MessageData_ofName(v_mod_4698_);
                    v___x_4705_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4705_, 0, v___x_4703_);
                    lean_ctor_set(v___x_4705_, 1, v___x_4704_);
                    v___x_4706_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_4707_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4707_, 0, v___x_4705_);
                    lean_ctor_set(v___x_4707_, 1, v___x_4706_);
                    v___x_4708_ = l_Lean_MessageData_note(v___x_4707_);
                    v___x_4709_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4709_, 0, v_msg_4665_);
                    lean_ctor_set(v___x_4709_, 1, v___x_4708_);
                    if v_isShared_4694_ == 0 {
                        lean_ctor_set_tag(v___x_4693_, 0);
                        lean_ctor_set(v___x_4693_, 0, v___x_4709_);
                        v___x_4711_ = v___x_4693_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4709_);
                        v___x_4711_ = v_reuseFailAlloc_4712_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4713_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                    v___x_4714_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4714_, 0, v___x_4713_);
                    lean_ctor_set(v___x_4714_, 1, v_c_4682_);
                    v___x_4715_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_4716_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4716_, 0, v___x_4714_);
                    lean_ctor_set(v___x_4716_, 1, v___x_4715_);
                    v___x_4717_ = l_Lean_MessageData_ofName(v_mod_4698_);
                    v___x_4718_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4718_, 0, v___x_4716_);
                    lean_ctor_set(v___x_4718_, 1, v___x_4717_);
                    v___x_4719_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_4720_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4720_, 0, v___x_4718_);
                    lean_ctor_set(v___x_4720_, 1, v___x_4719_);
                    v___x_4721_ = l_Lean_MessageData_note(v___x_4720_);
                    v___x_4722_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4722_, 0, v_msg_4665_);
                    lean_ctor_set(v___x_4722_, 1, v___x_4721_);
                    if v_isShared_4694_ == 0 {
                        lean_ctor_set_tag(v___x_4693_, 0);
                        lean_ctor_set(v___x_4693_, 0, v___x_4722_);
                        v___x_4724_ = v___x_4693_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4722_);
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
    mut v_msg_4728_: *mut LeanObject,
    mut v_declHint_4729_: *mut LeanObject,
    mut v___y_4730_: *mut LeanObject,
    mut v___y_4731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4732_: *mut LeanObject = core::ptr::null_mut();
    v_res_4732_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_4728_, v_declHint_4729_, v___y_4730_);
    lean_dec(v___y_4730_);
    return v_res_4732_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_4733_: *mut LeanObject,
    mut v_declHint_4734_: *mut LeanObject,
    mut v___y_4735_: *mut LeanObject,
    mut v___y_4736_: *mut LeanObject,
    mut v___y_4737_: *mut LeanObject,
    mut v___y_4738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4744_: u8 = 0;
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4740_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_4733_, v_declHint_4734_, v___y_4738_);
                v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
                v_isSharedCheck_4750_ = (!lean_is_exclusive(v___x_4740_)) as u8;
                if v_isSharedCheck_4750_ == 0 {
                    v___x_4743_ = v___x_4740_;
                    v_isShared_4744_ = v_isSharedCheck_4750_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4741_);
                    lean_dec(v___x_4740_);
                    v___x_4743_ = lean_box(0);
                    v_isShared_4744_ = v_isSharedCheck_4750_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4745_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4746_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_4746_, 0, v___x_4745_);
                lean_ctor_set(v___x_4746_, 1, v_a_4741_);
                if v_isShared_4744_ == 0 {
                    lean_ctor_set(v___x_4743_, 0, v___x_4746_);
                    v___x_4748_ = v___x_4743_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4746_);
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
    mut v_msg_4751_: *mut LeanObject,
    mut v_declHint_4752_: *mut LeanObject,
    mut v___y_4753_: *mut LeanObject,
    mut v___y_4754_: *mut LeanObject,
    mut v___y_4755_: *mut LeanObject,
    mut v___y_4756_: *mut LeanObject,
    mut v___y_4757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4758_: *mut LeanObject = core::ptr::null_mut();
    v_res_4758_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_4751_, v_declHint_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
    lean_dec(v___y_4756_);
    lean_dec_ref(v___y_4755_);
    lean_dec(v___y_4754_);
    lean_dec_ref(v___y_4753_);
    return v_res_4758_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_4759_: *mut LeanObject,
    mut v_msg_4760_: *mut LeanObject,
    mut v___y_4761_: *mut LeanObject,
    mut v___y_4762_: *mut LeanObject,
    mut v___y_4763_: *mut LeanObject,
    mut v___y_4764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4778_: u8 = 0;
    let mut v_cancelTk_x3f_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4780_: u8 = 0;
    let mut v_inheritedTraceOptions_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_4766_ = lean_ctor_get(v___y_4763_, 0);
    v_fileMap_4767_ = lean_ctor_get(v___y_4763_, 1);
    v_options_4768_ = lean_ctor_get(v___y_4763_, 2);
    v_currRecDepth_4769_ = lean_ctor_get(v___y_4763_, 3);
    v_maxRecDepth_4770_ = lean_ctor_get(v___y_4763_, 4);
    v_ref_4771_ = lean_ctor_get(v___y_4763_, 5);
    v_currNamespace_4772_ = lean_ctor_get(v___y_4763_, 6);
    v_openDecls_4773_ = lean_ctor_get(v___y_4763_, 7);
    v_initHeartbeats_4774_ = lean_ctor_get(v___y_4763_, 8);
    v_maxHeartbeats_4775_ = lean_ctor_get(v___y_4763_, 9);
    v_quotContext_4776_ = lean_ctor_get(v___y_4763_, 10);
    v_currMacroScope_4777_ = lean_ctor_get(v___y_4763_, 11);
    v_diag_4778_ = lean_ctor_get_uint8(
        v___y_4763_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4779_ = lean_ctor_get(v___y_4763_, 12);
    v_suppressElabErrors_4780_ = lean_ctor_get_uint8(
        v___y_4763_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4781_ = lean_ctor_get(v___y_4763_, 13);
    v_ref_4782_ = l_Lean_replaceRef(v_ref_4759_, v_ref_4771_);
    lean_inc_ref(v_inheritedTraceOptions_4781_);
    lean_inc(v_cancelTk_x3f_4779_);
    lean_inc(v_currMacroScope_4777_);
    lean_inc(v_quotContext_4776_);
    lean_inc(v_maxHeartbeats_4775_);
    lean_inc(v_initHeartbeats_4774_);
    lean_inc(v_openDecls_4773_);
    lean_inc(v_currNamespace_4772_);
    lean_inc(v_maxRecDepth_4770_);
    lean_inc(v_currRecDepth_4769_);
    lean_inc_ref(v_options_4768_);
    lean_inc_ref(v_fileMap_4767_);
    lean_inc_ref(v_fileName_4766_);
    v___x_4783_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_4783_, 0, v_fileName_4766_);
    lean_ctor_set(v___x_4783_, 1, v_fileMap_4767_);
    lean_ctor_set(v___x_4783_, 2, v_options_4768_);
    lean_ctor_set(v___x_4783_, 3, v_currRecDepth_4769_);
    lean_ctor_set(v___x_4783_, 4, v_maxRecDepth_4770_);
    lean_ctor_set(v___x_4783_, 5, v_ref_4782_);
    lean_ctor_set(v___x_4783_, 6, v_currNamespace_4772_);
    lean_ctor_set(v___x_4783_, 7, v_openDecls_4773_);
    lean_ctor_set(v___x_4783_, 8, v_initHeartbeats_4774_);
    lean_ctor_set(v___x_4783_, 9, v_maxHeartbeats_4775_);
    lean_ctor_set(v___x_4783_, 10, v_quotContext_4776_);
    lean_ctor_set(v___x_4783_, 11, v_currMacroScope_4777_);
    lean_ctor_set(v___x_4783_, 12, v_cancelTk_x3f_4779_);
    lean_ctor_set(v___x_4783_, 13, v_inheritedTraceOptions_4781_);
    lean_ctor_set_uint8(
        v___x_4783_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_4778_,
    );
    lean_ctor_set_uint8(
        v___x_4783_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4780_,
    );
    v___x_4784_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v_msg_4760_, v___y_4761_, v___y_4762_, v___x_4783_, v___y_4764_);
    lean_dec_ref_known(v___x_4783_, 14);
    return v___x_4784_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_4785_: *mut LeanObject,
    mut v_msg_4786_: *mut LeanObject,
    mut v___y_4787_: *mut LeanObject,
    mut v___y_4788_: *mut LeanObject,
    mut v___y_4789_: *mut LeanObject,
    mut v___y_4790_: *mut LeanObject,
    mut v___y_4791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4792_: *mut LeanObject = core::ptr::null_mut();
    v_res_4792_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_4785_, v_msg_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_);
    lean_dec(v___y_4790_);
    lean_dec_ref(v___y_4789_);
    lean_dec(v___y_4788_);
    lean_dec_ref(v___y_4787_);
    lean_dec(v_ref_4785_);
    return v_res_4792_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_4793_: *mut LeanObject,
    mut v_msg_4794_: *mut LeanObject,
    mut v_declHint_4795_: *mut LeanObject,
    mut v___y_4796_: *mut LeanObject,
    mut v___y_4797_: *mut LeanObject,
    mut v___y_4798_: *mut LeanObject,
    mut v___y_4799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    v___x_4801_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_4794_, v_declHint_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
    v_a_4802_ = lean_ctor_get(v___x_4801_, 0);
    lean_inc(v_a_4802_);
    lean_dec_ref(v___x_4801_);
    v___x_4803_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_4793_, v_a_4802_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
    return v___x_4803_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_4804_: *mut LeanObject,
    mut v_msg_4805_: *mut LeanObject,
    mut v_declHint_4806_: *mut LeanObject,
    mut v___y_4807_: *mut LeanObject,
    mut v___y_4808_: *mut LeanObject,
    mut v___y_4809_: *mut LeanObject,
    mut v___y_4810_: *mut LeanObject,
    mut v___y_4811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4812_: *mut LeanObject = core::ptr::null_mut();
    v_res_4812_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_4804_, v_msg_4805_, v_declHint_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
    lean_dec(v___y_4810_);
    lean_dec_ref(v___y_4809_);
    lean_dec(v___y_4808_);
    lean_dec_ref(v___y_4807_);
    lean_dec(v_ref_4804_);
    return v_res_4812_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    v___x_4814_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_4815_ = l_Lean_stringToMessageData(v___x_4814_);
    return v___x_4815_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(
    mut v_ref_4816_: *mut LeanObject,
    mut v_constName_4817_: *mut LeanObject,
    mut v___y_4818_: *mut LeanObject,
    mut v___y_4819_: *mut LeanObject,
    mut v___y_4820_: *mut LeanObject,
    mut v___y_4821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: u8 = 0;
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    v___x_4823_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_4824_ = 0;
    lean_inc(v_constName_4817_);
    v___x_4825_ = l_Lean_MessageData_ofConstName(v_constName_4817_, v___x_4824_);
    v___x_4826_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4826_, 0, v___x_4823_);
    lean_ctor_set(v___x_4826_, 1, v___x_4825_);
    v___x_4827_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once), _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1);
    v___x_4828_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4828_, 0, v___x_4826_);
    lean_ctor_set(v___x_4828_, 1, v___x_4827_);
    v___x_4829_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_4816_, v___x_4828_, v_constName_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
    return v___x_4829_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_4830_: *mut LeanObject,
    mut v_constName_4831_: *mut LeanObject,
    mut v___y_4832_: *mut LeanObject,
    mut v___y_4833_: *mut LeanObject,
    mut v___y_4834_: *mut LeanObject,
    mut v___y_4835_: *mut LeanObject,
    mut v___y_4836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4837_: *mut LeanObject = core::ptr::null_mut();
    v_res_4837_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(v_ref_4830_, v_constName_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
    lean_dec(v___y_4835_);
    lean_dec_ref(v___y_4834_);
    lean_dec(v___y_4833_);
    lean_dec_ref(v___y_4832_);
    lean_dec(v_ref_4830_);
    return v_res_4837_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(
    mut v_constName_4838_: *mut LeanObject,
    mut v___y_4839_: *mut LeanObject,
    mut v___y_4840_: *mut LeanObject,
    mut v___y_4841_: *mut LeanObject,
    mut v___y_4842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    v_ref_4844_ = lean_ctor_get(v___y_4841_, 5);
    v___x_4845_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(v_ref_4844_, v_constName_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
    return v___x_4845_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg___boxed(
    mut v_constName_4846_: *mut LeanObject,
    mut v___y_4847_: *mut LeanObject,
    mut v___y_4848_: *mut LeanObject,
    mut v___y_4849_: *mut LeanObject,
    mut v___y_4850_: *mut LeanObject,
    mut v___y_4851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4852_: *mut LeanObject = core::ptr::null_mut();
    v_res_4852_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(v_constName_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
    lean_dec(v___y_4850_);
    lean_dec_ref(v___y_4849_);
    lean_dec(v___y_4848_);
    lean_dec_ref(v___y_4847_);
    return v_res_4852_;
}
pub unsafe fn l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(
    mut v_constName_4853_: *mut LeanObject,
    mut v___y_4854_: *mut LeanObject,
    mut v___y_4855_: *mut LeanObject,
    mut v___y_4856_: *mut LeanObject,
    mut v___y_4857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: u8 = 0;
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4867_: u8 = 0;
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4859_ = lean_st_ref_get(v___y_4857_);
                v_env_4860_ = lean_ctor_get(v___x_4859_, 0);
                lean_inc_ref(v_env_4860_);
                lean_dec(v___x_4859_);
                v___x_4861_ = 0;
                lean_inc(v_constName_4853_);
                v___x_4862_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_4860_,
                    v_constName_4853_,
                    v___x_4861_,
                );
                if lean_obj_tag(v___x_4862_) == 0 {
                    v___x_4863_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(v_constName_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
                    return v___x_4863_;
                } else {
                    lean_dec(v_constName_4853_);
                    v_val_4864_ = lean_ctor_get(v___x_4862_, 0);
                    v_isSharedCheck_4871_ = (!lean_is_exclusive(v___x_4862_)) as u8;
                    if v_isSharedCheck_4871_ == 0 {
                        v___x_4866_ = v___x_4862_;
                        v_isShared_4867_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4864_);
                        lean_dec(v___x_4862_);
                        v___x_4866_ = lean_box(0);
                        v_isShared_4867_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4867_ == 0 {
                    lean_ctor_set_tag(v___x_4866_, 0);
                    v___x_4869_ = v___x_4866_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4870_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_val_4864_);
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
    mut v_constName_4872_: *mut LeanObject,
    mut v___y_4873_: *mut LeanObject,
    mut v___y_4874_: *mut LeanObject,
    mut v___y_4875_: *mut LeanObject,
    mut v___y_4876_: *mut LeanObject,
    mut v___y_4877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4878_: *mut LeanObject = core::ptr::null_mut();
    v_res_4878_ =
        l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(
            v_constName_4872_,
            v___y_4873_,
            v___y_4874_,
            v___y_4875_,
            v___y_4876_,
        );
    lean_dec(v___y_4876_);
    lean_dec_ref(v___y_4875_);
    lean_dec(v___y_4874_);
    lean_dec_ref(v___y_4873_);
    return v_res_4878_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0()
-> *mut LeanObject {
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    v___x_4879_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4879_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1()
-> *mut LeanObject {
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    v___x_4880_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0,
    );
    v___x_4881_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4881_, 0, v___x_4880_);
    return v___x_4881_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2()
-> *mut LeanObject {
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    v___x_4882_ = lean_unsigned_to_nat(0);
    v___x_4883_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1,
    );
    v___x_4884_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4884_, 0, v___x_4883_);
    lean_ctor_set(v___x_4884_, 1, v___x_4882_);
    return v___x_4884_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3()
-> *mut LeanObject {
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    v___x_4885_ = lean_unsigned_to_nat(32);
    v___x_4886_ = lean_mk_empty_array_with_capacity(v___x_4885_);
    v___x_4887_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4887_, 0, v___x_4886_);
    return v___x_4887_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4()
-> *mut LeanObject {
    let mut v___x_4888_: usize = 0;
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    v___x_4888_ = 5usize;
    v___x_4889_ = lean_unsigned_to_nat(0);
    v___x_4890_ = lean_unsigned_to_nat(32);
    v___x_4891_ = lean_mk_empty_array_with_capacity(v___x_4890_);
    v___x_4892_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3,
    );
    v___x_4893_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4893_, 0, v___x_4892_);
    lean_ctor_set(v___x_4893_, 1, v___x_4891_);
    lean_ctor_set(v___x_4893_, 2, v___x_4889_);
    lean_ctor_set(v___x_4893_, 3, v___x_4889_);
    lean_ctor_set_usize(v___x_4893_, 4, v___x_4888_);
    return v___x_4893_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5()
-> *mut LeanObject {
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    v___x_4894_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4,
    );
    v___x_4895_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1,
    );
    v___x_4896_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4896_, 0, v___x_4895_);
    lean_ctor_set(v___x_4896_, 1, v___x_4895_);
    lean_ctor_set(v___x_4896_, 2, v___x_4895_);
    lean_ctor_set(v___x_4896_, 3, v___x_4894_);
    return v___x_4896_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6()
-> *mut LeanObject {
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    v___x_4897_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5,
    );
    v___x_4898_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2,
    );
    v___x_4899_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4899_, 0, v___x_4898_);
    lean_ctor_set(v___x_4899_, 1, v___x_4897_);
    return v___x_4899_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10()
-> *mut LeanObject {
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    v___x_4905_ = lean_unsigned_to_nat(0);
    v___x_4906_ = l_Lean_Level_ofNat(v___x_4905_);
    return v___x_4906_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11()
-> *mut LeanObject {
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    v___x_4907_ = lean_box(0);
    v___x_4908_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10_once
        ),
        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10,
    );
    v___x_4909_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4909_, 0, v___x_4908_);
    lean_ctor_set(v___x_4909_, 1, v___x_4907_);
    return v___x_4909_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12()
-> *mut LeanObject {
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    v___x_4910_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    v___x_4914_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13;
    v___x_4915_ = l_Lean_stringToMessageData(v___x_4914_);
    return v___x_4915_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16()
-> *mut LeanObject {
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    v___x_4917_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15;
    v___x_4918_ = l_Lean_stringToMessageData(v___x_4917_);
    return v___x_4918_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(
    mut v_ctx_4919_: *mut LeanObject,
    mut v_simprocs_4920_: *mut LeanObject,
    mut v_eqThmName_4921_: *mut LeanObject,
    mut v_destThmName_4922_: *mut LeanObject,
    mut v_a_4923_: *mut LeanObject,
    mut v_a_4924_: *mut LeanObject,
    mut v_a_4925_: *mut LeanObject,
    mut v_a_4926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4945_: u8 = 0;
    let mut v___y_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: u8 = 0;
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4978_: u8 = 0;
    let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4982_: u8 = 0;
    let mut v_options_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4984_: u8 = 0;
    let mut v_inheritedTraceOptions_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: u8 = 0;
    let mut v_expr_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4998_: u8 = 0;
    let mut v_unused_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5003_: u8 = 0;
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5007_: u8 = 0;
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v_unused_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5013_: u8 = 0;
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_eqThmName_4921_);
                v___x_4928_ = l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(v_eqThmName_4921_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
                if lean_obj_tag(v___x_4928_) == 0 {
                    v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
                    lean_inc(v_a_4929_);
                    lean_dec_ref_known(v___x_4928_, 1);
                    v_levelParams_4930_ = lean_ctor_get(v_a_4929_, 1);
                    v_type_4931_ = lean_ctor_get(v_a_4929_, 2);
                    v_isSharedCheck_5008_ = (!lean_is_exclusive(v_a_4929_)) as u8;
                    if v_isSharedCheck_5008_ == 0 {
                        v_unused_5009_ = lean_ctor_get(v_a_4929_, 0);
                        lean_dec(v_unused_5009_);
                        v___x_4933_ = v_a_4929_;
                        v_isShared_4934_ = v_isSharedCheck_5008_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_type_4931_);
                        lean_inc(v_levelParams_4930_);
                        lean_dec(v_a_4929_);
                        v___x_4933_ = lean_box(0);
                        v_isShared_4934_ = v_isSharedCheck_5008_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_destThmName_4922_);
                    lean_dec(v_eqThmName_4921_);
                    lean_dec_ref(v_simprocs_4920_);
                    lean_dec_ref(v_ctx_4919_);
                    v_a_5010_ = lean_ctor_get(v___x_4928_, 0);
                    v_isSharedCheck_5017_ = (!lean_is_exclusive(v___x_4928_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v___x_5012_ = v___x_4928_;
                        v_isShared_5013_ = v_isSharedCheck_5017_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5010_);
                        lean_dec(v___x_4928_);
                        v___x_5012_ = lean_box(0);
                        v_isShared_5013_ = v_isSharedCheck_5017_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4935_ = lean_unsigned_to_nat(1);
                v___x_4936_ = lean_mk_empty_array_with_capacity(v___x_4935_);
                v___x_4937_ = lean_array_push(v___x_4936_, v_simprocs_4920_);
                v___x_4938_ = lean_box(0);
                v___x_4939_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6_once
                    ),
                    _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6,
                );
                lean_inc_ref(v_type_4931_);
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
                if lean_obj_tag(v___x_4940_) == 0 {
                    v_a_4941_ = lean_ctor_get(v___x_4940_, 0);
                    lean_inc(v_a_4941_);
                    lean_dec_ref_known(v___x_4940_, 1);
                    v_fst_4942_ = lean_ctor_get(v_a_4941_, 0);
                    v_isSharedCheck_4998_ = (!lean_is_exclusive(v_a_4941_)) as u8;
                    if v_isSharedCheck_4998_ == 0 {
                        v_unused_4999_ = lean_ctor_get(v_a_4941_, 1);
                        lean_dec(v_unused_4999_);
                        v___x_4944_ = v_a_4941_;
                        v_isShared_4945_ = v_isSharedCheck_4998_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_4942_);
                        lean_dec(v_a_4941_);
                        v___x_4944_ = lean_box(0);
                        v_isShared_4945_ = v_isSharedCheck_4998_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4933_);
                    lean_dec_ref(v_type_4931_);
                    lean_dec(v_levelParams_4930_);
                    lean_dec(v_destThmName_4922_);
                    lean_dec(v_eqThmName_4921_);
                    v_a_5000_ = lean_ctor_get(v___x_4940_, 0);
                    v_isSharedCheck_5007_ = (!lean_is_exclusive(v___x_4940_)) as u8;
                    if v_isSharedCheck_5007_ == 0 {
                        v___x_5002_ = v___x_4940_;
                        v_isShared_5003_ = v_isSharedCheck_5007_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5000_);
                        lean_dec(v___x_4940_);
                        v___x_5002_ = lean_box(0);
                        v_isShared_5003_ = v_isSharedCheck_5007_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_options_4983_ = lean_ctor_get(v_a_4925_, 2);
                v_hasTrace_4984_ = lean_ctor_get_uint8(
                    v_options_4983_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_4984_ == 0 {
                    v___y_4947_ = v_a_4923_;
                    v___y_4948_ = v_a_4924_;
                    v___y_4949_ = v_a_4925_;
                    v___y_4950_ = v_a_4926_;
                    state = 3;
                    continue;
                } else {
                    v_inheritedTraceOptions_4985_ = lean_ctor_get(v_a_4925_, 13);
                    v___x_4986_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3;
                    v___x_4987_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6);
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
                        v_expr_4989_ = lean_ctor_get(v_fst_4942_, 0);
                        v___x_4990_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14);
                        lean_inc(v_destThmName_4922_);
                        v___x_4991_ = l_Lean_MessageData_ofName(v_destThmName_4922_);
                        v___x_4992_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4992_, 0, v___x_4990_);
                        lean_ctor_set(v___x_4992_, 1, v___x_4991_);
                        v___x_4993_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16);
                        v___x_4994_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4994_, 0, v___x_4992_);
                        lean_ctor_set(v___x_4994_, 1, v___x_4993_);
                        lean_inc_ref(v_expr_4989_);
                        v___x_4995_ = l_Lean_indentExpr(v_expr_4989_);
                        v___x_4996_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4996_, 0, v___x_4994_);
                        lean_ctor_set(v___x_4996_, 1, v___x_4995_);
                        v___x_4997_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v___x_4986_, v___x_4996_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
                        if lean_obj_tag(v___x_4997_) == 0 {
                            lean_dec_ref_known(v___x_4997_, 1);
                            v___y_4947_ = v_a_4923_;
                            v___y_4948_ = v_a_4924_;
                            v___y_4949_ = v_a_4925_;
                            v___y_4950_ = v_a_4926_;
                            state = 3;
                            continue;
                        } else {
                            lean_del_object(v___x_4944_);
                            lean_dec(v_fst_4942_);
                            lean_del_object(v___x_4933_);
                            lean_dec_ref(v_type_4931_);
                            lean_dec(v_levelParams_4930_);
                            lean_dec(v_destThmName_4922_);
                            lean_dec(v_eqThmName_4921_);
                            return v___x_4997_;
                        }
                    }
                }
            }
            3 => {
                lean_inc(v_fst_4942_);
                v___x_4951_ = l_Lean_Meta_Simp_Result_getProof(
                    v_fst_4942_,
                    v___y_4947_,
                    v___y_4948_,
                    v___y_4949_,
                    v___y_4950_,
                );
                if lean_obj_tag(v___x_4951_) == 0 {
                    v_a_4952_ = lean_ctor_get(v___x_4951_, 0);
                    lean_inc(v_a_4952_);
                    lean_dec_ref_known(v___x_4951_, 1);
                    v_expr_4953_ = lean_ctor_get(v_fst_4942_, 0);
                    lean_inc_ref_n(v_expr_4953_, 2);
                    lean_dec(v_fst_4942_);
                    v___x_4954_ = lean_box(0);
                    lean_inc(v_levelParams_4930_);
                    v___x_4955_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__2(v_levelParams_4930_, v___x_4954_);
                    v___x_4956_ = l_Lean_mkConst(v_eqThmName_4921_, v___x_4955_);
                    v___x_4957_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12_once
                        ),
                        _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12,
                    );
                    v___x_4958_ = lean_unsigned_to_nat(4);
                    v___x_4959_ = lean_mk_empty_array_with_capacity(v___x_4958_);
                    v___x_4960_ = lean_array_push(v___x_4959_, v_type_4931_);
                    v___x_4961_ = lean_array_push(v___x_4960_, v_expr_4953_);
                    v___x_4962_ = lean_array_push(v___x_4961_, v_a_4952_);
                    v___x_4963_ = lean_array_push(v___x_4962_, v___x_4956_);
                    v___x_4964_ = l_Lean_mkAppN(v___x_4957_, v___x_4963_);
                    lean_dec_ref(v___x_4963_);
                    lean_inc(v_destThmName_4922_);
                    if v_isShared_4934_ == 0 {
                        lean_ctor_set(v___x_4933_, 2, v_expr_4953_);
                        lean_ctor_set(v___x_4933_, 0, v_destThmName_4922_);
                        v___x_4966_ = v___x_4933_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_destThmName_4922_);
                        lean_ctor_set(v_reuseFailAlloc_4974_, 1, v_levelParams_4930_);
                        lean_ctor_set(v_reuseFailAlloc_4974_, 2, v_expr_4953_);
                        v___x_4966_ = v_reuseFailAlloc_4974_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4944_);
                    lean_dec(v_fst_4942_);
                    lean_del_object(v___x_4933_);
                    lean_dec_ref(v_type_4931_);
                    lean_dec(v_levelParams_4930_);
                    lean_dec(v_destThmName_4922_);
                    lean_dec(v_eqThmName_4921_);
                    v_a_4975_ = lean_ctor_get(v___x_4951_, 0);
                    v_isSharedCheck_4982_ = (!lean_is_exclusive(v___x_4951_)) as u8;
                    if v_isSharedCheck_4982_ == 0 {
                        v___x_4977_ = v___x_4951_;
                        v_isShared_4978_ = v_isSharedCheck_4982_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4975_);
                        lean_dec(v___x_4951_);
                        v___x_4977_ = lean_box(0);
                        v_isShared_4978_ = v_isSharedCheck_4982_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4945_ == 0 {
                    lean_ctor_set_tag(v___x_4944_, 1);
                    lean_ctor_set(v___x_4944_, 1, v___x_4954_);
                    lean_ctor_set(v___x_4944_, 0, v_destThmName_4922_);
                    v___x_4968_ = v___x_4944_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_destThmName_4922_);
                    lean_ctor_set(v_reuseFailAlloc_4973_, 1, v___x_4954_);
                    v___x_4968_ = v_reuseFailAlloc_4973_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4969_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4969_, 0, v___x_4966_);
                lean_ctor_set(v___x_4969_, 1, v___x_4964_);
                lean_ctor_set(v___x_4969_, 2, v___x_4968_);
                v___x_4970_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_4970_, 0, v___x_4969_);
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
                    v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4975_);
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
                    v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_5000_);
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
                    v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
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
    mut v_ctx_5018_: *mut LeanObject,
    mut v_simprocs_5019_: *mut LeanObject,
    mut v_eqThmName_5020_: *mut LeanObject,
    mut v_destThmName_5021_: *mut LeanObject,
    mut v_a_5022_: *mut LeanObject,
    mut v_a_5023_: *mut LeanObject,
    mut v_a_5024_: *mut LeanObject,
    mut v_a_5025_: *mut LeanObject,
    mut v_a_5026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5027_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5025_);
    lean_dec_ref(v_a_5024_);
    lean_dec(v_a_5023_);
    lean_dec_ref(v_a_5022_);
    return v_res_5027_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0(
    mut v_00_u03b1_5028_: *mut LeanObject,
    mut v_constName_5029_: *mut LeanObject,
    mut v___y_5030_: *mut LeanObject,
    mut v___y_5031_: *mut LeanObject,
    mut v___y_5032_: *mut LeanObject,
    mut v___y_5033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5035_: *mut LeanObject = core::ptr::null_mut();
    v___x_5035_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(v_constName_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_);
    return v___x_5035_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___boxed(
    mut v_00_u03b1_5036_: *mut LeanObject,
    mut v_constName_5037_: *mut LeanObject,
    mut v___y_5038_: *mut LeanObject,
    mut v___y_5039_: *mut LeanObject,
    mut v___y_5040_: *mut LeanObject,
    mut v___y_5041_: *mut LeanObject,
    mut v___y_5042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5043_: *mut LeanObject = core::ptr::null_mut();
    v_res_5043_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0(v_00_u03b1_5036_, v_constName_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
    lean_dec(v___y_5041_);
    lean_dec_ref(v___y_5040_);
    lean_dec(v___y_5039_);
    lean_dec_ref(v___y_5038_);
    return v_res_5043_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1(
    mut v_00_u03b1_5044_: *mut LeanObject,
    mut v_ref_5045_: *mut LeanObject,
    mut v_constName_5046_: *mut LeanObject,
    mut v___y_5047_: *mut LeanObject,
    mut v___y_5048_: *mut LeanObject,
    mut v___y_5049_: *mut LeanObject,
    mut v___y_5050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    v___x_5052_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(v_ref_5045_, v_constName_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_);
    return v___x_5052_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_5053_: *mut LeanObject,
    mut v_ref_5054_: *mut LeanObject,
    mut v_constName_5055_: *mut LeanObject,
    mut v___y_5056_: *mut LeanObject,
    mut v___y_5057_: *mut LeanObject,
    mut v___y_5058_: *mut LeanObject,
    mut v___y_5059_: *mut LeanObject,
    mut v___y_5060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5061_: *mut LeanObject = core::ptr::null_mut();
    v_res_5061_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1(v_00_u03b1_5053_, v_ref_5054_, v_constName_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_);
    lean_dec(v___y_5059_);
    lean_dec_ref(v___y_5058_);
    lean_dec(v___y_5057_);
    lean_dec_ref(v___y_5056_);
    lean_dec(v_ref_5054_);
    return v_res_5061_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_5062_: *mut LeanObject,
    mut v_ref_5063_: *mut LeanObject,
    mut v_msg_5064_: *mut LeanObject,
    mut v_declHint_5065_: *mut LeanObject,
    mut v___y_5066_: *mut LeanObject,
    mut v___y_5067_: *mut LeanObject,
    mut v___y_5068_: *mut LeanObject,
    mut v___y_5069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    v___x_5071_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_5063_, v_msg_5064_, v_declHint_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_);
    return v___x_5071_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_5072_: *mut LeanObject,
    mut v_ref_5073_: *mut LeanObject,
    mut v_msg_5074_: *mut LeanObject,
    mut v_declHint_5075_: *mut LeanObject,
    mut v___y_5076_: *mut LeanObject,
    mut v___y_5077_: *mut LeanObject,
    mut v___y_5078_: *mut LeanObject,
    mut v___y_5079_: *mut LeanObject,
    mut v___y_5080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5081_: *mut LeanObject = core::ptr::null_mut();
    v_res_5081_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_5072_, v_ref_5073_, v_msg_5074_, v_declHint_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_);
    lean_dec(v___y_5079_);
    lean_dec_ref(v___y_5078_);
    lean_dec(v___y_5077_);
    lean_dec_ref(v___y_5076_);
    lean_dec(v_ref_5073_);
    return v_res_5081_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_5082_: *mut LeanObject,
    mut v_declHint_5083_: *mut LeanObject,
    mut v___y_5084_: *mut LeanObject,
    mut v___y_5085_: *mut LeanObject,
    mut v___y_5086_: *mut LeanObject,
    mut v___y_5087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    v___x_5089_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_5082_, v_declHint_5083_, v___y_5087_);
    return v___x_5089_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_5090_: *mut LeanObject,
    mut v_declHint_5091_: *mut LeanObject,
    mut v___y_5092_: *mut LeanObject,
    mut v___y_5093_: *mut LeanObject,
    mut v___y_5094_: *mut LeanObject,
    mut v___y_5095_: *mut LeanObject,
    mut v___y_5096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5097_: *mut LeanObject = core::ptr::null_mut();
    v_res_5097_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_5090_, v_declHint_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
    lean_dec(v___y_5095_);
    lean_dec_ref(v___y_5094_);
    lean_dec(v___y_5093_);
    lean_dec_ref(v___y_5092_);
    return v_res_5097_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_5098_: *mut LeanObject,
    mut v_ref_5099_: *mut LeanObject,
    mut v_msg_5100_: *mut LeanObject,
    mut v___y_5101_: *mut LeanObject,
    mut v___y_5102_: *mut LeanObject,
    mut v___y_5103_: *mut LeanObject,
    mut v___y_5104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    v___x_5106_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_5099_, v_msg_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
    return v___x_5106_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_5107_: *mut LeanObject,
    mut v_ref_5108_: *mut LeanObject,
    mut v_msg_5109_: *mut LeanObject,
    mut v___y_5110_: *mut LeanObject,
    mut v___y_5111_: *mut LeanObject,
    mut v___y_5112_: *mut LeanObject,
    mut v___y_5113_: *mut LeanObject,
    mut v___y_5114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5115_: *mut LeanObject = core::ptr::null_mut();
    v_res_5115_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_5107_, v_ref_5108_, v_msg_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_);
    lean_dec(v___y_5113_);
    lean_dec_ref(v___y_5112_);
    lean_dec(v___y_5111_);
    lean_dec_ref(v___y_5110_);
    lean_dec(v_ref_5108_);
    return v_res_5115_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(
    mut v___x_5116_: *mut LeanObject,
    mut v___x_5117_: *mut LeanObject,
    mut v_instName_5118_: *mut LeanObject,
    mut v___x_5119_: u8,
    mut v_a_5120_: *mut LeanObject,
    mut v_a_5121_: *mut LeanObject,
    mut v_as_5122_: *mut LeanObject,
    mut v_sz_5123_: usize,
    mut v_i_5124_: usize,
    mut v_b_5125_: *mut LeanObject,
    mut v___y_5126_: *mut LeanObject,
    mut v___y_5127_: *mut LeanObject,
    mut v___y_5128_: *mut LeanObject,
    mut v___y_5129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5131_: u8 = 0;
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_step_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: u8 = 0;
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5140_: u8 = 0;
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: usize = 0;
    let mut v___x_5154_: usize = 0;
    let mut v_reuseFailAlloc_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5160_: u8 = 0;
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5164_: u8 = 0;
    let mut v_isSharedCheck_5165_: u8 = 0;
    let mut v_unused_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5131_ = lean_usize_dec_lt(v_i_5124_, v_sz_5123_);
                if v___x_5131_ == 0 {
                    lean_dec_ref(v_a_5121_);
                    lean_dec_ref(v_a_5120_);
                    lean_dec(v_instName_5118_);
                    lean_dec_ref(v___x_5116_);
                    v___x_5132_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5132_, 0, v_b_5125_);
                    return v___x_5132_;
                } else {
                    v_start_5133_ = lean_ctor_get(v_b_5125_, 0);
                    v_stop_5134_ = lean_ctor_get(v_b_5125_, 1);
                    v_step_5135_ = lean_ctor_get(v_b_5125_, 2);
                    v___x_5136_ = lean_nat_dec_lt(v_start_5133_, v_stop_5134_);
                    if v___x_5136_ == 0 {
                        lean_dec_ref(v_a_5121_);
                        lean_dec_ref(v_a_5120_);
                        lean_dec(v_instName_5118_);
                        lean_dec_ref(v___x_5116_);
                        v___x_5137_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5137_, 0, v_b_5125_);
                        return v___x_5137_;
                    } else {
                        lean_inc(v_step_5135_);
                        lean_inc(v_stop_5134_);
                        lean_inc(v_start_5133_);
                        v_isSharedCheck_5165_ = (!lean_is_exclusive(v_b_5125_)) as u8;
                        if v_isSharedCheck_5165_ == 0 {
                            v_unused_5166_ = lean_ctor_get(v_b_5125_, 2);
                            lean_dec(v_unused_5166_);
                            v_unused_5167_ = lean_ctor_get(v_b_5125_, 1);
                            lean_dec(v_unused_5167_);
                            v_unused_5168_ = lean_ctor_get(v_b_5125_, 0);
                            lean_dec(v_unused_5168_);
                            v___x_5139_ = v_b_5125_;
                            v_isShared_5140_ = v_isSharedCheck_5165_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_b_5125_);
                            v___x_5139_ = lean_box(0);
                            v_isShared_5140_ = v_isSharedCheck_5165_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5141_ = lean_unsigned_to_nat(1);
                v_a_5142_ = lean_array_uget_borrowed(v_as_5122_, v_i_5124_);
                v___x_5143_ =
                    l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1;
                lean_inc_ref(v___x_5116_);
                v___x_5144_ = lean_string_append(v___x_5116_, v___x_5143_);
                v___x_5145_ = lean_nat_add(v_start_5133_, v___x_5141_);
                v___x_5146_ = l_Nat_reprFast(v___x_5145_);
                v___x_5147_ = lean_string_append(v___x_5144_, v___x_5146_);
                lean_dec_ref(v___x_5146_);
                lean_inc(v_instName_5118_);
                v___x_5148_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                    v___x_5117_,
                    v_instName_5118_,
                    v___x_5119_,
                    v___x_5147_,
                );
                lean_inc(v_a_5142_);
                lean_inc_ref(v_a_5121_);
                lean_inc_ref(v_a_5120_);
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
                if lean_obj_tag(v___x_5149_) == 0 {
                    lean_dec_ref_known(v___x_5149_, 1);
                    v___x_5150_ = lean_nat_add(v_start_5133_, v_step_5135_);
                    lean_dec(v_start_5133_);
                    if v_isShared_5140_ == 0 {
                        lean_ctor_set(v___x_5139_, 0, v___x_5150_);
                        v___x_5152_ = v___x_5139_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5156_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5150_);
                        lean_ctor_set(v_reuseFailAlloc_5156_, 1, v_stop_5134_);
                        lean_ctor_set(v_reuseFailAlloc_5156_, 2, v_step_5135_);
                        v___x_5152_ = v_reuseFailAlloc_5156_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5139_);
                    lean_dec(v_step_5135_);
                    lean_dec(v_stop_5134_);
                    lean_dec(v_start_5133_);
                    lean_dec_ref(v_a_5121_);
                    lean_dec_ref(v_a_5120_);
                    lean_dec(v_instName_5118_);
                    lean_dec_ref(v___x_5116_);
                    v_a_5157_ = lean_ctor_get(v___x_5149_, 0);
                    v_isSharedCheck_5164_ = (!lean_is_exclusive(v___x_5149_)) as u8;
                    if v_isSharedCheck_5164_ == 0 {
                        v___x_5159_ = v___x_5149_;
                        v_isShared_5160_ = v_isSharedCheck_5164_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5157_);
                        lean_dec(v___x_5149_);
                        v___x_5159_ = lean_box(0);
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
                    v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
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
    mut v___x_5169_: *mut LeanObject,
    mut v___x_5170_: *mut LeanObject,
    mut v_instName_5171_: *mut LeanObject,
    mut v___x_5172_: *mut LeanObject,
    mut v_a_5173_: *mut LeanObject,
    mut v_a_5174_: *mut LeanObject,
    mut v_as_5175_: *mut LeanObject,
    mut v_sz_5176_: *mut LeanObject,
    mut v_i_5177_: *mut LeanObject,
    mut v_b_5178_: *mut LeanObject,
    mut v___y_5179_: *mut LeanObject,
    mut v___y_5180_: *mut LeanObject,
    mut v___y_5181_: *mut LeanObject,
    mut v___y_5182_: *mut LeanObject,
    mut v___y_5183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9646__boxed_5184_: u8 = 0;
    let mut v_sz_boxed_5185_: usize = 0;
    let mut v_i_boxed_5186_: usize = 0;
    let mut v_res_5187_: *mut LeanObject = core::ptr::null_mut();
    v___x_9646__boxed_5184_ = (lean_unbox(v___x_5172_) as u8);
    v_sz_boxed_5185_ = lean_unbox_usize(v_sz_5176_);
    lean_dec(v_sz_5176_);
    v_i_boxed_5186_ = lean_unbox_usize(v_i_5177_);
    lean_dec(v_i_5177_);
    v_res_5187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(v___x_5169_, v___x_5170_, v_instName_5171_, v___x_9646__boxed_5184_, v_a_5173_, v_a_5174_, v_as_5175_, v_sz_boxed_5185_, v_i_boxed_5186_, v_b_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_);
    lean_dec(v___y_5182_);
    lean_dec_ref(v___y_5181_);
    lean_dec(v___y_5180_);
    lean_dec_ref(v___y_5179_);
    lean_dec_ref(v_as_5175_);
    lean_dec_ref(v___x_5170_);
    return v_res_5187_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    v___x_5189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0;
    v___x_5190_ = l_Lean_stringToMessageData(v___x_5189_);
    return v___x_5190_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(
    mut v_a_5191_: *mut LeanObject,
    mut v___x_5192_: *mut LeanObject,
    mut v_instName_5193_: *mut LeanObject,
    mut v_a_5194_: *mut LeanObject,
    mut v_a_5195_: *mut LeanObject,
    mut v_as_5196_: *mut LeanObject,
    mut v_sz_5197_: usize,
    mut v_i_5198_: usize,
    mut v_b_5199_: *mut LeanObject,
    mut v___y_5200_: *mut LeanObject,
    mut v___y_5201_: *mut LeanObject,
    mut v___y_5202_: *mut LeanObject,
    mut v___y_5203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: usize = 0;
    let mut v___x_5208_: usize = 0;
    let mut v___x_5210_: u8 = 0;
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5217_: u8 = 0;
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_privateSpecs_5222_: u8 = 0;
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5235_: usize = 0;
    let mut v___x_5236_: usize = 0;
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5241_: u8 = 0;
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5245_: u8 = 0;
    let mut v_a_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5249_: u8 = 0;
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5253_: u8 = 0;
    let mut v___x_5254_: u8 = 0;
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5264_: u8 = 0;
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5268_: u8 = 0;
    let mut v_isSharedCheck_5269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5210_ = lean_usize_dec_lt(v_i_5198_, v_sz_5197_);
                if v___x_5210_ == 0 {
                    lean_dec_ref(v_a_5195_);
                    lean_dec_ref(v_a_5194_);
                    lean_dec(v_instName_5193_);
                    v___x_5211_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5211_, 0, v_b_5199_);
                    return v___x_5211_;
                } else {
                    v_a_5212_ = lean_array_uget(v_as_5196_, v_i_5198_);
                    v_fst_5213_ = lean_ctor_get(v_a_5212_, 0);
                    v_snd_5214_ = lean_ctor_get(v_a_5212_, 1);
                    v_isSharedCheck_5269_ = (!lean_is_exclusive(v_a_5212_)) as u8;
                    if v_isSharedCheck_5269_ == 0 {
                        v___x_5216_ = v_a_5212_;
                        v_isShared_5217_ = v_isSharedCheck_5269_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_5214_);
                        lean_inc(v_fst_5213_);
                        lean_dec(v_a_5212_);
                        v___x_5216_ = lean_box(0);
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
                lean_inc(v_snd_5214_);
                v___x_5218_ = l_Lean_Meta_getUnfoldEqnFor_x3f(
                    v_snd_5214_,
                    v___x_5210_,
                    v___y_5200_,
                    v___y_5201_,
                    v___y_5202_,
                    v___y_5203_,
                );
                if lean_obj_tag(v___x_5218_) == 0 {
                    v_a_5219_ = lean_ctor_get(v___x_5218_, 0);
                    lean_inc(v_a_5219_);
                    lean_dec_ref_known(v___x_5218_, 1);
                    v___x_5220_ = lean_box(0);
                    if lean_obj_tag(v_a_5219_) == 1 {
                        lean_del_object(v___x_5216_);
                        v_val_5221_ = lean_ctor_get(v_a_5219_, 0);
                        lean_inc(v_val_5221_);
                        lean_dec_ref_known(v_a_5219_, 1);
                        v_privateSpecs_5222_ = lean_ctor_get_uint8(
                            v_a_5191_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v___x_5223_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_fst_5213_,
                                v___x_5210_,
                            );
                        v___x_5224_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0;
                        lean_inc_ref(v___x_5223_);
                        v___x_5225_ = lean_string_append(v___x_5223_, v___x_5224_);
                        lean_inc(v_instName_5193_);
                        v___x_5226_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                            v___x_5192_,
                            v_instName_5193_,
                            v_privateSpecs_5222_,
                            v___x_5225_,
                        );
                        lean_inc_ref(v_a_5195_);
                        lean_inc_ref(v_a_5194_);
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
                        if lean_obj_tag(v___x_5227_) == 0 {
                            lean_dec_ref_known(v___x_5227_, 1);
                            v___x_5228_ = l_Lean_Meta_getEqnsFor_x3f(
                                v_snd_5214_,
                                v___y_5200_,
                                v___y_5201_,
                                v___y_5202_,
                                v___y_5203_,
                            );
                            if lean_obj_tag(v___x_5228_) == 0 {
                                v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
                                lean_inc(v_a_5229_);
                                lean_dec_ref_known(v___x_5228_, 1);
                                if lean_obj_tag(v_a_5229_) == 1 {
                                    v_val_5230_ = lean_ctor_get(v_a_5229_, 0);
                                    lean_inc(v_val_5230_);
                                    lean_dec_ref_known(v_a_5229_, 1);
                                    v___x_5231_ = lean_unsigned_to_nat(0);
                                    v___x_5232_ = lean_array_get_size(v_val_5230_);
                                    v___x_5233_ = lean_unsigned_to_nat(1);
                                    v___x_5234_ = lean_alloc_ctor(0, 3, (0) as u32);
                                    lean_ctor_set(v___x_5234_, 0, v___x_5231_);
                                    lean_ctor_set(v___x_5234_, 1, v___x_5232_);
                                    lean_ctor_set(v___x_5234_, 2, v___x_5233_);
                                    v_sz_5235_ = lean_array_size(v_val_5230_);
                                    v___x_5236_ = 0usize;
                                    lean_inc_ref(v_a_5195_);
                                    lean_inc_ref(v_a_5194_);
                                    lean_inc(v_instName_5193_);
                                    v___x_5237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(v___x_5223_, v___x_5192_, v_instName_5193_, v_privateSpecs_5222_, v_a_5194_, v_a_5195_, v_val_5230_, v_sz_5235_, v___x_5236_, v___x_5234_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_);
                                    lean_dec(v_val_5230_);
                                    if lean_obj_tag(v___x_5237_) == 0 {
                                        lean_dec_ref_known(v___x_5237_, 1);
                                        v_a_5206_ = v___x_5220_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_a_5195_);
                                        lean_dec_ref(v_a_5194_);
                                        lean_dec(v_instName_5193_);
                                        v_a_5238_ = lean_ctor_get(v___x_5237_, 0);
                                        v_isSharedCheck_5245_ =
                                            (!lean_is_exclusive(v___x_5237_)) as u8;
                                        if v_isSharedCheck_5245_ == 0 {
                                            v___x_5240_ = v___x_5237_;
                                            v_isShared_5241_ = v_isSharedCheck_5245_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5238_);
                                            lean_dec(v___x_5237_);
                                            v___x_5240_ = lean_box(0);
                                            v_isShared_5241_ = v_isSharedCheck_5245_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_5229_);
                                    lean_dec_ref(v___x_5223_);
                                    v_a_5206_ = v___x_5220_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_5223_);
                                lean_dec_ref(v_a_5195_);
                                lean_dec_ref(v_a_5194_);
                                lean_dec(v_instName_5193_);
                                v_a_5246_ = lean_ctor_get(v___x_5228_, 0);
                                v_isSharedCheck_5253_ = (!lean_is_exclusive(v___x_5228_)) as u8;
                                if v_isSharedCheck_5253_ == 0 {
                                    v___x_5248_ = v___x_5228_;
                                    v_isShared_5249_ = v_isSharedCheck_5253_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_5246_);
                                    lean_dec(v___x_5228_);
                                    v___x_5248_ = lean_box(0);
                                    v_isShared_5249_ = v_isSharedCheck_5253_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_5223_);
                            lean_dec(v_snd_5214_);
                            lean_dec_ref(v_a_5195_);
                            lean_dec_ref(v_a_5194_);
                            lean_dec(v_instName_5193_);
                            return v___x_5227_;
                        }
                    } else {
                        lean_dec(v_a_5219_);
                        lean_dec(v_fst_5213_);
                        v___x_5254_ = 0;
                        v___x_5255_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1);
                        v___x_5256_ = l_Lean_MessageData_ofConstName(v_snd_5214_, v___x_5254_);
                        if v_isShared_5217_ == 0 {
                            lean_ctor_set_tag(v___x_5216_, 7);
                            lean_ctor_set(v___x_5216_, 1, v___x_5256_);
                            lean_ctor_set(v___x_5216_, 0, v___x_5255_);
                            v___x_5258_ = v___x_5216_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_5260_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5260_, 0, v___x_5255_);
                            lean_ctor_set(v_reuseFailAlloc_5260_, 1, v___x_5256_);
                            v___x_5258_ = v_reuseFailAlloc_5260_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5216_);
                    lean_dec(v_snd_5214_);
                    lean_dec(v_fst_5213_);
                    lean_dec_ref(v_a_5195_);
                    lean_dec_ref(v_a_5194_);
                    lean_dec(v_instName_5193_);
                    v_a_5261_ = lean_ctor_get(v___x_5218_, 0);
                    v_isSharedCheck_5268_ = (!lean_is_exclusive(v___x_5218_)) as u8;
                    if v_isSharedCheck_5268_ == 0 {
                        v___x_5263_ = v___x_5218_;
                        v_isShared_5264_ = v_isSharedCheck_5268_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5261_);
                        lean_dec(v___x_5218_);
                        v___x_5263_ = lean_box(0);
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
                    v_reuseFailAlloc_5244_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_a_5238_);
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
                    v_reuseFailAlloc_5252_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_a_5246_);
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
                if lean_obj_tag(v___x_5259_) == 0 {
                    lean_dec_ref_known(v___x_5259_, 1);
                    v_a_5206_ = v___x_5220_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_a_5195_);
                    lean_dec_ref(v_a_5194_);
                    lean_dec(v_instName_5193_);
                    return v___x_5259_;
                }
            }
            8 => {
                if v_isShared_5264_ == 0 {
                    v___x_5266_ = v___x_5263_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5267_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5261_);
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
    mut v_a_5270_: *mut LeanObject,
    mut v___x_5271_: *mut LeanObject,
    mut v_instName_5272_: *mut LeanObject,
    mut v_a_5273_: *mut LeanObject,
    mut v_a_5274_: *mut LeanObject,
    mut v_as_5275_: *mut LeanObject,
    mut v_sz_5276_: *mut LeanObject,
    mut v_i_5277_: *mut LeanObject,
    mut v_b_5278_: *mut LeanObject,
    mut v___y_5279_: *mut LeanObject,
    mut v___y_5280_: *mut LeanObject,
    mut v___y_5281_: *mut LeanObject,
    mut v___y_5282_: *mut LeanObject,
    mut v___y_5283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5284_: usize = 0;
    let mut v_i_boxed_5285_: usize = 0;
    let mut v_res_5286_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5284_ = lean_unbox_usize(v_sz_5276_);
    lean_dec(v_sz_5276_);
    v_i_boxed_5285_ = lean_unbox_usize(v_i_5277_);
    lean_dec(v_i_5277_);
    v_res_5286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(v_a_5270_, v___x_5271_, v_instName_5272_, v_a_5273_, v_a_5274_, v_as_5275_, v_sz_boxed_5284_, v_i_boxed_5285_, v_b_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_);
    lean_dec(v___y_5282_);
    lean_dec_ref(v___y_5281_);
    lean_dec(v___y_5280_);
    lean_dec_ref(v___y_5279_);
    lean_dec_ref(v_as_5275_);
    lean_dec_ref(v___x_5271_);
    lean_dec_ref(v_a_5270_);
    return v_res_5286_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    v___x_5288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0;
    v___x_5289_ = l_Lean_stringToMessageData(v___x_5288_);
    return v___x_5289_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    v___x_5291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2;
    v___x_5292_ = l_Lean_stringToMessageData(v___x_5291_);
    return v___x_5292_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(
    mut v_as_5293_: *mut LeanObject,
    mut v_sz_5294_: usize,
    mut v_i_5295_: usize,
    mut v_b_5296_: *mut LeanObject,
    mut v___y_5297_: *mut LeanObject,
    mut v___y_5298_: *mut LeanObject,
    mut v___y_5299_: *mut LeanObject,
    mut v___y_5300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5302_: u8 = 0;
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5306_: u8 = 0;
    let mut v_a_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: usize = 0;
    let mut v___x_5324_: usize = 0;
    let mut v_a_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5329_: u8 = 0;
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5333_: u8 = 0;
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: u8 = 0;
    let mut v_name_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5350_: u8 = 0;
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5302_ = lean_usize_dec_lt(v_i_5295_, v_sz_5294_);
                if v___x_5302_ == 0 {
                    v___x_5303_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5303_, 0, v_b_5296_);
                    return v___x_5303_;
                } else {
                    v_options_5304_ = lean_ctor_get(v___y_5299_, 2);
                    v_inheritedTraceOptions_5305_ = lean_ctor_get(v___y_5299_, 13);
                    v_hasTrace_5306_ = lean_ctor_get_uint8(
                        v_options_5304_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                        v___x_5335_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6);
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
                            v_name_5337_ = lean_ctor_get(v_a_5307_, 0);
                            v_type_5338_ = lean_ctor_get(v_a_5307_, 2);
                            v___x_5339_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1);
                            lean_inc(v_name_5337_);
                            v___x_5340_ = l_Lean_MessageData_ofName(v_name_5337_);
                            v___x_5341_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5341_, 0, v___x_5339_);
                            lean_ctor_set(v___x_5341_, 1, v___x_5340_);
                            v___x_5342_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3);
                            v___x_5343_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5343_, 0, v___x_5341_);
                            lean_ctor_set(v___x_5343_, 1, v___x_5342_);
                            lean_inc_ref(v_type_5338_);
                            v___x_5344_ = l_Lean_MessageData_ofExpr(v_type_5338_);
                            v___x_5345_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5345_, 0, v___x_5343_);
                            lean_ctor_set(v___x_5345_, 1, v___x_5344_);
                            v___x_5346_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v___x_5334_, v___x_5345_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_);
                            if lean_obj_tag(v___x_5346_) == 0 {
                                lean_dec_ref_known(v___x_5346_, 1);
                                v___y_5309_ = v___y_5297_;
                                v___y_5310_ = v___y_5298_;
                                v___y_5311_ = v___y_5299_;
                                v___y_5312_ = v___y_5300_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_b_5296_);
                                v_a_5347_ = lean_ctor_get(v___x_5346_, 0);
                                v_isSharedCheck_5354_ = (!lean_is_exclusive(v___x_5346_)) as u8;
                                if v_isSharedCheck_5354_ == 0 {
                                    v___x_5349_ = v___x_5346_;
                                    v_isShared_5350_ = v_isSharedCheck_5354_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_5347_);
                                    lean_dec(v___x_5346_);
                                    v___x_5349_ = lean_box(0);
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
                v_name_5313_ = lean_ctor_get(v_a_5307_, 0);
                v_levelParams_5314_ = lean_ctor_get(v_a_5307_, 1);
                v_type_5315_ = lean_ctor_get(v_a_5307_, 2);
                lean_inc(v_name_5313_);
                v___x_5316_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5316_, 0, v_name_5313_);
                lean_inc(v_levelParams_5314_);
                v___x_5317_ = lean_array_mk(v_levelParams_5314_);
                v___x_5318_ = lean_unsigned_to_nat(1000);
                v___x_5319_ = l_Lean_Meta_simpGlobalConfig;
                lean_inc_ref(v_type_5315_);
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
                if lean_obj_tag(v___x_5320_) == 0 {
                    v_a_5321_ = lean_ctor_get(v___x_5320_, 0);
                    lean_inc(v_a_5321_);
                    lean_dec_ref_known(v___x_5320_, 1);
                    v___x_5322_ = l_Lean_Meta_SimpTheorems_addSimpTheorem(v_b_5296_, v_a_5321_);
                    v___x_5323_ = 1usize;
                    v___x_5324_ = lean_usize_add(v_i_5295_, v___x_5323_);
                    v_i_5295_ = v___x_5324_;
                    v_b_5296_ = v___x_5322_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_b_5296_);
                    v_a_5326_ = lean_ctor_get(v___x_5320_, 0);
                    v_isSharedCheck_5333_ = (!lean_is_exclusive(v___x_5320_)) as u8;
                    if v_isSharedCheck_5333_ == 0 {
                        v___x_5328_ = v___x_5320_;
                        v_isShared_5329_ = v_isSharedCheck_5333_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5326_);
                        lean_dec(v___x_5320_);
                        v___x_5328_ = lean_box(0);
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
                    v_reuseFailAlloc_5332_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5326_);
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
                    v_reuseFailAlloc_5353_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5347_);
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
    mut v_as_5355_: *mut LeanObject,
    mut v_sz_5356_: *mut LeanObject,
    mut v_i_5357_: *mut LeanObject,
    mut v_b_5358_: *mut LeanObject,
    mut v___y_5359_: *mut LeanObject,
    mut v___y_5360_: *mut LeanObject,
    mut v___y_5361_: *mut LeanObject,
    mut v___y_5362_: *mut LeanObject,
    mut v___y_5363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5364_: usize = 0;
    let mut v_i_boxed_5365_: usize = 0;
    let mut v_res_5366_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5364_ = lean_unbox_usize(v_sz_5356_);
    lean_dec(v_sz_5356_);
    v_i_boxed_5365_ = lean_unbox_usize(v_i_5357_);
    lean_dec(v_i_5357_);
    v_res_5366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(v_as_5355_, v_sz_boxed_5364_, v_i_boxed_5365_, v_b_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_);
    lean_dec(v___y_5362_);
    lean_dec_ref(v___y_5361_);
    lean_dec(v___y_5360_);
    lean_dec_ref(v___y_5359_);
    lean_dec_ref(v_as_5355_);
    return v_res_5366_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0(
    mut v___x_5374_: *mut LeanObject,
    mut v_thms_5375_: *mut LeanObject,
    mut v_fieldImpls_5376_: *mut LeanObject,
    mut v_a_5377_: *mut LeanObject,
    mut v_instName_5378_: *mut LeanObject,
    mut v___y_5379_: *mut LeanObject,
    mut v___y_5380_: *mut LeanObject,
    mut v___y_5381_: *mut LeanObject,
    mut v___y_5382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5386_: usize = 0;
    let mut v___x_5387_: usize = 0;
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5404_: usize = 0;
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5408_: u8 = 0;
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5412_: u8 = 0;
    let mut v_unused_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5417_: u8 = 0;
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5421_: u8 = 0;
    let mut v_a_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5425_: u8 = 0;
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5429_: u8 = 0;
    let mut v_a_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5433_: u8 = 0;
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5437_: u8 = 0;
    let mut v_a_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5441_: u8 = 0;
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5445_: u8 = 0;
    let mut v_a_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5449_: u8 = 0;
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5384_ =
                    l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_5374_, v___y_5382_);
                if lean_obj_tag(v___x_5384_) == 0 {
                    v_a_5385_ = lean_ctor_get(v___x_5384_, 0);
                    lean_inc(v_a_5385_);
                    lean_dec_ref_known(v___x_5384_, 1);
                    v_sz_5386_ = lean_array_size(v_thms_5375_);
                    v___x_5387_ = 0usize;
                    v___x_5388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(v_thms_5375_, v_sz_5386_, v___x_5387_, v_a_5385_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
                    if lean_obj_tag(v___x_5388_) == 0 {
                        v_a_5389_ = lean_ctor_get(v___x_5388_, 0);
                        lean_inc(v_a_5389_);
                        lean_dec_ref_known(v___x_5388_, 1);
                        v___x_5390_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_5382_);
                        if lean_obj_tag(v___x_5390_) == 0 {
                            v_a_5391_ = lean_ctor_get(v___x_5390_, 0);
                            lean_inc(v_a_5391_);
                            lean_dec_ref_known(v___x_5390_, 1);
                            v___x_5392_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0;
                            v___x_5393_ = lean_unsigned_to_nat(1);
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
                            if lean_obj_tag(v___x_5397_) == 0 {
                                v_a_5398_ = lean_ctor_get(v___x_5397_, 0);
                                lean_inc(v_a_5398_);
                                lean_dec_ref_known(v___x_5397_, 1);
                                v___x_5399_ = l_Lean_Meta_Simp_getSimprocs___redArg(v___y_5382_);
                                if lean_obj_tag(v___x_5399_) == 0 {
                                    v_a_5400_ = lean_ctor_get(v___x_5399_, 0);
                                    lean_inc(v_a_5400_);
                                    lean_dec_ref_known(v___x_5399_, 1);
                                    v___x_5401_ = lean_st_ref_get(v___y_5382_);
                                    v_env_5402_ = lean_ctor_get(v___x_5401_, 0);
                                    lean_inc_ref(v_env_5402_);
                                    lean_dec(v___x_5401_);
                                    v___x_5403_ = lean_box(0);
                                    v_sz_5404_ = lean_array_size(v_fieldImpls_5376_);
                                    v___x_5405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(v_a_5377_, v_env_5402_, v_instName_5378_, v_a_5398_, v_a_5400_, v_fieldImpls_5376_, v_sz_5404_, v___x_5387_, v___x_5403_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
                                    lean_dec_ref(v_env_5402_);
                                    if lean_obj_tag(v___x_5405_) == 0 {
                                        v_isSharedCheck_5412_ =
                                            (!lean_is_exclusive(v___x_5405_)) as u8;
                                        if v_isSharedCheck_5412_ == 0 {
                                            v_unused_5413_ = lean_ctor_get(v___x_5405_, 0);
                                            lean_dec(v_unused_5413_);
                                            v___x_5407_ = v___x_5405_;
                                            v_isShared_5408_ = v_isSharedCheck_5412_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec(v___x_5405_);
                                            v___x_5407_ = lean_box(0);
                                            v_isShared_5408_ = v_isSharedCheck_5412_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        return v___x_5405_;
                                    }
                                } else {
                                    lean_dec(v_a_5398_);
                                    lean_dec(v_instName_5378_);
                                    v_a_5414_ = lean_ctor_get(v___x_5399_, 0);
                                    v_isSharedCheck_5421_ = (!lean_is_exclusive(v___x_5399_)) as u8;
                                    if v_isSharedCheck_5421_ == 0 {
                                        v___x_5416_ = v___x_5399_;
                                        v_isShared_5417_ = v_isSharedCheck_5421_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5414_);
                                        lean_dec(v___x_5399_);
                                        v___x_5416_ = lean_box(0);
                                        v_isShared_5417_ = v_isSharedCheck_5421_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_instName_5378_);
                                v_a_5422_ = lean_ctor_get(v___x_5397_, 0);
                                v_isSharedCheck_5429_ = (!lean_is_exclusive(v___x_5397_)) as u8;
                                if v_isSharedCheck_5429_ == 0 {
                                    v___x_5424_ = v___x_5397_;
                                    v_isShared_5425_ = v_isSharedCheck_5429_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_5422_);
                                    lean_dec(v___x_5397_);
                                    v___x_5424_ = lean_box(0);
                                    v_isShared_5425_ = v_isSharedCheck_5429_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5389_);
                            lean_dec(v_instName_5378_);
                            v_a_5430_ = lean_ctor_get(v___x_5390_, 0);
                            v_isSharedCheck_5437_ = (!lean_is_exclusive(v___x_5390_)) as u8;
                            if v_isSharedCheck_5437_ == 0 {
                                v___x_5432_ = v___x_5390_;
                                v_isShared_5433_ = v_isSharedCheck_5437_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_5430_);
                                lean_dec(v___x_5390_);
                                v___x_5432_ = lean_box(0);
                                v_isShared_5433_ = v_isSharedCheck_5437_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_instName_5378_);
                        v_a_5438_ = lean_ctor_get(v___x_5388_, 0);
                        v_isSharedCheck_5445_ = (!lean_is_exclusive(v___x_5388_)) as u8;
                        if v_isSharedCheck_5445_ == 0 {
                            v___x_5440_ = v___x_5388_;
                            v_isShared_5441_ = v_isSharedCheck_5445_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5438_);
                            lean_dec(v___x_5388_);
                            v___x_5440_ = lean_box(0);
                            v_isShared_5441_ = v_isSharedCheck_5445_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_instName_5378_);
                    v_a_5446_ = lean_ctor_get(v___x_5384_, 0);
                    v_isSharedCheck_5453_ = (!lean_is_exclusive(v___x_5384_)) as u8;
                    if v_isSharedCheck_5453_ == 0 {
                        v___x_5448_ = v___x_5384_;
                        v_isShared_5449_ = v_isSharedCheck_5453_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5446_);
                        lean_dec(v___x_5384_);
                        v___x_5448_ = lean_box(0);
                        v_isShared_5449_ = v_isSharedCheck_5453_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5408_ == 0 {
                    lean_ctor_set(v___x_5407_, 0, v___x_5403_);
                    v___x_5410_ = v___x_5407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5411_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5411_, 0, v___x_5403_);
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
                    v_reuseFailAlloc_5420_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5420_, 0, v_a_5414_);
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
                    v_reuseFailAlloc_5428_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5428_, 0, v_a_5422_);
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
                    v_reuseFailAlloc_5436_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5436_, 0, v_a_5430_);
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
                    v_reuseFailAlloc_5444_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_a_5438_);
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
                    v_reuseFailAlloc_5452_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_a_5446_);
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
    mut v___x_5454_: *mut LeanObject,
    mut v_thms_5455_: *mut LeanObject,
    mut v_fieldImpls_5456_: *mut LeanObject,
    mut v_a_5457_: *mut LeanObject,
    mut v_instName_5458_: *mut LeanObject,
    mut v___y_5459_: *mut LeanObject,
    mut v___y_5460_: *mut LeanObject,
    mut v___y_5461_: *mut LeanObject,
    mut v___y_5462_: *mut LeanObject,
    mut v___y_5463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5464_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5462_);
    lean_dec_ref(v___y_5461_);
    lean_dec(v___y_5460_);
    lean_dec_ref(v___y_5459_);
    lean_dec_ref(v_a_5457_);
    lean_dec_ref(v_fieldImpls_5456_);
    lean_dec_ref(v_thms_5455_);
    lean_dec_ref(v___x_5454_);
    return v_res_5464_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(
    mut v___y_5465_: *mut LeanObject,
    mut v_isExporting_5466_: u8,
    mut v___x_5467_: *mut LeanObject,
    mut v___y_5468_: *mut LeanObject,
    mut v___x_5469_: *mut LeanObject,
    mut v_a_x3f_5470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5483_: u8 = 0;
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5495_: u8 = 0;
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5502_: u8 = 0;
    let mut v_unused_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5505_: u8 = 0;
    let mut v_unused_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5472_ = lean_st_ref_take(v___y_5465_);
                v_env_5473_ = lean_ctor_get(v___x_5472_, 0);
                v_nextMacroScope_5474_ = lean_ctor_get(v___x_5472_, 1);
                v_ngen_5475_ = lean_ctor_get(v___x_5472_, 2);
                v_auxDeclNGen_5476_ = lean_ctor_get(v___x_5472_, 3);
                v_traceState_5477_ = lean_ctor_get(v___x_5472_, 4);
                v_messages_5478_ = lean_ctor_get(v___x_5472_, 6);
                v_infoState_5479_ = lean_ctor_get(v___x_5472_, 7);
                v_snapshotTasks_5480_ = lean_ctor_get(v___x_5472_, 8);
                v_isSharedCheck_5505_ = (!lean_is_exclusive(v___x_5472_)) as u8;
                if v_isSharedCheck_5505_ == 0 {
                    v_unused_5506_ = lean_ctor_get(v___x_5472_, 5);
                    lean_dec(v_unused_5506_);
                    v___x_5482_ = v___x_5472_;
                    v_isShared_5483_ = v_isSharedCheck_5505_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5480_);
                    lean_inc(v_infoState_5479_);
                    lean_inc(v_messages_5478_);
                    lean_inc(v_traceState_5477_);
                    lean_inc(v_auxDeclNGen_5476_);
                    lean_inc(v_ngen_5475_);
                    lean_inc(v_nextMacroScope_5474_);
                    lean_inc(v_env_5473_);
                    lean_dec(v___x_5472_);
                    v___x_5482_ = lean_box(0);
                    v_isShared_5483_ = v_isSharedCheck_5505_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5484_ = l_Lean_Environment_setExporting(v_env_5473_, v_isExporting_5466_);
                if v_isShared_5483_ == 0 {
                    lean_ctor_set(v___x_5482_, 5, v___x_5467_);
                    lean_ctor_set(v___x_5482_, 0, v___x_5484_);
                    v___x_5486_ = v___x_5482_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5504_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 0, v___x_5484_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 1, v_nextMacroScope_5474_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 2, v_ngen_5475_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 3, v_auxDeclNGen_5476_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 4, v_traceState_5477_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 5, v___x_5467_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 6, v_messages_5478_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 7, v_infoState_5479_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 8, v_snapshotTasks_5480_);
                    v___x_5486_ = v_reuseFailAlloc_5504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5487_ = lean_st_ref_set(v___y_5465_, v___x_5486_);
                v___x_5488_ = lean_st_ref_take(v___y_5468_);
                v_mctx_5489_ = lean_ctor_get(v___x_5488_, 0);
                v_zetaDeltaFVarIds_5490_ = lean_ctor_get(v___x_5488_, 2);
                v_postponed_5491_ = lean_ctor_get(v___x_5488_, 3);
                v_diag_5492_ = lean_ctor_get(v___x_5488_, 4);
                v_isSharedCheck_5502_ = (!lean_is_exclusive(v___x_5488_)) as u8;
                if v_isSharedCheck_5502_ == 0 {
                    v_unused_5503_ = lean_ctor_get(v___x_5488_, 1);
                    lean_dec(v_unused_5503_);
                    v___x_5494_ = v___x_5488_;
                    v_isShared_5495_ = v_isSharedCheck_5502_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_5492_);
                    lean_inc(v_postponed_5491_);
                    lean_inc(v_zetaDeltaFVarIds_5490_);
                    lean_inc(v_mctx_5489_);
                    lean_dec(v___x_5488_);
                    v___x_5494_ = lean_box(0);
                    v_isShared_5495_ = v_isSharedCheck_5502_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5495_ == 0 {
                    lean_ctor_set(v___x_5494_, 1, v___x_5469_);
                    v___x_5497_ = v___x_5494_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5501_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_mctx_5489_);
                    lean_ctor_set(v_reuseFailAlloc_5501_, 1, v___x_5469_);
                    lean_ctor_set(v_reuseFailAlloc_5501_, 2, v_zetaDeltaFVarIds_5490_);
                    lean_ctor_set(v_reuseFailAlloc_5501_, 3, v_postponed_5491_);
                    lean_ctor_set(v_reuseFailAlloc_5501_, 4, v_diag_5492_);
                    v___x_5497_ = v_reuseFailAlloc_5501_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5498_ = lean_st_ref_set(v___y_5468_, v___x_5497_);
                v___x_5499_ = lean_box(0);
                v___x_5500_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5500_, 0, v___x_5499_);
                return v___x_5500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0___boxed(
    mut v___y_5507_: *mut LeanObject,
    mut v_isExporting_5508_: *mut LeanObject,
    mut v___x_5509_: *mut LeanObject,
    mut v___y_5510_: *mut LeanObject,
    mut v___x_5511_: *mut LeanObject,
    mut v_a_x3f_5512_: *mut LeanObject,
    mut v___y_5513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_5514_: u8 = 0;
    let mut v_res_5515_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_5514_ = (lean_unbox(v_isExporting_5508_) as u8);
    v_res_5515_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(v___y_5507_, v_isExporting_boxed_5514_, v___x_5509_, v___y_5510_, v___x_5511_, v_a_x3f_5512_);
    lean_dec(v_a_x3f_5512_);
    lean_dec(v___y_5510_);
    lean_dec(v___y_5507_);
    return v_res_5515_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    v___x_5516_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5516_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    v___x_5517_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0);
    v___x_5518_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5518_, 0, v___x_5517_);
    return v___x_5518_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    v___x_5519_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1);
    v___x_5520_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5520_, 0, v___x_5519_);
    lean_ctor_set(v___x_5520_, 1, v___x_5519_);
    return v___x_5520_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    v___x_5521_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1);
    v___x_5522_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_5522_, 0, v___x_5521_);
    lean_ctor_set(v___x_5522_, 1, v___x_5521_);
    lean_ctor_set(v___x_5522_, 2, v___x_5521_);
    lean_ctor_set(v___x_5522_, 3, v___x_5521_);
    lean_ctor_set(v___x_5522_, 4, v___x_5521_);
    lean_ctor_set(v___x_5522_, 5, v___x_5521_);
    return v___x_5522_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(
    mut v_x_5523_: *mut LeanObject,
    mut v_isExporting_5524_: u8,
    mut v___y_5525_: *mut LeanObject,
    mut v___y_5526_: *mut LeanObject,
    mut v___y_5527_: *mut LeanObject,
    mut v___y_5528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_5532_: u8 = 0;
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5544_: u8 = 0;
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5557_: u8 = 0;
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5566_: u8 = 0;
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5572_: u8 = 0;
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5576_: u8 = 0;
    let mut v_unused_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5579_: u8 = 0;
    let mut v_a_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5585_: u8 = 0;
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5589_: u8 = 0;
    let mut v_unused_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5592_: u8 = 0;
    let mut v_unused_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5595_: u8 = 0;
    let mut v_unused_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5530_ = lean_st_ref_get(v___y_5528_);
                v_env_5531_ = lean_ctor_get(v___x_5530_, 0);
                lean_inc_ref(v_env_5531_);
                lean_dec(v___x_5530_);
                v_isExporting_5532_ = lean_ctor_get_uint8(
                    v_env_5531_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_5531_);
                v___x_5533_ = lean_st_ref_take(v___y_5528_);
                v_env_5534_ = lean_ctor_get(v___x_5533_, 0);
                v_nextMacroScope_5535_ = lean_ctor_get(v___x_5533_, 1);
                v_ngen_5536_ = lean_ctor_get(v___x_5533_, 2);
                v_auxDeclNGen_5537_ = lean_ctor_get(v___x_5533_, 3);
                v_traceState_5538_ = lean_ctor_get(v___x_5533_, 4);
                v_messages_5539_ = lean_ctor_get(v___x_5533_, 6);
                v_infoState_5540_ = lean_ctor_get(v___x_5533_, 7);
                v_snapshotTasks_5541_ = lean_ctor_get(v___x_5533_, 8);
                v_isSharedCheck_5595_ = (!lean_is_exclusive(v___x_5533_)) as u8;
                if v_isSharedCheck_5595_ == 0 {
                    v_unused_5596_ = lean_ctor_get(v___x_5533_, 5);
                    lean_dec(v_unused_5596_);
                    v___x_5543_ = v___x_5533_;
                    v_isShared_5544_ = v_isSharedCheck_5595_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5541_);
                    lean_inc(v_infoState_5540_);
                    lean_inc(v_messages_5539_);
                    lean_inc(v_traceState_5538_);
                    lean_inc(v_auxDeclNGen_5537_);
                    lean_inc(v_ngen_5536_);
                    lean_inc(v_nextMacroScope_5535_);
                    lean_inc(v_env_5534_);
                    lean_dec(v___x_5533_);
                    v___x_5543_ = lean_box(0);
                    v_isShared_5544_ = v_isSharedCheck_5595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5545_ = l_Lean_Environment_setExporting(v_env_5534_, v_isExporting_5524_);
                v___x_5546_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2);
                if v_isShared_5544_ == 0 {
                    lean_ctor_set(v___x_5543_, 5, v___x_5546_);
                    lean_ctor_set(v___x_5543_, 0, v___x_5545_);
                    v___x_5548_ = v___x_5543_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5545_);
                    lean_ctor_set(v_reuseFailAlloc_5594_, 1, v_nextMacroScope_5535_);
                    lean_ctor_set(v_reuseFailAlloc_5594_, 2, v_ngen_5536_);
                    lean_ctor_set(v_reuseFailAlloc_5594_, 3, v_auxDeclNGen_5537_);
                    lean_ctor_set(v_reuseFailAlloc_5594_, 4, v_traceState_5538_);
                    lean_ctor_set(v_reuseFailAlloc_5594_, 5, v___x_5546_);
                    lean_ctor_set(v_reuseFailAlloc_5594_, 6, v_messages_5539_);
                    lean_ctor_set(v_reuseFailAlloc_5594_, 7, v_infoState_5540_);
                    lean_ctor_set(v_reuseFailAlloc_5594_, 8, v_snapshotTasks_5541_);
                    v___x_5548_ = v_reuseFailAlloc_5594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5549_ = lean_st_ref_set(v___y_5528_, v___x_5548_);
                v___x_5550_ = lean_st_ref_take(v___y_5526_);
                v_mctx_5551_ = lean_ctor_get(v___x_5550_, 0);
                v_zetaDeltaFVarIds_5552_ = lean_ctor_get(v___x_5550_, 2);
                v_postponed_5553_ = lean_ctor_get(v___x_5550_, 3);
                v_diag_5554_ = lean_ctor_get(v___x_5550_, 4);
                v_isSharedCheck_5592_ = (!lean_is_exclusive(v___x_5550_)) as u8;
                if v_isSharedCheck_5592_ == 0 {
                    v_unused_5593_ = lean_ctor_get(v___x_5550_, 1);
                    lean_dec(v_unused_5593_);
                    v___x_5556_ = v___x_5550_;
                    v_isShared_5557_ = v_isSharedCheck_5592_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_5554_);
                    lean_inc(v_postponed_5553_);
                    lean_inc(v_zetaDeltaFVarIds_5552_);
                    lean_inc(v_mctx_5551_);
                    lean_dec(v___x_5550_);
                    v___x_5556_ = lean_box(0);
                    v_isShared_5557_ = v_isSharedCheck_5592_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5558_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3);
                if v_isShared_5557_ == 0 {
                    lean_ctor_set(v___x_5556_, 1, v___x_5558_);
                    v___x_5560_ = v___x_5556_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_mctx_5551_);
                    lean_ctor_set(v_reuseFailAlloc_5591_, 1, v___x_5558_);
                    lean_ctor_set(v_reuseFailAlloc_5591_, 2, v_zetaDeltaFVarIds_5552_);
                    lean_ctor_set(v_reuseFailAlloc_5591_, 3, v_postponed_5553_);
                    lean_ctor_set(v_reuseFailAlloc_5591_, 4, v_diag_5554_);
                    v___x_5560_ = v_reuseFailAlloc_5591_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5561_ = lean_st_ref_set(v___y_5526_, v___x_5560_);
                lean_inc(v___y_5528_);
                lean_inc_ref(v___y_5527_);
                lean_inc(v___y_5526_);
                lean_inc_ref(v___y_5525_);
                v_r_5562_ = lean_apply_5(
                    v_x_5523_,
                    v___y_5525_,
                    v___y_5526_,
                    v___y_5527_,
                    v___y_5528_,
                    lean_box(0),
                );
                if lean_obj_tag(v_r_5562_) == 0 {
                    v_a_5563_ = lean_ctor_get(v_r_5562_, 0);
                    v_isSharedCheck_5579_ = (!lean_is_exclusive(v_r_5562_)) as u8;
                    if v_isSharedCheck_5579_ == 0 {
                        v___x_5565_ = v_r_5562_;
                        v_isShared_5566_ = v_isSharedCheck_5579_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5563_);
                        lean_dec(v_r_5562_);
                        v___x_5565_ = lean_box(0);
                        v_isShared_5566_ = v_isSharedCheck_5579_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_5580_ = lean_ctor_get(v_r_5562_, 0);
                    lean_inc(v_a_5580_);
                    lean_dec_ref_known(v_r_5562_, 1);
                    v___x_5581_ = lean_box(0);
                    v___x_5582_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(v___y_5528_, v_isExporting_5532_, v___x_5546_, v___y_5526_, v___x_5558_, v___x_5581_);
                    v_isSharedCheck_5589_ = (!lean_is_exclusive(v___x_5582_)) as u8;
                    if v_isSharedCheck_5589_ == 0 {
                        v_unused_5590_ = lean_ctor_get(v___x_5582_, 0);
                        lean_dec(v_unused_5590_);
                        v___x_5584_ = v___x_5582_;
                        v_isShared_5585_ = v_isSharedCheck_5589_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v___x_5582_);
                        v___x_5584_ = lean_box(0);
                        v_isShared_5585_ = v_isSharedCheck_5589_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_5563_);
                if v_isShared_5566_ == 0 {
                    lean_ctor_set_tag(v___x_5565_, 1);
                    v___x_5568_ = v___x_5565_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5578_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_a_5563_);
                    v___x_5568_ = v_reuseFailAlloc_5578_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5569_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(v___y_5528_, v_isExporting_5532_, v___x_5546_, v___y_5526_, v___x_5558_, v___x_5568_);
                lean_dec_ref(v___x_5568_);
                v_isSharedCheck_5576_ = (!lean_is_exclusive(v___x_5569_)) as u8;
                if v_isSharedCheck_5576_ == 0 {
                    v_unused_5577_ = lean_ctor_get(v___x_5569_, 0);
                    lean_dec(v_unused_5577_);
                    v___x_5571_ = v___x_5569_;
                    v_isShared_5572_ = v_isSharedCheck_5576_;
                    state = 7;
                    continue;
                } else {
                    lean_dec(v___x_5569_);
                    v___x_5571_ = lean_box(0);
                    v_isShared_5572_ = v_isSharedCheck_5576_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5572_ == 0 {
                    lean_ctor_set(v___x_5571_, 0, v_a_5563_);
                    v___x_5574_ = v___x_5571_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5575_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_a_5563_);
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
                    lean_ctor_set_tag(v___x_5584_, 1);
                    lean_ctor_set(v___x_5584_, 0, v_a_5580_);
                    v___x_5587_ = v___x_5584_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5588_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_a_5580_);
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
    mut v_x_5597_: *mut LeanObject,
    mut v_isExporting_5598_: *mut LeanObject,
    mut v___y_5599_: *mut LeanObject,
    mut v___y_5600_: *mut LeanObject,
    mut v___y_5601_: *mut LeanObject,
    mut v___y_5602_: *mut LeanObject,
    mut v___y_5603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_5604_: u8 = 0;
    let mut v_res_5605_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_5604_ = (lean_unbox(v_isExporting_5598_) as u8);
    v_res_5605_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(v_x_5597_, v_isExporting_boxed_5604_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_);
    lean_dec(v___y_5602_);
    lean_dec_ref(v___y_5601_);
    lean_dec(v___y_5600_);
    lean_dec_ref(v___y_5599_);
    return v_res_5605_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(
    mut v_x_5606_: *mut LeanObject,
    mut v_when_5607_: u8,
    mut v___y_5608_: *mut LeanObject,
    mut v___y_5609_: *mut LeanObject,
    mut v___y_5610_: *mut LeanObject,
    mut v___y_5611_: *mut LeanObject,
) -> *mut LeanObject {
    if v_when_5607_ == 0 {
        let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___y_5611_);
        lean_inc_ref(v___y_5610_);
        lean_inc(v___y_5609_);
        lean_inc_ref(v___y_5608_);
        v___x_5613_ = lean_apply_5(
            v_x_5606_,
            v___y_5608_,
            v___y_5609_,
            v___y_5610_,
            v___y_5611_,
            lean_box(0),
        );
        return v___x_5613_;
    } else {
        let mut v___x_5614_: u8 = 0;
        let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
        v___x_5614_ = 0;
        v___x_5615_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(v_x_5606_, v___x_5614_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_);
        return v___x_5615_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg___boxed(
    mut v_x_5616_: *mut LeanObject,
    mut v_when_5617_: *mut LeanObject,
    mut v___y_5618_: *mut LeanObject,
    mut v___y_5619_: *mut LeanObject,
    mut v___y_5620_: *mut LeanObject,
    mut v___y_5621_: *mut LeanObject,
    mut v___y_5622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_5623_: u8 = 0;
    let mut v_res_5624_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_5623_ = (lean_unbox(v_when_5617_) as u8);
    v_res_5624_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(v_x_5616_, v_when_boxed_5623_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
    lean_dec(v___y_5621_);
    lean_dec_ref(v___y_5620_);
    lean_dec(v___y_5619_);
    lean_dec_ref(v___y_5618_);
    return v_res_5624_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize(
    mut v_instName_5625_: *mut LeanObject,
    mut v_a_5626_: *mut LeanObject,
    mut v_a_5627_: *mut LeanObject,
    mut v_a_5628_: *mut LeanObject,
    mut v_a_5629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_privateSpecs_5633_: u8 = 0;
    let mut v_fieldImpls_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thms_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_instName_5625_);
                v___x_5631_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(
                    v_instName_5625_,
                    v_a_5626_,
                    v_a_5627_,
                    v_a_5628_,
                    v_a_5629_,
                );
                if lean_obj_tag(v___x_5631_) == 0 {
                    v_a_5632_ = lean_ctor_get(v___x_5631_, 0);
                    lean_inc(v_a_5632_);
                    lean_dec_ref_known(v___x_5631_, 1);
                    v_privateSpecs_5633_ = lean_ctor_get_uint8(
                        v_a_5632_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_fieldImpls_5634_ = lean_ctor_get(v_a_5632_, 1);
                    lean_inc_ref(v_fieldImpls_5634_);
                    v_thms_5635_ = lean_ctor_get(v_a_5632_, 2);
                    lean_inc_ref(v_thms_5635_);
                    v___x_5636_ =
                        l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsSimpExtension;
                    v___f_5637_ = lean_alloc_closure(l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                    lean_closure_set(v___f_5637_, 0, v___x_5636_);
                    lean_closure_set(v___f_5637_, 1, v_thms_5635_);
                    lean_closure_set(v___f_5637_, 2, v_fieldImpls_5634_);
                    lean_closure_set(v___f_5637_, 3, v_a_5632_);
                    lean_closure_set(v___f_5637_, 4, v_instName_5625_);
                    v___x_5638_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(v___f_5637_, v_privateSpecs_5633_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_);
                    return v___x_5638_;
                } else {
                    lean_dec(v_instName_5625_);
                    v_a_5639_ = lean_ctor_get(v___x_5631_, 0);
                    v_isSharedCheck_5646_ = (!lean_is_exclusive(v___x_5631_)) as u8;
                    if v_isSharedCheck_5646_ == 0 {
                        v___x_5641_ = v___x_5631_;
                        v_isShared_5642_ = v_isSharedCheck_5646_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5639_);
                        lean_dec(v___x_5631_);
                        v___x_5641_ = lean_box(0);
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
                    v_reuseFailAlloc_5645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
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
    mut v_instName_5647_: *mut LeanObject,
    mut v_a_5648_: *mut LeanObject,
    mut v_a_5649_: *mut LeanObject,
    mut v_a_5650_: *mut LeanObject,
    mut v_a_5651_: *mut LeanObject,
    mut v_a_5652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5653_: *mut LeanObject = core::ptr::null_mut();
    v_res_5653_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize(
        v_instName_5647_,
        v_a_5648_,
        v_a_5649_,
        v_a_5650_,
        v_a_5651_,
    );
    lean_dec(v_a_5651_);
    lean_dec_ref(v_a_5650_);
    lean_dec(v_a_5649_);
    lean_dec_ref(v_a_5648_);
    return v_res_5653_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3(
    mut v_00_u03b1_5654_: *mut LeanObject,
    mut v_x_5655_: *mut LeanObject,
    mut v_isExporting_5656_: u8,
    mut v___y_5657_: *mut LeanObject,
    mut v___y_5658_: *mut LeanObject,
    mut v___y_5659_: *mut LeanObject,
    mut v___y_5660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    v___x_5662_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(v_x_5655_, v_isExporting_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_);
    return v___x_5662_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___boxed(
    mut v_00_u03b1_5663_: *mut LeanObject,
    mut v_x_5664_: *mut LeanObject,
    mut v_isExporting_5665_: *mut LeanObject,
    mut v___y_5666_: *mut LeanObject,
    mut v___y_5667_: *mut LeanObject,
    mut v___y_5668_: *mut LeanObject,
    mut v___y_5669_: *mut LeanObject,
    mut v___y_5670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_5671_: u8 = 0;
    let mut v_res_5672_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_5671_ = (lean_unbox(v_isExporting_5665_) as u8);
    v_res_5672_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3(v_00_u03b1_5663_, v_x_5664_, v_isExporting_boxed_5671_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_);
    lean_dec(v___y_5669_);
    lean_dec_ref(v___y_5668_);
    lean_dec(v___y_5667_);
    lean_dec_ref(v___y_5666_);
    return v_res_5672_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3(
    mut v_00_u03b1_5673_: *mut LeanObject,
    mut v_x_5674_: *mut LeanObject,
    mut v_when_5675_: u8,
    mut v___y_5676_: *mut LeanObject,
    mut v___y_5677_: *mut LeanObject,
    mut v___y_5678_: *mut LeanObject,
    mut v___y_5679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    v___x_5681_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(v_x_5674_, v_when_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_);
    return v___x_5681_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___boxed(
    mut v_00_u03b1_5682_: *mut LeanObject,
    mut v_x_5683_: *mut LeanObject,
    mut v_when_5684_: *mut LeanObject,
    mut v___y_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
    mut v___y_5687_: *mut LeanObject,
    mut v___y_5688_: *mut LeanObject,
    mut v___y_5689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_5690_: u8 = 0;
    let mut v_res_5691_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_5690_ = (lean_unbox(v_when_5684_) as u8);
    v_res_5691_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3(v_00_u03b1_5682_, v_x_5683_, v_when_boxed_5690_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_);
    lean_dec(v___y_5688_);
    lean_dec_ref(v___y_5687_);
    lean_dec(v___y_5686_);
    lean_dec_ref(v___y_5685_);
    return v_res_5691_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(
    mut v_instName_5694_: *mut LeanObject,
    mut v_a_5695_: *mut LeanObject,
    mut v_a_5696_: *mut LeanObject,
    mut v_a_5697_: *mut LeanObject,
    mut v_a_5698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_privateSpecs_5705_: u8 = 0;
    let mut v_fieldImpls_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: u8 = 0;
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5720_: u8 = 0;
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5700_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0;
                lean_inc(v_instName_5694_);
                v___x_5701_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(
                    v_instName_5694_,
                    v_a_5695_,
                    v_a_5696_,
                    v_a_5697_,
                    v_a_5698_,
                );
                if lean_obj_tag(v___x_5701_) == 0 {
                    v_a_5702_ = lean_ctor_get(v___x_5701_, 0);
                    lean_inc(v_a_5702_);
                    lean_dec_ref_known(v___x_5701_, 1);
                    v___x_5703_ = lean_st_ref_get(v_a_5698_);
                    v_env_5704_ = lean_ctor_get(v___x_5703_, 0);
                    lean_inc_ref(v_env_5704_);
                    lean_dec(v___x_5703_);
                    v_privateSpecs_5705_ = lean_ctor_get_uint8(
                        v_a_5702_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_fieldImpls_5706_ = lean_ctor_get(v_a_5702_, 1);
                    lean_inc_ref(v_fieldImpls_5706_);
                    lean_dec(v_a_5702_);
                    v___x_5707_ = lean_unsigned_to_nat(0);
                    v___x_5708_ = lean_array_get(v___x_5700_, v_fieldImpls_5706_, v___x_5707_);
                    lean_dec_ref(v_fieldImpls_5706_);
                    v_fst_5709_ = lean_ctor_get(v___x_5708_, 0);
                    lean_inc(v_fst_5709_);
                    lean_dec(v___x_5708_);
                    v___x_5710_ = 1;
                    v___x_5711_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_fst_5709_,
                        v___x_5710_,
                    );
                    v___x_5712_ =
                        l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0;
                    v___x_5713_ = lean_string_append(v___x_5711_, v___x_5712_);
                    lean_inc_n(v_instName_5694_, 2);
                    v___x_5714_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                        v_env_5704_,
                        v_instName_5694_,
                        v_privateSpecs_5705_,
                        v___x_5713_,
                    );
                    lean_dec_ref(v_env_5704_);
                    v___x_5715_ = lean_alloc_closure(
                        l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___boxed
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    lean_closure_set(v___x_5715_, 0, v_instName_5694_);
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
                    lean_dec(v_instName_5694_);
                    v_a_5717_ = lean_ctor_get(v___x_5701_, 0);
                    v_isSharedCheck_5724_ = (!lean_is_exclusive(v___x_5701_)) as u8;
                    if v_isSharedCheck_5724_ == 0 {
                        v___x_5719_ = v___x_5701_;
                        v_isShared_5720_ = v_isSharedCheck_5724_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5717_);
                        lean_dec(v___x_5701_);
                        v___x_5719_ = lean_box(0);
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
                    v_reuseFailAlloc_5723_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_a_5717_);
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
    mut v_instName_5725_: *mut LeanObject,
    mut v_a_5726_: *mut LeanObject,
    mut v_a_5727_: *mut LeanObject,
    mut v_a_5728_: *mut LeanObject,
    mut v_a_5729_: *mut LeanObject,
    mut v_a_5730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5731_: *mut LeanObject = core::ptr::null_mut();
    v_res_5731_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(
        v_instName_5725_,
        v_a_5726_,
        v_a_5727_,
        v_a_5728_,
        v_a_5729_,
    );
    lean_dec(v_a_5729_);
    lean_dec_ref(v_a_5728_);
    lean_dec(v_a_5727_);
    lean_dec_ref(v_a_5726_);
    return v_res_5731_;
}
pub unsafe fn l_Lean_getMethodSpecTheorem___redArg(
    mut v_instName_5732_: *mut LeanObject,
    mut v_op_5733_: *mut LeanObject,
    mut v_a_5734_: *mut LeanObject,
    mut v_a_5735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5745_: u8 = 0;
    let mut v_privateSpecs_5746_: u8 = 0;
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5754_: u8 = 0;
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5761_: u8 = 0;
    let mut v_a_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5765_: u8 = 0;
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5769_: u8 = 0;
    let mut v_isSharedCheck_5770_: u8 = 0;
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5737_ = lean_st_ref_get(v_a_5735_);
                v_env_5738_ = lean_ctor_get(v___x_5737_, 0);
                lean_inc_ref_n(v_env_5738_, 2);
                lean_dec(v___x_5737_);
                v___x_5739_ = l_Lean_instInhabitedMethodSpecsAttrData_default;
                v___x_5740_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
                lean_inc(v_instName_5732_);
                v___x_5741_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
                    v___x_5739_,
                    v___x_5740_,
                    v_env_5738_,
                    v_instName_5732_,
                );
                if lean_obj_tag(v___x_5741_) == 1 {
                    v_val_5742_ = lean_ctor_get(v___x_5741_, 0);
                    v_isSharedCheck_5770_ = (!lean_is_exclusive(v___x_5741_)) as u8;
                    if v_isSharedCheck_5770_ == 0 {
                        v___x_5744_ = v___x_5741_;
                        v_isShared_5745_ = v_isSharedCheck_5770_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5742_);
                        lean_dec(v___x_5741_);
                        v___x_5744_ = lean_box(0);
                        v_isShared_5745_ = v_isSharedCheck_5770_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5741_);
                    lean_dec_ref(v_env_5738_);
                    lean_dec_ref(v_op_5733_);
                    lean_dec(v_instName_5732_);
                    v___x_5771_ = lean_box(0);
                    v___x_5772_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5772_, 0, v___x_5771_);
                    return v___x_5772_;
                }
            }
            1 => {
                v_privateSpecs_5746_ = lean_ctor_get_uint8(
                    v_val_5742_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec(v_val_5742_);
                v___x_5747_ =
                    l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0;
                v___x_5748_ = lean_string_append(v_op_5733_, v___x_5747_);
                v___x_5749_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                    v_env_5738_,
                    v_instName_5732_,
                    v_privateSpecs_5746_,
                    v___x_5748_,
                );
                lean_dec_ref(v_env_5738_);
                v___x_5750_ =
                    l_Lean_realizeGlobalConstNoOverloadCore(v___x_5749_, v_a_5734_, v_a_5735_);
                if lean_obj_tag(v___x_5750_) == 0 {
                    v_a_5751_ = lean_ctor_get(v___x_5750_, 0);
                    v_isSharedCheck_5761_ = (!lean_is_exclusive(v___x_5750_)) as u8;
                    if v_isSharedCheck_5761_ == 0 {
                        v___x_5753_ = v___x_5750_;
                        v_isShared_5754_ = v_isSharedCheck_5761_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5751_);
                        lean_dec(v___x_5750_);
                        v___x_5753_ = lean_box(0);
                        v_isShared_5754_ = v_isSharedCheck_5761_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5744_);
                    v_a_5762_ = lean_ctor_get(v___x_5750_, 0);
                    v_isSharedCheck_5769_ = (!lean_is_exclusive(v___x_5750_)) as u8;
                    if v_isSharedCheck_5769_ == 0 {
                        v___x_5764_ = v___x_5750_;
                        v_isShared_5765_ = v_isSharedCheck_5769_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5762_);
                        lean_dec(v___x_5750_);
                        v___x_5764_ = lean_box(0);
                        v_isShared_5765_ = v_isSharedCheck_5769_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5745_ == 0 {
                    lean_ctor_set(v___x_5744_, 0, v_a_5751_);
                    v___x_5756_ = v___x_5744_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5760_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5760_, 0, v_a_5751_);
                    v___x_5756_ = v_reuseFailAlloc_5760_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5754_ == 0 {
                    lean_ctor_set(v___x_5753_, 0, v___x_5756_);
                    v___x_5758_ = v___x_5753_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5759_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5759_, 0, v___x_5756_);
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
                    v_reuseFailAlloc_5768_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_a_5762_);
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
    mut v_instName_5773_: *mut LeanObject,
    mut v_op_5774_: *mut LeanObject,
    mut v_a_5775_: *mut LeanObject,
    mut v_a_5776_: *mut LeanObject,
    mut v_a_5777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5778_: *mut LeanObject = core::ptr::null_mut();
    v_res_5778_ =
        l_Lean_getMethodSpecTheorem___redArg(v_instName_5773_, v_op_5774_, v_a_5775_, v_a_5776_);
    lean_dec(v_a_5776_);
    lean_dec_ref(v_a_5775_);
    return v_res_5778_;
}
pub unsafe fn l_Lean_getMethodSpecTheorem(
    mut v_instName_5779_: *mut LeanObject,
    mut v_op_5780_: *mut LeanObject,
    mut v_a_5781_: *mut LeanObject,
    mut v_a_5782_: *mut LeanObject,
    mut v_a_5783_: *mut LeanObject,
    mut v_a_5784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    v___x_5786_ =
        l_Lean_getMethodSpecTheorem___redArg(v_instName_5779_, v_op_5780_, v_a_5783_, v_a_5784_);
    return v___x_5786_;
}
pub unsafe fn l_Lean_getMethodSpecTheorem___boxed(
    mut v_instName_5787_: *mut LeanObject,
    mut v_op_5788_: *mut LeanObject,
    mut v_a_5789_: *mut LeanObject,
    mut v_a_5790_: *mut LeanObject,
    mut v_a_5791_: *mut LeanObject,
    mut v_a_5792_: *mut LeanObject,
    mut v_a_5793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5794_: *mut LeanObject = core::ptr::null_mut();
    v_res_5794_ = l_Lean_getMethodSpecTheorem(
        v_instName_5787_,
        v_op_5788_,
        v_a_5789_,
        v_a_5790_,
        v_a_5791_,
        v_a_5792_,
    );
    lean_dec(v_a_5792_);
    lean_dec_ref(v_a_5791_);
    lean_dec(v_a_5790_);
    lean_dec_ref(v_a_5789_);
    return v_res_5794_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0___redArg(
    mut v_op_5795_: *mut LeanObject,
    mut v_instName_5796_: *mut LeanObject,
    mut v___x_5797_: u8,
    mut v___x_5798_: *mut LeanObject,
    mut v_a_5799_: *mut LeanObject,
    mut v___y_5800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5807_: u8 = 0;
    let mut v_env_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: u8 = 0;
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5826_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5802_ = lean_st_ref_get(v___y_5800_);
                v_fst_5803_ = lean_ctor_get(v_a_5799_, 0);
                v_snd_5804_ = lean_ctor_get(v_a_5799_, 1);
                v_isSharedCheck_5826_ = (!lean_is_exclusive(v_a_5799_)) as u8;
                if v_isSharedCheck_5826_ == 0 {
                    v___x_5806_ = v_a_5799_;
                    v_isShared_5807_ = v_isSharedCheck_5826_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_5804_);
                    lean_inc(v_fst_5803_);
                    lean_dec(v_a_5799_);
                    v___x_5806_ = lean_box(0);
                    v_isShared_5807_ = v_isSharedCheck_5826_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_env_5808_ = lean_ctor_get(v___x_5802_, 0);
                lean_inc_ref(v_env_5808_);
                lean_dec(v___x_5802_);
                v___x_5809_ =
                    l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1;
                lean_inc_ref(v_op_5795_);
                v___x_5810_ = lean_string_append(v_op_5795_, v___x_5809_);
                v___x_5811_ = lean_unsigned_to_nat(1);
                v___x_5812_ = lean_nat_add(v_fst_5803_, v___x_5811_);
                lean_inc(v___x_5812_);
                v___x_5813_ = l_Nat_reprFast(v___x_5812_);
                v___x_5814_ = lean_string_append(v___x_5810_, v___x_5813_);
                lean_dec_ref(v___x_5813_);
                lean_inc(v_instName_5796_);
                v___x_5815_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                    v_env_5808_,
                    v_instName_5796_,
                    v___x_5797_,
                    v___x_5814_,
                );
                lean_dec_ref(v_env_5808_);
                v___x_5816_ = l_Lean_Environment_containsOnBranch(v___x_5798_, v___x_5815_);
                if v___x_5816_ == 0 {
                    lean_dec(v___x_5815_);
                    lean_dec(v___x_5812_);
                    lean_dec(v_instName_5796_);
                    lean_dec_ref(v_op_5795_);
                    if v_isShared_5807_ == 0 {
                        v___x_5818_ = v___x_5806_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5820_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5820_, 0, v_fst_5803_);
                        lean_ctor_set(v_reuseFailAlloc_5820_, 1, v_snd_5804_);
                        v___x_5818_ = v_reuseFailAlloc_5820_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_5803_);
                    v___x_5821_ = lean_array_push(v_snd_5804_, v___x_5815_);
                    if v_isShared_5807_ == 0 {
                        lean_ctor_set(v___x_5806_, 1, v___x_5821_);
                        lean_ctor_set(v___x_5806_, 0, v___x_5812_);
                        v___x_5823_ = v___x_5806_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5825_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5825_, 0, v___x_5812_);
                        lean_ctor_set(v_reuseFailAlloc_5825_, 1, v___x_5821_);
                        v___x_5823_ = v_reuseFailAlloc_5825_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5819_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5819_, 0, v___x_5818_);
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
    mut v_op_5827_: *mut LeanObject,
    mut v_instName_5828_: *mut LeanObject,
    mut v___x_5829_: *mut LeanObject,
    mut v___x_5830_: *mut LeanObject,
    mut v_a_5831_: *mut LeanObject,
    mut v___y_5832_: *mut LeanObject,
    mut v___y_5833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2216__boxed_5834_: u8 = 0;
    let mut v_res_5835_: *mut LeanObject = core::ptr::null_mut();
    v___x_2216__boxed_5834_ = (lean_unbox(v___x_5829_) as u8);
    v_res_5835_ = l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0___redArg(v_op_5827_, v_instName_5828_, v___x_2216__boxed_5834_, v___x_5830_, v_a_5831_, v___y_5832_);
    lean_dec(v___y_5832_);
    lean_dec_ref(v___x_5830_);
    return v_res_5835_;
}
pub unsafe fn l_Lean_getMethodSpecTheorems(
    mut v_instName_5841_: *mut LeanObject,
    mut v_op_5842_: *mut LeanObject,
    mut v_a_5843_: *mut LeanObject,
    mut v_a_5844_: *mut LeanObject,
    mut v_a_5845_: *mut LeanObject,
    mut v_a_5846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5856_: u8 = 0;
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_privateSpecs_5859_: u8 = 0;
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5871_: u8 = 0;
    let mut v_snd_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5879_: u8 = 0;
    let mut v_a_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5883_: u8 = 0;
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5887_: u8 = 0;
    let mut v_a_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5891_: u8 = 0;
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5895_: u8 = 0;
    let mut v_isSharedCheck_5896_: u8 = 0;
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5848_ = lean_st_ref_get(v_a_5846_);
                v_env_5849_ = lean_ctor_get(v___x_5848_, 0);
                lean_inc_ref(v_env_5849_);
                lean_dec(v___x_5848_);
                v___x_5850_ = l_Lean_instInhabitedMethodSpecsAttrData_default;
                v___x_5851_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
                lean_inc(v_instName_5841_);
                v___x_5852_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
                    v___x_5850_,
                    v___x_5851_,
                    v_env_5849_,
                    v_instName_5841_,
                );
                if lean_obj_tag(v___x_5852_) == 1 {
                    v_val_5853_ = lean_ctor_get(v___x_5852_, 0);
                    v_isSharedCheck_5896_ = (!lean_is_exclusive(v___x_5852_)) as u8;
                    if v_isSharedCheck_5896_ == 0 {
                        v___x_5855_ = v___x_5852_;
                        v_isShared_5856_ = v_isSharedCheck_5896_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5853_);
                        lean_dec(v___x_5852_);
                        v___x_5855_ = lean_box(0);
                        v_isShared_5856_ = v_isSharedCheck_5896_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5852_);
                    lean_dec_ref(v_op_5842_);
                    lean_dec(v_instName_5841_);
                    v___x_5897_ = lean_box(0);
                    v___x_5898_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5898_, 0, v___x_5897_);
                    return v___x_5898_;
                }
            }
            1 => {
                v___x_5857_ = lean_st_ref_get(v_a_5846_);
                v_env_5858_ = lean_ctor_get(v___x_5857_, 0);
                lean_inc_ref(v_env_5858_);
                lean_dec(v___x_5857_);
                v_privateSpecs_5859_ = lean_ctor_get_uint8(
                    v_val_5853_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec(v_val_5853_);
                v___x_5860_ =
                    l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0;
                lean_inc_ref(v_op_5842_);
                v___x_5861_ = lean_string_append(v_op_5842_, v___x_5860_);
                lean_inc(v_instName_5841_);
                v___x_5862_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(
                    v_env_5858_,
                    v_instName_5841_,
                    v_privateSpecs_5859_,
                    v___x_5861_,
                );
                lean_dec_ref(v_env_5858_);
                v___x_5863_ =
                    l_Lean_realizeGlobalConstNoOverloadCore(v___x_5862_, v_a_5845_, v_a_5846_);
                if lean_obj_tag(v___x_5863_) == 0 {
                    lean_dec_ref_known(v___x_5863_, 1);
                    v___x_5864_ = lean_st_ref_get(v_a_5846_);
                    v_env_5865_ = lean_ctor_get(v___x_5864_, 0);
                    lean_inc_ref(v_env_5865_);
                    lean_dec(v___x_5864_);
                    v___x_5866_ = l_Lean_getMethodSpecTheorems___closed__1;
                    v___x_5867_ = l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0___redArg(v_op_5842_, v_instName_5841_, v_privateSpecs_5859_, v_env_5865_, v___x_5866_, v_a_5846_);
                    lean_dec_ref(v_env_5865_);
                    if lean_obj_tag(v___x_5867_) == 0 {
                        v_a_5868_ = lean_ctor_get(v___x_5867_, 0);
                        v_isSharedCheck_5879_ = (!lean_is_exclusive(v___x_5867_)) as u8;
                        if v_isSharedCheck_5879_ == 0 {
                            v___x_5870_ = v___x_5867_;
                            v_isShared_5871_ = v_isSharedCheck_5879_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5868_);
                            lean_dec(v___x_5867_);
                            v___x_5870_ = lean_box(0);
                            v_isShared_5871_ = v_isSharedCheck_5879_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5855_);
                        v_a_5880_ = lean_ctor_get(v___x_5867_, 0);
                        v_isSharedCheck_5887_ = (!lean_is_exclusive(v___x_5867_)) as u8;
                        if v_isSharedCheck_5887_ == 0 {
                            v___x_5882_ = v___x_5867_;
                            v_isShared_5883_ = v_isSharedCheck_5887_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5880_);
                            lean_dec(v___x_5867_);
                            v___x_5882_ = lean_box(0);
                            v_isShared_5883_ = v_isSharedCheck_5887_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5855_);
                    lean_dec_ref(v_op_5842_);
                    lean_dec(v_instName_5841_);
                    v_a_5888_ = lean_ctor_get(v___x_5863_, 0);
                    v_isSharedCheck_5895_ = (!lean_is_exclusive(v___x_5863_)) as u8;
                    if v_isSharedCheck_5895_ == 0 {
                        v___x_5890_ = v___x_5863_;
                        v_isShared_5891_ = v_isSharedCheck_5895_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_5888_);
                        lean_dec(v___x_5863_);
                        v___x_5890_ = lean_box(0);
                        v_isShared_5891_ = v_isSharedCheck_5895_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_5872_ = lean_ctor_get(v_a_5868_, 1);
                lean_inc(v_snd_5872_);
                lean_dec(v_a_5868_);
                if v_isShared_5856_ == 0 {
                    lean_ctor_set(v___x_5855_, 0, v_snd_5872_);
                    v___x_5874_ = v___x_5855_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5878_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5878_, 0, v_snd_5872_);
                    v___x_5874_ = v_reuseFailAlloc_5878_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5871_ == 0 {
                    lean_ctor_set(v___x_5870_, 0, v___x_5874_);
                    v___x_5876_ = v___x_5870_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5877_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5877_, 0, v___x_5874_);
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
                    v_reuseFailAlloc_5886_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5886_, 0, v_a_5880_);
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
                    v_reuseFailAlloc_5894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5894_, 0, v_a_5888_);
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
    mut v_instName_5899_: *mut LeanObject,
    mut v_op_5900_: *mut LeanObject,
    mut v_a_5901_: *mut LeanObject,
    mut v_a_5902_: *mut LeanObject,
    mut v_a_5903_: *mut LeanObject,
    mut v_a_5904_: *mut LeanObject,
    mut v_a_5905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5906_: *mut LeanObject = core::ptr::null_mut();
    v_res_5906_ = l_Lean_getMethodSpecTheorems(
        v_instName_5899_,
        v_op_5900_,
        v_a_5901_,
        v_a_5902_,
        v_a_5903_,
        v_a_5904_,
    );
    lean_dec(v_a_5904_);
    lean_dec_ref(v_a_5903_);
    lean_dec(v_a_5902_);
    lean_dec_ref(v_a_5901_);
    return v_res_5906_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0(
    mut v_op_5907_: *mut LeanObject,
    mut v_instName_5908_: *mut LeanObject,
    mut v___x_5909_: u8,
    mut v___x_5910_: *mut LeanObject,
    mut v_inst_5911_: *mut LeanObject,
    mut v_a_5912_: *mut LeanObject,
    mut v___y_5913_: *mut LeanObject,
    mut v___y_5914_: *mut LeanObject,
    mut v___y_5915_: *mut LeanObject,
    mut v___y_5916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    v___x_5918_ = l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0___redArg(v_op_5907_, v_instName_5908_, v___x_5909_, v___x_5910_, v_a_5912_, v___y_5916_);
    return v___x_5918_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_getMethodSpecTheorems_spec__0___boxed(
    mut v_op_5919_: *mut LeanObject,
    mut v_instName_5920_: *mut LeanObject,
    mut v___x_5921_: *mut LeanObject,
    mut v___x_5922_: *mut LeanObject,
    mut v_inst_5923_: *mut LeanObject,
    mut v_a_5924_: *mut LeanObject,
    mut v___y_5925_: *mut LeanObject,
    mut v___y_5926_: *mut LeanObject,
    mut v___y_5927_: *mut LeanObject,
    mut v___y_5928_: *mut LeanObject,
    mut v___y_5929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2384__boxed_5930_: u8 = 0;
    let mut v_res_5931_: *mut LeanObject = core::ptr::null_mut();
    v___x_2384__boxed_5930_ = (lean_unbox(v___x_5921_) as u8);
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
    lean_dec(v___y_5928_);
    lean_dec_ref(v___y_5927_);
    lean_dec(v___y_5926_);
    lean_dec_ref(v___y_5925_);
    lean_dec_ref(v___x_5922_);
    return v_res_5931_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(
    mut v_env_5932_: *mut LeanObject,
    mut v_name_5933_: *mut LeanObject,
) -> u8 {
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    v___x_5934_ =
        l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(v_env_5932_, v_name_5933_);
    if lean_obj_tag(v___x_5934_) == 0 {
        let mut v___x_5935_: u8 = 0;
        v___x_5935_ = 0;
        return v___x_5935_;
    } else {
        let mut v___x_5936_: u8 = 0;
        lean_dec_ref_known(v___x_5934_, 1);
        v___x_5936_ = 1;
        return v___x_5936_;
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(
    mut v_env_5937_: *mut LeanObject,
    mut v_name_5938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5939_: u8 = 0;
    let mut v_r_5940_: *mut LeanObject = core::ptr::null_mut();
    v_res_5939_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(v_env_5937_, v_name_5938_);
    v_r_5940_ = lean_box((v_res_5939_) as usize);
    return v_r_5940_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(
    mut v___x_5941_: *mut LeanObject,
    mut v_name_5942_: *mut LeanObject,
    mut v___y_5943_: *mut LeanObject,
    mut v___y_5944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: u8 = 0;
    let mut v___x_5951_: u8 = 0;
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5969_: u8 = 0;
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5975_: u8 = 0;
    let mut v_unused_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5979_: u8 = 0;
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5984_: u8 = 0;
    let mut v_unused_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5989_: u8 = 0;
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5993_: u8 = 0;
    let mut v___x_5994_: u8 = 0;
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5946_ = lean_st_ref_get(v___y_5944_);
                v_env_5947_ = lean_ctor_get(v___x_5946_, 0);
                lean_inc_ref(v_env_5947_);
                lean_dec(v___x_5946_);
                v___x_5948_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(
                    v_env_5947_,
                    v_name_5942_,
                );
                if lean_obj_tag(v___x_5948_) == 1 {
                    v_val_5949_ = lean_ctor_get(v___x_5948_, 0);
                    lean_inc(v_val_5949_);
                    lean_dec_ref_known(v___x_5948_, 1);
                    v___x_5950_ = 0;
                    v___x_5951_ = 1;
                    v___x_5952_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2);
                    v___x_5953_ = lean_unsigned_to_nat(32);
                    v___x_5954_ = lean_mk_empty_array_with_capacity(v___x_5953_);
                    lean_dec_ref(v___x_5954_);
                    v___x_5955_ = lean_unsigned_to_nat(0);
                    v___x_5956_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6);
                    v___x_5957_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7);
                    v___x_5958_ =
                        l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8;
                    v___x_5959_ = lean_box(0);
                    lean_inc(v___x_5941_);
                    v___x_5960_ = lean_alloc_ctor(0, 7, (4) as u32);
                    lean_ctor_set(v___x_5960_, 0, v___x_5952_);
                    lean_ctor_set(v___x_5960_, 1, v___x_5941_);
                    lean_ctor_set(v___x_5960_, 2, v___x_5957_);
                    lean_ctor_set(v___x_5960_, 3, v___x_5958_);
                    lean_ctor_set(v___x_5960_, 4, v___x_5959_);
                    lean_ctor_set(v___x_5960_, 5, v___x_5955_);
                    lean_ctor_set(v___x_5960_, 6, v___x_5959_);
                    lean_ctor_set_uint8(
                        v___x_5960_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v___x_5950_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5960_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                        v___x_5950_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5960_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                        v___x_5950_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5960_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                        v___x_5951_,
                    );
                    v___x_5961_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10);
                    v___x_5962_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11);
                    v___x_5963_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12_once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12);
                    v___x_5964_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_5964_, 0, v___x_5961_);
                    lean_ctor_set(v___x_5964_, 1, v___x_5962_);
                    lean_ctor_set(v___x_5964_, 2, v___x_5941_);
                    lean_ctor_set(v___x_5964_, 3, v___x_5956_);
                    lean_ctor_set(v___x_5964_, 4, v___x_5963_);
                    v___x_5965_ = lean_st_mk_ref(v___x_5964_);
                    v___x_5966_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(
                        v_val_5949_,
                        v___x_5960_,
                        v___x_5965_,
                        v___y_5943_,
                        v___y_5944_,
                    );
                    lean_dec_ref_known(v___x_5960_, 7);
                    if lean_obj_tag(v___x_5966_) == 0 {
                        v_isSharedCheck_5975_ = (!lean_is_exclusive(v___x_5966_)) as u8;
                        if v_isSharedCheck_5975_ == 0 {
                            v_unused_5976_ = lean_ctor_get(v___x_5966_, 0);
                            lean_dec(v_unused_5976_);
                            v___x_5968_ = v___x_5966_;
                            v_isShared_5969_ = v_isSharedCheck_5975_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_5966_);
                            v___x_5968_ = lean_box(0);
                            v_isShared_5969_ = v_isSharedCheck_5975_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5965_);
                        if lean_obj_tag(v___x_5966_) == 0 {
                            v_isSharedCheck_5984_ = (!lean_is_exclusive(v___x_5966_)) as u8;
                            if v_isSharedCheck_5984_ == 0 {
                                v_unused_5985_ = lean_ctor_get(v___x_5966_, 0);
                                lean_dec(v_unused_5985_);
                                v___x_5978_ = v___x_5966_;
                                v_isShared_5979_ = v_isSharedCheck_5984_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_5966_);
                                v___x_5978_ = lean_box(0);
                                v_isShared_5979_ = v_isSharedCheck_5984_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_5986_ = lean_ctor_get(v___x_5966_, 0);
                            v_isSharedCheck_5993_ = (!lean_is_exclusive(v___x_5966_)) as u8;
                            if v_isSharedCheck_5993_ == 0 {
                                v___x_5988_ = v___x_5966_;
                                v_isShared_5989_ = v_isSharedCheck_5993_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_5986_);
                                lean_dec(v___x_5966_);
                                v___x_5988_ = lean_box(0);
                                v_isShared_5989_ = v_isSharedCheck_5993_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_5948_);
                    lean_dec(v___x_5941_);
                    v___x_5994_ = 0;
                    v___x_5995_ = lean_box((v___x_5994_) as usize);
                    v___x_5996_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5996_, 0, v___x_5995_);
                    return v___x_5996_;
                }
            }
            1 => {
                v___x_5970_ = lean_st_ref_get(v___x_5965_);
                lean_dec(v___x_5965_);
                lean_dec(v___x_5970_);
                v___x_5971_ = lean_box((v___x_5951_) as usize);
                if v_isShared_5969_ == 0 {
                    lean_ctor_set(v___x_5968_, 0, v___x_5971_);
                    v___x_5973_ = v___x_5968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5974_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5974_, 0, v___x_5971_);
                    v___x_5973_ = v_reuseFailAlloc_5974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5973_;
            }
            3 => {
                v___x_5980_ = lean_box((v___x_5951_) as usize);
                if v_isShared_5979_ == 0 {
                    lean_ctor_set_tag(v___x_5978_, 0);
                    lean_ctor_set(v___x_5978_, 0, v___x_5980_);
                    v___x_5982_ = v___x_5978_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5983_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5983_, 0, v___x_5980_);
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
                    v_reuseFailAlloc_5992_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5992_, 0, v_a_5986_);
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
    mut v___x_5997_: *mut LeanObject,
    mut v_name_5998_: *mut LeanObject,
    mut v___y_5999_: *mut LeanObject,
    mut v___y_6000_: *mut LeanObject,
    mut v___y_6001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6002_: *mut LeanObject = core::ptr::null_mut();
    v_res_6002_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(v___x_5997_, v_name_5998_, v___y_5999_, v___y_6000_);
    lean_dec(v___y_6000_);
    lean_dec_ref(v___y_5999_);
    return v_res_6002_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut LeanObject = core::ptr::null_mut();
    v___f_6007_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_;
    v___x_6008_ = l_Lean_registerReservedNamePredicate(v___f_6007_);
    if lean_obj_tag(v___x_6008_) == 0 {
        let mut v___f_6009_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_6008_, 1);
        v___f_6009_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_;
        v___x_6010_ = l_Lean_registerReservedNameAction(v___f_6009_);
        return v___x_6010_;
    } else {
        return v___x_6008_;
    }
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(
    mut v_a_6011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6012_: *mut LeanObject = core::ptr::null_mut();
    v_res_6012_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_();
    return v_res_6012_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    v___x_6030_ = lean_unsigned_to_nat(2329740376);
    v___x_6031_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_;
    v___x_6032_ = l_Lean_Name_num___override(v___x_6031_, v___x_6030_);
    return v___x_6032_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut LeanObject = core::ptr::null_mut();
    v___x_6034_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_;
    v___x_6035_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
    v___x_6036_ = l_Lean_Name_str___override(v___x_6035_, v___x_6034_);
    return v___x_6036_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    v___x_6038_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_;
    v___x_6039_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
    v___x_6040_ = l_Lean_Name_str___override(v___x_6039_, v___x_6038_);
    return v___x_6040_;
}
pub unsafe fn _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    v___x_6041_ = lean_unsigned_to_nat(2);
    v___x_6042_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
    v___x_6043_ = l_Lean_Name_num___override(v___x_6042_, v___x_6041_);
    return v___x_6043_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: u8 = 0;
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    v___x_6045_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3;
    v___x_6046_ = 0;
    v___x_6047_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
    v___x_6048_ = l_Lean_registerTraceClass(v___x_6045_, v___x_6046_, v___x_6047_);
    return v___x_6048_;
}
pub unsafe fn l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2____boxed(
    mut v_a_6049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6050_: *mut LeanObject = core::ptr::null_mut();
    v_res_6050_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_();
    return v_res_6050_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_MethodSpecs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Structure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsSimpExtension =
        lean_io_result_get_value(res);
    lean_mark_persistent(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsSimpExtension);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_MethodSpecs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_MethodSpecs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Structure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_MethodSpecs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_MethodSpecs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_MethodSpecs(builtin);
}
