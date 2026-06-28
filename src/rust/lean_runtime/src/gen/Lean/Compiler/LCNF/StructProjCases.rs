// Lean compiler output
// Module: Lean.Compiler.LCNF.StructProjCases
// Imports: Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.MonoTypes
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_replaceRef, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_instInhabitedCode_default__1,
    l_Lean_Compiler_LCNF_instInhabitedLetValue_default,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg, l_Lean_Compiler_LCNF_eraseLetDecl___redArg,
    l_Lean_Compiler_LCNF_eraseParam___redArg,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, l_Lean_Compiler_LCNF_mkParam,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::l_Lean_Compiler_LCNF_Code_inferType;
use crate::r#gen::Lean::Compiler::LCNF::MonoTypes::{
    initialize_Lean_Compiler_LCNF_MonoTypes, l_Lean_Compiler_LCNF_toMonoType,
    runtime_initialize_Lean_Compiler_LCNF_MonoTypes,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::l_Lean_Compiler_LCNF_Pass_mkPerDeclaration;
use crate::r#gen::Lean::Compiler::LCNF::PrettyPrinter::{
    initialize_Lean_Compiler_LCNF_PrettyPrinter,
    runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Compiler_LCNF_toLCNFType;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{l_Lean_instBEqFVarId_beq, l_Lean_instHashableFVarId_hash};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 116, 114, 117, 99, 116, 80, 114, 111, 106, 67, 97, 115, 101, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__1_value: LeanStringObject<60> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 60, m_capacity: 60, m_length: 59, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 116, 114, 117, 99, 116, 80, 114, 111, 106, 67, 97, 115, 101, 115, 46, 109, 107, 70, 105, 101, 108, 100, 80, 97, 114, 97, 109, 115, 70, 111, 114, 67, 116, 111, 114, 84, 121, 112, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__1: u64 = 0;
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6_value:
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
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6_value
) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__8:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__9:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__10:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__11:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__1_value
) as *mut LeanObject;
static mut l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__0_value: LeanStringObject<
    49,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83,
        116, 114, 117, 99, 116, 80, 114, 111, 106, 67, 97, 115, 101, 115, 46, 118, 105, 115, 105,
        116, 76, 101, 116, 86, 97, 108, 117, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__1_value: LeanStringObject<68> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 68,
        m_capacity: 68,
        m_length: 67,
        m_data: [
            95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105,
            108, 101, 114, 46, 76, 67, 78, 70, 46, 66, 97, 115, 105, 99, 46, 48, 46, 76, 101, 97,
            110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 117, 112, 100,
            97, 116, 101, 70, 117, 110, 73, 109, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__0_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            66, 97, 115, 105, 99, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__4_value: LeanStringObject<28> =
    LeanStringObject {
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
            101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 116, 114, 117, 99, 116, 32, 99, 111,
            110, 115, 116, 114, 117, 99, 116, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__3_value: LeanStringObject<45> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 45,
        m_capacity: 45,
        m_length: 44,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            83, 116, 114, 117, 99, 116, 80, 114, 111, 106, 67, 97, 115, 101, 115, 46, 118, 105,
            115, 105, 116, 67, 111, 100, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__6_value: LeanStringObject<59> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 59,
        m_capacity: 59,
        m_length: 58,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 112, 114, 111, 106, 86, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61,
            32, 112, 97, 114, 97, 109, 115, 46, 115, 105, 122, 101, 10, 32, 32, 32, 32, 32, 32, 32,
            32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_StructProjCases_visitDecl___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_StructProjCases_visitCode___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_StructProjCases_visitDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_StructProjCases_visitDecl___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_structProjCases___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_structProjCases___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_structProjCases___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_structProjCases___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_structProjCases___closed__1_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            115, 116, 114, 117, 99, 116, 80, 114, 111, 106, 67, 97, 115, 101, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_structProjCases___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_structProjCases___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_structProjCases___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_structProjCases___closed__1_value)
                as *mut LeanObject,
            10306960168369943990 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_structProjCases___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_structProjCases___closed__2_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_structProjCases___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_structProjCases___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_structProjCases: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_structProjCases___closed__1_value) as *mut LeanObject,8903863121290441208 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [83, 116, 114, 117, 99, 116, 80, 114, 111, 106, 67, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,8597765313508619280 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,533831526727940969 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,16106799734930389804 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,13978681729320241078 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,17893990298072104223 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,17126839337681873342 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,14884656761456744927 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,17544534605622942866 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,5466817986092315232 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,6242447319752813273 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,5736251386791258888 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,((( 268537386 as usize) << 1) | 1) as *mut LeanObject,15974919991714455520 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,12341754598804802807 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,10361774798274923231 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,1381731708675145946 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    v___x_2374_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2374_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    v___x_2375_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_2376_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2376_, 0, v___x_2375_);
    return v___x_2376_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    v___x_2377_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_2378_ = lean_unsigned_to_nat(0);
    v___x_2379_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2379_, 0, v___x_2378_);
    lean_ctor_set(v___x_2379_, 1, v___x_2378_);
    lean_ctor_set(v___x_2379_, 2, v___x_2378_);
    lean_ctor_set(v___x_2379_, 3, v___x_2378_);
    lean_ctor_set(v___x_2379_, 4, v___x_2377_);
    lean_ctor_set(v___x_2379_, 5, v___x_2377_);
    lean_ctor_set(v___x_2379_, 6, v___x_2377_);
    lean_ctor_set(v___x_2379_, 7, v___x_2377_);
    lean_ctor_set(v___x_2379_, 8, v___x_2377_);
    lean_ctor_set(v___x_2379_, 9, v___x_2377_);
    return v___x_2379_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    v___x_2380_ = lean_unsigned_to_nat(32);
    v___x_2381_ = lean_mk_empty_array_with_capacity(v___x_2380_);
    v___x_2382_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2382_, 0, v___x_2381_);
    return v___x_2382_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2383_: usize = 0;
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    v___x_2383_ = 5usize;
    v___x_2384_ = lean_unsigned_to_nat(0);
    v___x_2385_ = lean_unsigned_to_nat(32);
    v___x_2386_ = lean_mk_empty_array_with_capacity(v___x_2385_);
    v___x_2387_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_2388_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2388_, 0, v___x_2387_);
    lean_ctor_set(v___x_2388_, 1, v___x_2386_);
    lean_ctor_set(v___x_2388_, 2, v___x_2384_);
    lean_ctor_set(v___x_2388_, 3, v___x_2384_);
    lean_ctor_set_usize(v___x_2388_, 4, v___x_2383_);
    return v___x_2388_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    v___x_2389_ = lean_box(1);
    v___x_2390_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_2391_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_2392_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2392_, 0, v___x_2391_);
    lean_ctor_set(v___x_2392_, 1, v___x_2390_);
    lean_ctor_set(v___x_2392_, 2, v___x_2389_);
    return v___x_2392_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    v___x_2394_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_2395_ = l_Lean_stringToMessageData(v___x_2394_);
    return v___x_2395_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    v___x_2397_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_2398_ = l_Lean_stringToMessageData(v___x_2397_);
    return v___x_2398_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    v___x_2400_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_2401_ = l_Lean_stringToMessageData(v___x_2400_);
    return v___x_2401_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    v___x_2403_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_2404_ = l_Lean_stringToMessageData(v___x_2403_);
    return v___x_2404_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_2407_ = l_Lean_stringToMessageData(v___x_2406_);
    return v___x_2407_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    v___x_2409_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_2410_ = l_Lean_stringToMessageData(v___x_2409_);
    return v___x_2410_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    v___x_2412_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_2413_ = l_Lean_stringToMessageData(v___x_2412_);
    return v___x_2413_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_2414_: *mut LeanObject,
    mut v_declHint_2415_: *mut LeanObject,
    mut v___y_2416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: u8 = 0;
    let mut v_isExporting_2421_: u8 = 0;
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: u8 = 0;
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2443_: u8 = 0;
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2475_: u8 = 0;
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2418_ = lean_st_ref_get(v___y_2416_);
                v_env_2419_ = lean_ctor_get(v___x_2418_, 0);
                lean_inc_ref(v_env_2419_);
                lean_dec(v___x_2418_);
                v___x_2420_ = l_Lean_Name_isAnonymous(v_declHint_2415_);
                if v___x_2420_ == 0 {
                    v_isExporting_2421_ = lean_ctor_get_uint8(
                        v_env_2419_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2421_ == 0 {
                        lean_dec_ref(v_env_2419_);
                        lean_dec(v_declHint_2415_);
                        v___x_2422_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2422_, 0, v_msg_2414_);
                        return v___x_2422_;
                    } else {
                        lean_inc_ref(v_env_2419_);
                        v___x_2423_ = l_Lean_Environment_setExporting(v_env_2419_, v___x_2420_);
                        lean_inc(v_declHint_2415_);
                        lean_inc_ref(v___x_2423_);
                        v___x_2424_ = l_Lean_Environment_contains(
                            v___x_2423_,
                            v_declHint_2415_,
                            v_isExporting_2421_,
                        );
                        if v___x_2424_ == 0 {
                            lean_dec_ref(v___x_2423_);
                            lean_dec_ref(v_env_2419_);
                            lean_dec(v_declHint_2415_);
                            v___x_2425_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2425_, 0, v_msg_2414_);
                            return v___x_2425_;
                        } else {
                            v___x_2426_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_2427_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_2428_ = l_Lean_Options_empty;
                            v___x_2429_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_2429_, 0, v___x_2423_);
                            lean_ctor_set(v___x_2429_, 1, v___x_2426_);
                            lean_ctor_set(v___x_2429_, 2, v___x_2427_);
                            lean_ctor_set(v___x_2429_, 3, v___x_2428_);
                            lean_inc(v_declHint_2415_);
                            v___x_2430_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2415_, v___x_2420_);
                            v_c_2431_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_2431_, 0, v___x_2429_);
                            lean_ctor_set(v_c_2431_, 1, v___x_2430_);
                            v___x_2432_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2419_,
                                v_declHint_2415_,
                            );
                            if lean_obj_tag(v___x_2432_) == 0 {
                                lean_dec_ref(v_env_2419_);
                                lean_dec(v_declHint_2415_);
                                v___x_2433_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_2434_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2434_, 0, v___x_2433_);
                                lean_ctor_set(v___x_2434_, 1, v_c_2431_);
                                v___x_2435_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_2436_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2436_, 0, v___x_2434_);
                                lean_ctor_set(v___x_2436_, 1, v___x_2435_);
                                v___x_2437_ = l_Lean_MessageData_note(v___x_2436_);
                                v___x_2438_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2438_, 0, v_msg_2414_);
                                lean_ctor_set(v___x_2438_, 1, v___x_2437_);
                                v___x_2439_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2439_, 0, v___x_2438_);
                                return v___x_2439_;
                            } else {
                                v_val_2440_ = lean_ctor_get(v___x_2432_, 0);
                                v_isSharedCheck_2475_ = (!lean_is_exclusive(v___x_2432_)) as u8;
                                if v_isSharedCheck_2475_ == 0 {
                                    v___x_2442_ = v___x_2432_;
                                    v_isShared_2443_ = v_isSharedCheck_2475_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_2440_);
                                    lean_dec(v___x_2432_);
                                    v___x_2442_ = lean_box(0);
                                    v_isShared_2443_ = v_isSharedCheck_2475_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_2419_);
                    lean_dec(v_declHint_2415_);
                    v___x_2476_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2476_, 0, v_msg_2414_);
                    return v___x_2476_;
                }
            }
            1 => {
                v___x_2444_ = lean_box(0);
                v___x_2445_ = l_Lean_Environment_header(v_env_2419_);
                lean_dec_ref(v_env_2419_);
                v___x_2446_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2445_);
                v_mod_2447_ = lean_array_get(v___x_2444_, v___x_2446_, v_val_2440_);
                lean_dec(v_val_2440_);
                lean_dec_ref(v___x_2446_);
                v___x_2448_ = l_Lean_isPrivateName(v_declHint_2415_);
                lean_dec(v_declHint_2415_);
                if v___x_2448_ == 0 {
                    v___x_2449_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_2450_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2450_, 0, v___x_2449_);
                    lean_ctor_set(v___x_2450_, 1, v_c_2431_);
                    v___x_2451_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_2452_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2452_, 0, v___x_2450_);
                    lean_ctor_set(v___x_2452_, 1, v___x_2451_);
                    v___x_2453_ = l_Lean_MessageData_ofName(v_mod_2447_);
                    v___x_2454_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2454_, 0, v___x_2452_);
                    lean_ctor_set(v___x_2454_, 1, v___x_2453_);
                    v___x_2455_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_2456_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2456_, 0, v___x_2454_);
                    lean_ctor_set(v___x_2456_, 1, v___x_2455_);
                    v___x_2457_ = l_Lean_MessageData_note(v___x_2456_);
                    v___x_2458_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2458_, 0, v_msg_2414_);
                    lean_ctor_set(v___x_2458_, 1, v___x_2457_);
                    if v_isShared_2443_ == 0 {
                        lean_ctor_set_tag(v___x_2442_, 0);
                        lean_ctor_set(v___x_2442_, 0, v___x_2458_);
                        v___x_2460_ = v___x_2442_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
                        v___x_2460_ = v_reuseFailAlloc_2461_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2462_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_2463_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2463_, 0, v___x_2462_);
                    lean_ctor_set(v___x_2463_, 1, v_c_2431_);
                    v___x_2464_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_2465_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2465_, 0, v___x_2463_);
                    lean_ctor_set(v___x_2465_, 1, v___x_2464_);
                    v___x_2466_ = l_Lean_MessageData_ofName(v_mod_2447_);
                    v___x_2467_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2467_, 0, v___x_2465_);
                    lean_ctor_set(v___x_2467_, 1, v___x_2466_);
                    v___x_2468_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_2469_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2469_, 0, v___x_2467_);
                    lean_ctor_set(v___x_2469_, 1, v___x_2468_);
                    v___x_2470_ = l_Lean_MessageData_note(v___x_2469_);
                    v___x_2471_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2471_, 0, v_msg_2414_);
                    lean_ctor_set(v___x_2471_, 1, v___x_2470_);
                    if v_isShared_2443_ == 0 {
                        lean_ctor_set_tag(v___x_2442_, 0);
                        lean_ctor_set(v___x_2442_, 0, v___x_2471_);
                        v___x_2473_ = v___x_2442_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
                        v___x_2473_ = v_reuseFailAlloc_2474_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2460_;
            }
            3 => {
                return v___x_2473_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_2477_: *mut LeanObject,
    mut v_declHint_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2481_: *mut LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2477_, v_declHint_2478_, v___y_2479_);
    lean_dec(v___y_2479_);
    return v_res_2481_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_2482_: *mut LeanObject,
    mut v_declHint_2483_: *mut LeanObject,
    mut v___y_2484_: *mut LeanObject,
    mut v___y_2485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2491_: u8 = 0;
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2487_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2482_, v_declHint_2483_, v___y_2485_);
                v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
                v_isSharedCheck_2497_ = (!lean_is_exclusive(v___x_2487_)) as u8;
                if v_isSharedCheck_2497_ == 0 {
                    v___x_2490_ = v___x_2487_;
                    v_isShared_2491_ = v_isSharedCheck_2497_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2488_);
                    lean_dec(v___x_2487_);
                    v___x_2490_ = lean_box(0);
                    v_isShared_2491_ = v_isSharedCheck_2497_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2492_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2493_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2493_, 0, v___x_2492_);
                lean_ctor_set(v___x_2493_, 1, v_a_2488_);
                if v_isShared_2491_ == 0 {
                    lean_ctor_set(v___x_2490_, 0, v___x_2493_);
                    v___x_2495_ = v___x_2490_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
                    v___x_2495_ = v_reuseFailAlloc_2496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_2498_: *mut LeanObject,
    mut v_declHint_2499_: *mut LeanObject,
    mut v___y_2500_: *mut LeanObject,
    mut v___y_2501_: *mut LeanObject,
    mut v___y_2502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2503_: *mut LeanObject = core::ptr::null_mut();
    v_res_2503_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2498_, v_declHint_2499_, v___y_2500_, v___y_2501_);
    lean_dec(v___y_2501_);
    lean_dec_ref(v___y_2500_);
    return v_res_2503_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_2504_: *mut LeanObject,
    mut v___y_2505_: *mut LeanObject,
    mut v___y_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    v___x_2508_ = lean_st_ref_get(v___y_2506_);
    v_env_2509_ = lean_ctor_get(v___x_2508_, 0);
    lean_inc_ref(v_env_2509_);
    lean_dec(v___x_2508_);
    v_options_2510_ = lean_ctor_get(v___y_2505_, 2);
    v___x_2511_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
    v___x_2512_ = lean_unsigned_to_nat(32);
    v___x_2513_ = lean_mk_empty_array_with_capacity(v___x_2512_);
    lean_dec_ref(v___x_2513_);
    v___x_2514_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
    lean_inc_ref(v_options_2510_);
    v___x_2515_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2515_, 0, v_env_2509_);
    lean_ctor_set(v___x_2515_, 1, v___x_2511_);
    lean_ctor_set(v___x_2515_, 2, v___x_2514_);
    lean_ctor_set(v___x_2515_, 3, v_options_2510_);
    v___x_2516_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2516_, 0, v___x_2515_);
    lean_ctor_set(v___x_2516_, 1, v_msgData_2504_);
    v___x_2517_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2517_, 0, v___x_2516_);
    return v___x_2517_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_2518_: *mut LeanObject,
    mut v___y_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
    mut v___y_2521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2522_: *mut LeanObject = core::ptr::null_mut();
    v_res_2522_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2518_, v___y_2519_, v___y_2520_);
    lean_dec(v___y_2520_);
    lean_dec_ref(v___y_2519_);
    return v_res_2522_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_2523_: *mut LeanObject,
    mut v___y_2524_: *mut LeanObject,
    mut v___y_2525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2532_: u8 = 0;
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2527_ = lean_ctor_get(v___y_2524_, 5);
                v___x_2528_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2523_, v___y_2524_, v___y_2525_);
                v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
                v_isSharedCheck_2537_ = (!lean_is_exclusive(v___x_2528_)) as u8;
                if v_isSharedCheck_2537_ == 0 {
                    v___x_2531_ = v___x_2528_;
                    v_isShared_2532_ = v_isSharedCheck_2537_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2529_);
                    lean_dec(v___x_2528_);
                    v___x_2531_ = lean_box(0);
                    v_isShared_2532_ = v_isSharedCheck_2537_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2527_);
                v___x_2533_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2533_, 0, v_ref_2527_);
                lean_ctor_set(v___x_2533_, 1, v_a_2529_);
                if v_isShared_2532_ == 0 {
                    lean_ctor_set_tag(v___x_2531_, 1);
                    lean_ctor_set(v___x_2531_, 0, v___x_2533_);
                    v___x_2535_ = v___x_2531_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
                    v___x_2535_ = v_reuseFailAlloc_2536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2535_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_2538_: *mut LeanObject,
    mut v___y_2539_: *mut LeanObject,
    mut v___y_2540_: *mut LeanObject,
    mut v___y_2541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2542_: *mut LeanObject = core::ptr::null_mut();
    v_res_2542_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2538_, v___y_2539_, v___y_2540_);
    lean_dec(v___y_2540_);
    lean_dec_ref(v___y_2539_);
    return v_res_2542_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_2543_: *mut LeanObject,
    mut v_msg_2544_: *mut LeanObject,
    mut v___y_2545_: *mut LeanObject,
    mut v___y_2546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2560_: u8 = 0;
    let mut v_cancelTk_x3f_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2562_: u8 = 0;
    let mut v_inheritedTraceOptions_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_2548_ = lean_ctor_get(v___y_2545_, 0);
    v_fileMap_2549_ = lean_ctor_get(v___y_2545_, 1);
    v_options_2550_ = lean_ctor_get(v___y_2545_, 2);
    v_currRecDepth_2551_ = lean_ctor_get(v___y_2545_, 3);
    v_maxRecDepth_2552_ = lean_ctor_get(v___y_2545_, 4);
    v_ref_2553_ = lean_ctor_get(v___y_2545_, 5);
    v_currNamespace_2554_ = lean_ctor_get(v___y_2545_, 6);
    v_openDecls_2555_ = lean_ctor_get(v___y_2545_, 7);
    v_initHeartbeats_2556_ = lean_ctor_get(v___y_2545_, 8);
    v_maxHeartbeats_2557_ = lean_ctor_get(v___y_2545_, 9);
    v_quotContext_2558_ = lean_ctor_get(v___y_2545_, 10);
    v_currMacroScope_2559_ = lean_ctor_get(v___y_2545_, 11);
    v_diag_2560_ = lean_ctor_get_uint8(
        v___y_2545_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2561_ = lean_ctor_get(v___y_2545_, 12);
    v_suppressElabErrors_2562_ = lean_ctor_get_uint8(
        v___y_2545_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2563_ = lean_ctor_get(v___y_2545_, 13);
    v_ref_2564_ = l_Lean_replaceRef(v_ref_2543_, v_ref_2553_);
    lean_inc_ref(v_inheritedTraceOptions_2563_);
    lean_inc(v_cancelTk_x3f_2561_);
    lean_inc(v_currMacroScope_2559_);
    lean_inc(v_quotContext_2558_);
    lean_inc(v_maxHeartbeats_2557_);
    lean_inc(v_initHeartbeats_2556_);
    lean_inc(v_openDecls_2555_);
    lean_inc(v_currNamespace_2554_);
    lean_inc(v_maxRecDepth_2552_);
    lean_inc(v_currRecDepth_2551_);
    lean_inc_ref(v_options_2550_);
    lean_inc_ref(v_fileMap_2549_);
    lean_inc_ref(v_fileName_2548_);
    v___x_2565_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_2565_, 0, v_fileName_2548_);
    lean_ctor_set(v___x_2565_, 1, v_fileMap_2549_);
    lean_ctor_set(v___x_2565_, 2, v_options_2550_);
    lean_ctor_set(v___x_2565_, 3, v_currRecDepth_2551_);
    lean_ctor_set(v___x_2565_, 4, v_maxRecDepth_2552_);
    lean_ctor_set(v___x_2565_, 5, v_ref_2564_);
    lean_ctor_set(v___x_2565_, 6, v_currNamespace_2554_);
    lean_ctor_set(v___x_2565_, 7, v_openDecls_2555_);
    lean_ctor_set(v___x_2565_, 8, v_initHeartbeats_2556_);
    lean_ctor_set(v___x_2565_, 9, v_maxHeartbeats_2557_);
    lean_ctor_set(v___x_2565_, 10, v_quotContext_2558_);
    lean_ctor_set(v___x_2565_, 11, v_currMacroScope_2559_);
    lean_ctor_set(v___x_2565_, 12, v_cancelTk_x3f_2561_);
    lean_ctor_set(v___x_2565_, 13, v_inheritedTraceOptions_2563_);
    lean_ctor_set_uint8(
        v___x_2565_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_2560_,
    );
    lean_ctor_set_uint8(
        v___x_2565_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2562_,
    );
    v___x_2566_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2544_, v___x_2565_, v___y_2546_);
    lean_dec_ref_known(v___x_2565_, 14);
    return v___x_2566_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_2567_: *mut LeanObject,
    mut v_msg_2568_: *mut LeanObject,
    mut v___y_2569_: *mut LeanObject,
    mut v___y_2570_: *mut LeanObject,
    mut v___y_2571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2572_: *mut LeanObject = core::ptr::null_mut();
    v_res_2572_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2567_, v_msg_2568_, v___y_2569_, v___y_2570_);
    lean_dec(v___y_2570_);
    lean_dec_ref(v___y_2569_);
    lean_dec(v_ref_2567_);
    return v_res_2572_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_2573_: *mut LeanObject,
    mut v_msg_2574_: *mut LeanObject,
    mut v_declHint_2575_: *mut LeanObject,
    mut v___y_2576_: *mut LeanObject,
    mut v___y_2577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    v___x_2579_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2574_, v_declHint_2575_, v___y_2576_, v___y_2577_);
    v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
    lean_inc(v_a_2580_);
    lean_dec_ref(v___x_2579_);
    v___x_2581_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2573_, v_a_2580_, v___y_2576_, v___y_2577_);
    return v___x_2581_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_2582_: *mut LeanObject,
    mut v_msg_2583_: *mut LeanObject,
    mut v_declHint_2584_: *mut LeanObject,
    mut v___y_2585_: *mut LeanObject,
    mut v___y_2586_: *mut LeanObject,
    mut v___y_2587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2588_: *mut LeanObject = core::ptr::null_mut();
    v_res_2588_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2582_, v_msg_2583_, v_declHint_2584_, v___y_2585_, v___y_2586_);
    lean_dec(v___y_2586_);
    lean_dec_ref(v___y_2585_);
    lean_dec(v_ref_2582_);
    return v_res_2588_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    v___x_2590_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_2591_ = l_Lean_stringToMessageData(v___x_2590_);
    return v___x_2591_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    v___x_2593_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_2594_ = l_Lean_stringToMessageData(v___x_2593_);
    return v___x_2594_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_ref_2595_: *mut LeanObject,
    mut v_constName_2596_: *mut LeanObject,
    mut v___y_2597_: *mut LeanObject,
    mut v___y_2598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: u8 = 0;
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    v___x_2600_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_2601_ = 0;
    lean_inc(v_constName_2596_);
    v___x_2602_ = l_Lean_MessageData_ofConstName(v_constName_2596_, v___x_2601_);
    v___x_2603_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2603_, 0, v___x_2600_);
    lean_ctor_set(v___x_2603_, 1, v___x_2602_);
    v___x_2604_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_2605_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2605_, 0, v___x_2603_);
    lean_ctor_set(v___x_2605_, 1, v___x_2604_);
    v___x_2606_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2595_, v___x_2605_, v_constName_2596_, v___y_2597_, v___y_2598_);
    return v___x_2606_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_2607_: *mut LeanObject,
    mut v_constName_2608_: *mut LeanObject,
    mut v___y_2609_: *mut LeanObject,
    mut v___y_2610_: *mut LeanObject,
    mut v___y_2611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2612_: *mut LeanObject = core::ptr::null_mut();
    v_res_2612_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ref_2607_, v_constName_2608_, v___y_2609_, v___y_2610_);
    lean_dec(v___y_2610_);
    lean_dec_ref(v___y_2609_);
    lean_dec(v_ref_2607_);
    return v_res_2612_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0___redArg(
    mut v_constName_2613_: *mut LeanObject,
    mut v___y_2614_: *mut LeanObject,
    mut v___y_2615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2617_ = lean_ctor_get(v___y_2614_, 5);
    v___x_2618_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ref_2617_, v_constName_2613_, v___y_2614_, v___y_2615_);
    return v___x_2618_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_2619_: *mut LeanObject,
    mut v___y_2620_: *mut LeanObject,
    mut v___y_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2623_: *mut LeanObject = core::ptr::null_mut();
    v_res_2623_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0___redArg(v_constName_2619_, v___y_2620_, v___y_2621_);
    lean_dec(v___y_2621_);
    lean_dec_ref(v___y_2620_);
    return v_res_2623_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0(
    mut v_constName_2624_: *mut LeanObject,
    mut v___y_2625_: *mut LeanObject,
    mut v___y_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: u8 = 0;
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2636_: u8 = 0;
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2628_ = lean_st_ref_get(v___y_2626_);
                v_env_2629_ = lean_ctor_get(v___x_2628_, 0);
                lean_inc_ref(v_env_2629_);
                lean_dec(v___x_2628_);
                v___x_2630_ = 0;
                lean_inc(v_constName_2624_);
                v___x_2631_ =
                    l_Lean_Environment_find_x3f(v_env_2629_, v_constName_2624_, v___x_2630_);
                if lean_obj_tag(v___x_2631_) == 0 {
                    v___x_2632_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0___redArg(v_constName_2624_, v___y_2625_, v___y_2626_);
                    return v___x_2632_;
                } else {
                    lean_dec(v_constName_2624_);
                    v_val_2633_ = lean_ctor_get(v___x_2631_, 0);
                    v_isSharedCheck_2640_ = (!lean_is_exclusive(v___x_2631_)) as u8;
                    if v_isSharedCheck_2640_ == 0 {
                        v___x_2635_ = v___x_2631_;
                        v_isShared_2636_ = v_isSharedCheck_2640_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2633_);
                        lean_dec(v___x_2631_);
                        v___x_2635_ = lean_box(0);
                        v_isShared_2636_ = v_isSharedCheck_2640_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2636_ == 0 {
                    lean_ctor_set_tag(v___x_2635_, 0);
                    v___x_2638_ = v___x_2635_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_val_2633_);
                    v___x_2638_ = v_reuseFailAlloc_2639_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2638_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0___boxed(
    mut v_constName_2641_: *mut LeanObject,
    mut v___y_2642_: *mut LeanObject,
    mut v___y_2643_: *mut LeanObject,
    mut v___y_2644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2645_: *mut LeanObject = core::ptr::null_mut();
    v_res_2645_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0(v_constName_2641_, v___y_2642_, v___y_2643_);
    lean_dec(v___y_2643_);
    lean_dec_ref(v___y_2642_);
    return v_res_2645_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f(
    mut v_typeName_2646_: *mut LeanObject,
    mut v_a_2647_: *mut LeanObject,
    mut v_a_2648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2660_: u8 = 0;
    let mut v_val_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: u8 = 0;
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2672_: u8 = 0;
    let mut v_val_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2680_: u8 = 0;
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2685_: u8 = 0;
    let mut v_a_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2689_: u8 = 0;
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2656_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0(v_typeName_2646_, v_a_2647_, v_a_2648_);
                if lean_obj_tag(v___x_2656_) == 0 {
                    v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
                    v_isSharedCheck_2685_ = (!lean_is_exclusive(v___x_2656_)) as u8;
                    if v_isSharedCheck_2685_ == 0 {
                        v___x_2659_ = v___x_2656_;
                        v_isShared_2660_ = v_isSharedCheck_2685_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2657_);
                        lean_dec(v___x_2656_);
                        v___x_2659_ = lean_box(0);
                        v_isShared_2660_ = v_isSharedCheck_2685_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2686_ = lean_ctor_get(v___x_2656_, 0);
                    v_isSharedCheck_2693_ = (!lean_is_exclusive(v___x_2656_)) as u8;
                    if v_isSharedCheck_2693_ == 0 {
                        v___x_2688_ = v___x_2656_;
                        v_isShared_2689_ = v_isSharedCheck_2693_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2686_);
                        lean_dec(v___x_2656_);
                        v___x_2688_ = lean_box(0);
                        v_isShared_2689_ = v_isSharedCheck_2693_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2651_ = lean_box(0);
                v___x_2652_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2652_, 0, v___x_2651_);
                return v___x_2652_;
            }
            2 => {
                v___x_2654_ = lean_box(0);
                v___x_2655_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2655_, 0, v___x_2654_);
                return v___x_2655_;
            }
            3 => {
                if lean_obj_tag(v_a_2657_) == 5 {
                    v_val_2661_ = lean_ctor_get(v_a_2657_, 0);
                    lean_inc_ref(v_val_2661_);
                    lean_dec_ref_known(v_a_2657_, 1);
                    v_ctors_2662_ = lean_ctor_get(v_val_2661_, 4);
                    lean_inc(v_ctors_2662_);
                    lean_dec_ref(v_val_2661_);
                    if lean_obj_tag(v_ctors_2662_) == 1 {
                        v_tail_2663_ = lean_ctor_get(v_ctors_2662_, 1);
                        if lean_obj_tag(v_tail_2663_) == 0 {
                            v_head_2664_ = lean_ctor_get(v_ctors_2662_, 0);
                            lean_inc(v_head_2664_);
                            lean_dec_ref_known(v_ctors_2662_, 2);
                            v___x_2665_ = lean_st_ref_get(v_a_2648_);
                            v_env_2666_ = lean_ctor_get(v___x_2665_, 0);
                            lean_inc_ref(v_env_2666_);
                            lean_dec(v___x_2665_);
                            v___x_2667_ = 0;
                            v___x_2668_ =
                                l_Lean_Environment_find_x3f(v_env_2666_, v_head_2664_, v___x_2667_);
                            if lean_obj_tag(v___x_2668_) == 1 {
                                v_val_2669_ = lean_ctor_get(v___x_2668_, 0);
                                v_isSharedCheck_2680_ = (!lean_is_exclusive(v___x_2668_)) as u8;
                                if v_isSharedCheck_2680_ == 0 {
                                    v___x_2671_ = v___x_2668_;
                                    v_isShared_2672_ = v_isSharedCheck_2680_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_val_2669_);
                                    lean_dec(v___x_2668_);
                                    v___x_2671_ = lean_box(0);
                                    v_isShared_2672_ = v_isSharedCheck_2680_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_2668_);
                                lean_del_object(v___x_2659_);
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_ctors_2662_, 2);
                            lean_del_object(v___x_2659_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_ctors_2662_);
                        lean_del_object(v___x_2659_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2657_);
                    v___x_2681_ = lean_box(0);
                    if v_isShared_2660_ == 0 {
                        lean_ctor_set(v___x_2659_, 0, v___x_2681_);
                        v___x_2683_ = v___x_2659_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
                        v___x_2683_ = v_reuseFailAlloc_2684_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if lean_obj_tag(v_val_2669_) == 6 {
                    v_val_2673_ = lean_ctor_get(v_val_2669_, 0);
                    lean_inc_ref(v_val_2673_);
                    lean_dec_ref_known(v_val_2669_, 1);
                    if v_isShared_2672_ == 0 {
                        lean_ctor_set(v___x_2671_, 0, v_val_2673_);
                        v___x_2675_ = v___x_2671_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_val_2673_);
                        v___x_2675_ = v_reuseFailAlloc_2679_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2671_);
                    lean_dec(v_val_2669_);
                    lean_del_object(v___x_2659_);
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2660_ == 0 {
                    lean_ctor_set(v___x_2659_, 0, v___x_2675_);
                    v___x_2677_ = v___x_2659_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2675_);
                    v___x_2677_ = v_reuseFailAlloc_2678_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2677_;
            }
            7 => {
                return v___x_2683_;
            }
            8 => {
                if v_isShared_2689_ == 0 {
                    v___x_2691_ = v___x_2688_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
                    v___x_2691_ = v_reuseFailAlloc_2692_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f___boxed(
    mut v_typeName_2694_: *mut LeanObject,
    mut v_a_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2698_: *mut LeanObject = core::ptr::null_mut();
    v_res_2698_ = l_Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f(
        v_typeName_2694_,
        v_a_2695_,
        v_a_2696_,
    );
    lean_dec(v_a_2696_);
    lean_dec_ref(v_a_2695_);
    return v_res_2698_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0(
    mut v_00_u03b1_2699_: *mut LeanObject,
    mut v_constName_2700_: *mut LeanObject,
    mut v___y_2701_: *mut LeanObject,
    mut v___y_2702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    v___x_2704_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0___redArg(v_constName_2700_, v___y_2701_, v___y_2702_);
    return v___x_2704_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_2705_: *mut LeanObject,
    mut v_constName_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
    mut v___y_2708_: *mut LeanObject,
    mut v___y_2709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2710_: *mut LeanObject = core::ptr::null_mut();
    v_res_2710_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0(v_00_u03b1_2705_, v_constName_2706_, v___y_2707_, v___y_2708_);
    lean_dec(v___y_2708_);
    lean_dec_ref(v___y_2707_);
    return v_res_2710_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2711_: *mut LeanObject,
    mut v_ref_2712_: *mut LeanObject,
    mut v_constName_2713_: *mut LeanObject,
    mut v___y_2714_: *mut LeanObject,
    mut v___y_2715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    v___x_2717_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ref_2712_, v_constName_2713_, v___y_2714_, v___y_2715_);
    return v___x_2717_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2718_: *mut LeanObject,
    mut v_ref_2719_: *mut LeanObject,
    mut v_constName_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2724_: *mut LeanObject = core::ptr::null_mut();
    v_res_2724_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2718_, v_ref_2719_, v_constName_2720_, v___y_2721_, v___y_2722_);
    lean_dec(v___y_2722_);
    lean_dec_ref(v___y_2721_);
    lean_dec(v_ref_2719_);
    return v_res_2724_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_2725_: *mut LeanObject,
    mut v_ref_2726_: *mut LeanObject,
    mut v_msg_2727_: *mut LeanObject,
    mut v_declHint_2728_: *mut LeanObject,
    mut v___y_2729_: *mut LeanObject,
    mut v___y_2730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    v___x_2732_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2726_, v_msg_2727_, v_declHint_2728_, v___y_2729_, v___y_2730_);
    return v___x_2732_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_2733_: *mut LeanObject,
    mut v_ref_2734_: *mut LeanObject,
    mut v_msg_2735_: *mut LeanObject,
    mut v_declHint_2736_: *mut LeanObject,
    mut v___y_2737_: *mut LeanObject,
    mut v___y_2738_: *mut LeanObject,
    mut v___y_2739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2740_: *mut LeanObject = core::ptr::null_mut();
    v_res_2740_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2733_, v_ref_2734_, v_msg_2735_, v_declHint_2736_, v___y_2737_, v___y_2738_);
    lean_dec(v___y_2738_);
    lean_dec_ref(v___y_2737_);
    lean_dec(v_ref_2734_);
    return v_res_2740_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_2741_: *mut LeanObject,
    mut v_declHint_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
    mut v___y_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    v___x_2746_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2741_, v_declHint_2742_, v___y_2744_);
    return v___x_2746_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_2747_: *mut LeanObject,
    mut v_declHint_2748_: *mut LeanObject,
    mut v___y_2749_: *mut LeanObject,
    mut v___y_2750_: *mut LeanObject,
    mut v___y_2751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2752_: *mut LeanObject = core::ptr::null_mut();
    v_res_2752_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2747_, v_declHint_2748_, v___y_2749_, v___y_2750_);
    lean_dec(v___y_2750_);
    lean_dec_ref(v___y_2749_);
    return v_res_2752_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_2753_: *mut LeanObject,
    mut v_ref_2754_: *mut LeanObject,
    mut v_msg_2755_: *mut LeanObject,
    mut v___y_2756_: *mut LeanObject,
    mut v___y_2757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    v___x_2759_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2754_, v_msg_2755_, v___y_2756_, v___y_2757_);
    return v___x_2759_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_2760_: *mut LeanObject,
    mut v_ref_2761_: *mut LeanObject,
    mut v_msg_2762_: *mut LeanObject,
    mut v___y_2763_: *mut LeanObject,
    mut v___y_2764_: *mut LeanObject,
    mut v___y_2765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2766_: *mut LeanObject = core::ptr::null_mut();
    v_res_2766_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_2760_, v_ref_2761_, v_msg_2762_, v___y_2763_, v___y_2764_);
    lean_dec(v___y_2764_);
    lean_dec_ref(v___y_2763_);
    lean_dec(v_ref_2761_);
    return v_res_2766_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_2767_: *mut LeanObject,
    mut v_msg_2768_: *mut LeanObject,
    mut v___y_2769_: *mut LeanObject,
    mut v___y_2770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    v___x_2772_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2768_, v___y_2769_, v___y_2770_);
    return v___x_2772_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_2773_: *mut LeanObject,
    mut v_msg_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
    mut v___y_2777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2778_: *mut LeanObject = core::ptr::null_mut();
    v_res_2778_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_2773_, v_msg_2774_, v___y_2775_, v___y_2776_);
    lean_dec(v___y_2776_);
    lean_dec_ref(v___y_2775_);
    return v_res_2778_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    v___x_2779_ = l_instMonadEIO(lean_box(0));
    return v___x_2779_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0(
    mut v_msg_2782_: *mut LeanObject,
    mut v___y_2783_: *mut LeanObject,
    mut v___y_2784_: *mut LeanObject,
    mut v___y_2785_: *mut LeanObject,
    mut v___y_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v_toFunctor_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2800_: u8 = 0;
    let mut v___f_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875__overap_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2821_: u8 = 0;
    let mut v_unused_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut v_unused_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2788_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0);
                v___x_2789_ = l_StateRefT_x27_instMonad___redArg(v___x_2788_);
                v_toApplicative_2790_ = lean_ctor_get(v___x_2789_, 0);
                v_isSharedCheck_2823_ = (!lean_is_exclusive(v___x_2789_)) as u8;
                if v_isSharedCheck_2823_ == 0 {
                    v_unused_2824_ = lean_ctor_get(v___x_2789_, 1);
                    lean_dec(v_unused_2824_);
                    v___x_2792_ = v___x_2789_;
                    v_isShared_2793_ = v_isSharedCheck_2823_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2790_);
                    lean_dec(v___x_2789_);
                    v___x_2792_ = lean_box(0);
                    v_isShared_2793_ = v_isSharedCheck_2823_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2794_ = lean_ctor_get(v_toApplicative_2790_, 0);
                v_toSeq_2795_ = lean_ctor_get(v_toApplicative_2790_, 2);
                v_toSeqLeft_2796_ = lean_ctor_get(v_toApplicative_2790_, 3);
                v_toSeqRight_2797_ = lean_ctor_get(v_toApplicative_2790_, 4);
                v_isSharedCheck_2821_ = (!lean_is_exclusive(v_toApplicative_2790_)) as u8;
                if v_isSharedCheck_2821_ == 0 {
                    v_unused_2822_ = lean_ctor_get(v_toApplicative_2790_, 1);
                    lean_dec(v_unused_2822_);
                    v___x_2799_ = v_toApplicative_2790_;
                    v_isShared_2800_ = v_isSharedCheck_2821_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2797_);
                    lean_inc(v_toSeqLeft_2796_);
                    lean_inc(v_toSeq_2795_);
                    lean_inc(v_toFunctor_2794_);
                    lean_dec(v_toApplicative_2790_);
                    v___x_2799_ = lean_box(0);
                    v_isShared_2800_ = v_isSharedCheck_2821_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2801_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__1;
                v___f_2802_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_2794_);
                v___f_2803_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2803_, 0, v_toFunctor_2794_);
                v___f_2804_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2804_, 0, v_toFunctor_2794_);
                v___x_2805_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2805_, 0, v___f_2803_);
                lean_ctor_set(v___x_2805_, 1, v___f_2804_);
                v___f_2806_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2806_, 0, v_toSeqRight_2797_);
                v___f_2807_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2807_, 0, v_toSeqLeft_2796_);
                v___f_2808_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2808_, 0, v_toSeq_2795_);
                if v_isShared_2800_ == 0 {
                    lean_ctor_set(v___x_2799_, 4, v___f_2806_);
                    lean_ctor_set(v___x_2799_, 3, v___f_2807_);
                    lean_ctor_set(v___x_2799_, 2, v___f_2808_);
                    lean_ctor_set(v___x_2799_, 1, v___f_2801_);
                    lean_ctor_set(v___x_2799_, 0, v___x_2805_);
                    v___x_2810_ = v___x_2799_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2805_);
                    lean_ctor_set(v_reuseFailAlloc_2820_, 1, v___f_2801_);
                    lean_ctor_set(v_reuseFailAlloc_2820_, 2, v___f_2808_);
                    lean_ctor_set(v_reuseFailAlloc_2820_, 3, v___f_2807_);
                    lean_ctor_set(v_reuseFailAlloc_2820_, 4, v___f_2806_);
                    v___x_2810_ = v_reuseFailAlloc_2820_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2793_ == 0 {
                    lean_ctor_set(v___x_2792_, 1, v___f_2802_);
                    lean_ctor_set(v___x_2792_, 0, v___x_2810_);
                    v___x_2812_ = v___x_2792_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2810_);
                    lean_ctor_set(v_reuseFailAlloc_2819_, 1, v___f_2802_);
                    v___x_2812_ = v_reuseFailAlloc_2819_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2813_ = l_StateRefT_x27_instMonad___redArg(v___x_2812_);
                v___x_2814_ = lean_box(0);
                v___x_2815_ = l_instInhabitedOfMonad___redArg(v___x_2813_, v___x_2814_);
                v___f_2816_ = lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2816_, 0, v___x_2815_);
                v___x_3875__overap_2817_ = lean_panic_fn_borrowed(v___f_2816_, v_msg_2782_);
                lean_dec_ref(v___f_2816_);
                lean_inc(v___y_2786_);
                lean_inc_ref(v___y_2785_);
                lean_inc(v___y_2784_);
                lean_inc_ref(v___y_2783_);
                v___x_2818_ = lean_apply_5(
                    v___x_3875__overap_2817_,
                    v___y_2783_,
                    v___y_2784_,
                    v___y_2785_,
                    v___y_2786_,
                    lean_box(0),
                );
                return v___x_2818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___boxed(
    mut v_msg_2825_: *mut LeanObject,
    mut v___y_2826_: *mut LeanObject,
    mut v___y_2827_: *mut LeanObject,
    mut v___y_2828_: *mut LeanObject,
    mut v___y_2829_: *mut LeanObject,
    mut v___y_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2831_: *mut LeanObject = core::ptr::null_mut();
    v_res_2831_ =
        l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0(
            v_msg_2825_,
            v___y_2826_,
            v___y_2827_,
            v___y_2828_,
            v___y_2829_,
        );
    lean_dec(v___y_2829_);
    lean_dec_ref(v___y_2828_);
    lean_dec(v___y_2827_);
    lean_dec_ref(v___y_2826_);
    return v_res_2831_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    v___x_2835_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2;
    v___x_2836_ = lean_unsigned_to_nat(11);
    v___x_2837_ = lean_unsigned_to_nat(39);
    v___x_2838_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__1;
    v___x_2839_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0;
    v___x_2840_ = l_mkPanicMessageWithDecl(
        v___x_2839_,
        v___x_2838_,
        v___x_2837_,
        v___x_2836_,
        v___x_2835_,
    );
    return v___x_2840_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg(
    mut v_upperBound_2841_: *mut LeanObject,
    mut v_a_2842_: *mut LeanObject,
    mut v_b_2843_: *mut LeanObject,
    mut v___y_2844_: *mut LeanObject,
    mut v___y_2845_: *mut LeanObject,
    mut v___y_2846_: *mut LeanObject,
    mut v___y_2847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: u8 = 0;
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2860_: u8 = 0;
    let mut v_binderName_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: u8 = 0;
    let mut v___x_2865_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2875_: u8 = 0;
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2879_: u8 = 0;
    let mut v_isSharedCheck_2880_: u8 = 0;
    let mut v_unused_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2885_: u8 = 0;
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2894_: u8 = 0;
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2898_: u8 = 0;
    let mut v_isSharedCheck_2899_: u8 = 0;
    let mut v_unused_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2854_ = lean_nat_dec_lt(v_a_2842_, v_upperBound_2841_);
                if v___x_2854_ == 0 {
                    lean_dec(v_a_2842_);
                    v___x_2855_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2855_, 0, v_b_2843_);
                    return v___x_2855_;
                } else {
                    v_fst_2856_ = lean_ctor_get(v_b_2843_, 0);
                    lean_inc(v_fst_2856_);
                    if lean_obj_tag(v_fst_2856_) == 7 {
                        v_snd_2857_ = lean_ctor_get(v_b_2843_, 1);
                        v_isSharedCheck_2880_ = (!lean_is_exclusive(v_b_2843_)) as u8;
                        if v_isSharedCheck_2880_ == 0 {
                            v_unused_2881_ = lean_ctor_get(v_b_2843_, 0);
                            lean_dec(v_unused_2881_);
                            v___x_2859_ = v_b_2843_;
                            v_isShared_2860_ = v_isSharedCheck_2880_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_2857_);
                            lean_dec(v_b_2843_);
                            v___x_2859_ = lean_box(0);
                            v_isShared_2860_ = v_isSharedCheck_2880_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_2882_ = lean_ctor_get(v_b_2843_, 1);
                        v_isSharedCheck_2899_ = (!lean_is_exclusive(v_b_2843_)) as u8;
                        if v_isSharedCheck_2899_ == 0 {
                            v_unused_2900_ = lean_ctor_get(v_b_2843_, 0);
                            lean_dec(v_unused_2900_);
                            v___x_2884_ = v_b_2843_;
                            v_isShared_2885_ = v_isSharedCheck_2899_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_snd_2882_);
                            lean_dec(v_b_2843_);
                            v___x_2884_ = lean_box(0);
                            v_isShared_2885_ = v_isSharedCheck_2899_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2851_ = lean_unsigned_to_nat(1);
                v___x_2852_ = lean_nat_add(v_a_2842_, v___x_2851_);
                lean_dec(v_a_2842_);
                v_a_2842_ = v___x_2852_;
                v_b_2843_ = v_a_2850_;
                state = 0;
                continue;
            }
            2 => {
                v_binderName_2861_ = lean_ctor_get(v_fst_2856_, 0);
                lean_inc(v_binderName_2861_);
                v_binderType_2862_ = lean_ctor_get(v_fst_2856_, 1);
                lean_inc_ref(v_binderType_2862_);
                v_body_2863_ = lean_ctor_get(v_fst_2856_, 2);
                lean_inc_ref(v_body_2863_);
                lean_dec_ref_known(v_fst_2856_, 3);
                v___x_2864_ = 0;
                v___x_2865_ = 0;
                v___x_2866_ = l_Lean_Compiler_LCNF_mkParam(
                    v___x_2865_,
                    v_binderName_2861_,
                    v_binderType_2862_,
                    v___x_2864_,
                    v___y_2844_,
                    v___y_2845_,
                    v___y_2846_,
                    v___y_2847_,
                );
                if lean_obj_tag(v___x_2866_) == 0 {
                    v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
                    lean_inc(v_a_2867_);
                    lean_dec_ref_known(v___x_2866_, 1);
                    v___x_2868_ = lean_array_push(v_snd_2857_, v_a_2867_);
                    if v_isShared_2860_ == 0 {
                        lean_ctor_set(v___x_2859_, 1, v___x_2868_);
                        lean_ctor_set(v___x_2859_, 0, v_body_2863_);
                        v___x_2870_ = v___x_2859_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_body_2863_);
                        lean_ctor_set(v_reuseFailAlloc_2871_, 1, v___x_2868_);
                        v___x_2870_ = v_reuseFailAlloc_2871_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_body_2863_);
                    lean_del_object(v___x_2859_);
                    lean_dec(v_snd_2857_);
                    lean_dec(v_a_2842_);
                    v_a_2872_ = lean_ctor_get(v___x_2866_, 0);
                    v_isSharedCheck_2879_ = (!lean_is_exclusive(v___x_2866_)) as u8;
                    if v_isSharedCheck_2879_ == 0 {
                        v___x_2874_ = v___x_2866_;
                        v_isShared_2875_ = v_isSharedCheck_2879_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2872_);
                        lean_dec(v___x_2866_);
                        v___x_2874_ = lean_box(0);
                        v_isShared_2875_ = v_isSharedCheck_2879_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_2850_ = v___x_2870_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_2875_ == 0 {
                    v___x_2877_ = v___x_2874_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
                    v___x_2877_ = v_reuseFailAlloc_2878_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2877_;
            }
            6 => {
                v___x_2886_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__3);
                v___x_2887_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0(v___x_2886_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
                if lean_obj_tag(v___x_2887_) == 0 {
                    lean_dec_ref_known(v___x_2887_, 1);
                    if v_isShared_2885_ == 0 {
                        v___x_2889_ = v___x_2884_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_fst_2856_);
                        lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_snd_2882_);
                        v___x_2889_ = v_reuseFailAlloc_2890_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2884_);
                    lean_dec(v_snd_2882_);
                    lean_dec(v_fst_2856_);
                    lean_dec(v_a_2842_);
                    v_a_2891_ = lean_ctor_get(v___x_2887_, 0);
                    v_isSharedCheck_2898_ = (!lean_is_exclusive(v___x_2887_)) as u8;
                    if v_isSharedCheck_2898_ == 0 {
                        v___x_2893_ = v___x_2887_;
                        v_isShared_2894_ = v_isSharedCheck_2898_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2891_);
                        lean_dec(v___x_2887_);
                        v___x_2893_ = lean_box(0);
                        v_isShared_2894_ = v_isSharedCheck_2898_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                v_a_2850_ = v___x_2889_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_2894_ == 0 {
                    v___x_2896_ = v___x_2893_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
                    v___x_2896_ = v_reuseFailAlloc_2897_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___boxed(
    mut v_upperBound_2901_: *mut LeanObject,
    mut v_a_2902_: *mut LeanObject,
    mut v_b_2903_: *mut LeanObject,
    mut v___y_2904_: *mut LeanObject,
    mut v___y_2905_: *mut LeanObject,
    mut v___y_2906_: *mut LeanObject,
    mut v___y_2907_: *mut LeanObject,
    mut v___y_2908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2909_: *mut LeanObject = core::ptr::null_mut();
    v_res_2909_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg(v_upperBound_2901_, v_a_2902_, v_b_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
    lean_dec(v___y_2907_);
    lean_dec_ref(v___y_2906_);
    lean_dec(v___y_2905_);
    lean_dec_ref(v___y_2904_);
    lean_dec(v_upperBound_2901_);
    return v_res_2909_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    v___x_2910_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2;
    v___x_2911_ = lean_unsigned_to_nat(11);
    v___x_2912_ = lean_unsigned_to_nat(31);
    v___x_2913_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__1;
    v___x_2914_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0;
    v___x_2915_ = l_mkPanicMessageWithDecl(
        v___x_2914_,
        v___x_2913_,
        v___x_2912_,
        v___x_2911_,
        v___x_2910_,
    );
    return v___x_2915_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg(
    mut v_upperBound_2916_: *mut LeanObject,
    mut v_a_2917_: *mut LeanObject,
    mut v_b_2918_: *mut LeanObject,
    mut v___y_2919_: *mut LeanObject,
    mut v___y_2920_: *mut LeanObject,
    mut v___y_2921_: *mut LeanObject,
    mut v___y_2922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: u8 = 0;
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2937_: u8 = 0;
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2941_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2929_ = lean_nat_dec_lt(v_a_2917_, v_upperBound_2916_);
                if v___x_2929_ == 0 {
                    lean_dec(v_a_2917_);
                    v___x_2930_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2930_, 0, v_b_2918_);
                    return v___x_2930_;
                } else {
                    if lean_obj_tag(v_b_2918_) == 7 {
                        v_body_2931_ = lean_ctor_get(v_b_2918_, 2);
                        lean_inc_ref(v_body_2931_);
                        lean_dec_ref_known(v_b_2918_, 3);
                        v_a_2925_ = v_body_2931_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2932_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___closed__0);
                        v___x_2933_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0(v___x_2932_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
                        if lean_obj_tag(v___x_2933_) == 0 {
                            lean_dec_ref_known(v___x_2933_, 1);
                            v_a_2925_ = v_b_2918_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_b_2918_);
                            lean_dec(v_a_2917_);
                            v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
                            v_isSharedCheck_2941_ = (!lean_is_exclusive(v___x_2933_)) as u8;
                            if v_isSharedCheck_2941_ == 0 {
                                v___x_2936_ = v___x_2933_;
                                v_isShared_2937_ = v_isSharedCheck_2941_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_2934_);
                                lean_dec(v___x_2933_);
                                v___x_2936_ = lean_box(0);
                                v_isShared_2937_ = v_isSharedCheck_2941_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2926_ = lean_unsigned_to_nat(1);
                v___x_2927_ = lean_nat_add(v_a_2917_, v___x_2926_);
                lean_dec(v_a_2917_);
                v_a_2917_ = v___x_2927_;
                v_b_2918_ = v_a_2925_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_2937_ == 0 {
                    v___x_2939_ = v___x_2936_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
                    v___x_2939_ = v_reuseFailAlloc_2940_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2939_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg___boxed(
    mut v_upperBound_2942_: *mut LeanObject,
    mut v_a_2943_: *mut LeanObject,
    mut v_b_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
    mut v___y_2946_: *mut LeanObject,
    mut v___y_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2950_: *mut LeanObject = core::ptr::null_mut();
    v_res_2950_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg(v_upperBound_2942_, v_a_2943_, v_b_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
    lean_dec(v___y_2948_);
    lean_dec_ref(v___y_2947_);
    lean_dec(v___y_2946_);
    lean_dec_ref(v___y_2945_);
    lean_dec(v_upperBound_2942_);
    return v_res_2950_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__1()
-> u64 {
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: u64 = 0;
    v___x_2957_ = l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__0;
    v___x_2958_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2957_);
    return v___x_2958_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__2()
-> *mut LeanObject {
    let mut v___x_2959_: u64 = 0;
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    v___x_2959_ = lean_uint64_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__1,
    );
    v___x_2960_ = l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__0;
    v___x_2961_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_2961_, 0, v___x_2960_);
    lean_ctor_set_uint64(
        v___x_2961_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2959_,
    );
    return v___x_2961_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__3()
-> *mut LeanObject {
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    v___x_2962_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2962_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4()
-> *mut LeanObject {
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    v___x_2963_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__3_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__3,
    );
    v___x_2964_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2964_, 0, v___x_2963_);
    return v___x_2964_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__5()
-> *mut LeanObject {
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    v___x_2965_ = lean_box(1);
    v___x_2966_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_2967_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4,
    );
    v___x_2968_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2968_, 0, v___x_2967_);
    lean_ctor_set(v___x_2968_, 1, v___x_2966_);
    lean_ctor_set(v___x_2968_, 2, v___x_2965_);
    return v___x_2968_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__7()
-> *mut LeanObject {
    let mut v___x_2971_: u8 = 0;
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: u8 = 0;
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    v___x_2971_ = 1;
    v___x_2972_ = lean_unsigned_to_nat(0);
    v___x_2973_ = lean_box(0);
    v___x_2974_ = l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__6;
    v___x_2975_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__5_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__5,
    );
    v___x_2976_ = lean_box(1);
    v___x_2977_ = 0;
    v___x_2978_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__2_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__2,
    );
    v___x_2979_ = lean_alloc_ctor(0, 7, (4) as u32);
    lean_ctor_set(v___x_2979_, 0, v___x_2978_);
    lean_ctor_set(v___x_2979_, 1, v___x_2976_);
    lean_ctor_set(v___x_2979_, 2, v___x_2975_);
    lean_ctor_set(v___x_2979_, 3, v___x_2974_);
    lean_ctor_set(v___x_2979_, 4, v___x_2973_);
    lean_ctor_set(v___x_2979_, 5, v___x_2972_);
    lean_ctor_set(v___x_2979_, 6, v___x_2973_);
    lean_ctor_set_uint8(
        v___x_2979_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
        v___x_2977_,
    );
    lean_ctor_set_uint8(
        v___x_2979_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
        v___x_2977_,
    );
    lean_ctor_set_uint8(
        v___x_2979_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
        v___x_2977_,
    );
    lean_ctor_set_uint8(
        v___x_2979_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
        v___x_2971_,
    );
    return v___x_2979_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__8()
-> *mut LeanObject {
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    v___x_2980_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4,
    );
    v___x_2981_ = lean_unsigned_to_nat(0);
    v___x_2982_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2982_, 0, v___x_2981_);
    lean_ctor_set(v___x_2982_, 1, v___x_2981_);
    lean_ctor_set(v___x_2982_, 2, v___x_2981_);
    lean_ctor_set(v___x_2982_, 3, v___x_2981_);
    lean_ctor_set(v___x_2982_, 4, v___x_2980_);
    lean_ctor_set(v___x_2982_, 5, v___x_2980_);
    lean_ctor_set(v___x_2982_, 6, v___x_2980_);
    lean_ctor_set(v___x_2982_, 7, v___x_2980_);
    lean_ctor_set(v___x_2982_, 8, v___x_2980_);
    lean_ctor_set(v___x_2982_, 9, v___x_2980_);
    return v___x_2982_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__9()
-> *mut LeanObject {
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    v___x_2983_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4,
    );
    v___x_2984_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_2984_, 0, v___x_2983_);
    lean_ctor_set(v___x_2984_, 1, v___x_2983_);
    lean_ctor_set(v___x_2984_, 2, v___x_2983_);
    lean_ctor_set(v___x_2984_, 3, v___x_2983_);
    lean_ctor_set(v___x_2984_, 4, v___x_2983_);
    lean_ctor_set(v___x_2984_, 5, v___x_2983_);
    return v___x_2984_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__10()
-> *mut LeanObject {
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    v___x_2985_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__4,
    );
    v___x_2986_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2986_, 0, v___x_2985_);
    lean_ctor_set(v___x_2986_, 1, v___x_2985_);
    lean_ctor_set(v___x_2986_, 2, v___x_2985_);
    lean_ctor_set(v___x_2986_, 3, v___x_2985_);
    lean_ctor_set(v___x_2986_, 4, v___x_2985_);
    return v___x_2986_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__11()
-> *mut LeanObject {
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    v___x_2987_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__10_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__10,
    );
    v___x_2988_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_2989_ = lean_box(1);
    v___x_2990_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__9_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__9,
    );
    v___x_2991_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__8_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__8,
    );
    v___x_2992_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2992_, 0, v___x_2991_);
    lean_ctor_set(v___x_2992_, 1, v___x_2990_);
    lean_ctor_set(v___x_2992_, 2, v___x_2989_);
    lean_ctor_set(v___x_2992_, 3, v___x_2988_);
    lean_ctor_set(v___x_2992_, 4, v___x_2987_);
    return v___x_2992_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType(
    mut v_ctorType_2993_: *mut LeanObject,
    mut v_numParams_2994_: *mut LeanObject,
    mut v_numFields_2995_: *mut LeanObject,
    mut v_a_2996_: *mut LeanObject,
    mut v_a_2997_: *mut LeanObject,
    mut v_a_2998_: *mut LeanObject,
    mut v_a_2999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3014_: u8 = 0;
    let mut v_snd_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3019_: u8 = 0;
    let mut v_a_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3023_: u8 = 0;
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3027_: u8 = 0;
    let mut v_a_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3031_: u8 = 0;
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3035_: u8 = 0;
    let mut v_a_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3039_: u8 = 0;
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3043_: u8 = 0;
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3054_: u8 = 0;
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3044_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__7), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__7_once), _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__7);
                v___x_3045_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__11_once), _init_l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___closed__11);
                v___x_3046_ = lean_st_mk_ref(v___x_3045_);
                v___x_3047_ = l_Lean_Compiler_LCNF_toLCNFType(
                    v_ctorType_2993_,
                    v___x_3044_,
                    v___x_3046_,
                    v_a_2998_,
                    v_a_2999_,
                );
                if lean_obj_tag(v___x_3047_) == 0 {
                    v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
                    lean_inc(v_a_3048_);
                    lean_dec_ref_known(v___x_3047_, 1);
                    v___x_3049_ = lean_st_ref_get(v___x_3046_);
                    lean_dec(v___x_3046_);
                    lean_dec(v___x_3049_);
                    v_a_3002_ = v_a_3048_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_3046_);
                    if lean_obj_tag(v___x_3047_) == 0 {
                        v_a_3050_ = lean_ctor_get(v___x_3047_, 0);
                        lean_inc(v_a_3050_);
                        lean_dec_ref_known(v___x_3047_, 1);
                        v_a_3002_ = v_a_3050_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3051_ = lean_ctor_get(v___x_3047_, 0);
                        v_isSharedCheck_3058_ = (!lean_is_exclusive(v___x_3047_)) as u8;
                        if v_isSharedCheck_3058_ == 0 {
                            v___x_3053_ = v___x_3047_;
                            v_isShared_3054_ = v_isSharedCheck_3058_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3051_);
                            lean_dec(v___x_3047_);
                            v___x_3053_ = lean_box(0);
                            v_isShared_3054_ = v_isSharedCheck_3058_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3003_ = l_Lean_Compiler_LCNF_toMonoType(v_a_3002_, v_a_2998_, v_a_2999_);
                if lean_obj_tag(v___x_3003_) == 0 {
                    v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
                    lean_inc(v_a_3004_);
                    lean_dec_ref_known(v___x_3003_, 1);
                    v___x_3005_ = lean_unsigned_to_nat(0);
                    v___x_3006_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg(v_numParams_2994_, v___x_3005_, v_a_3004_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
                    if lean_obj_tag(v___x_3006_) == 0 {
                        v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
                        lean_inc(v_a_3007_);
                        lean_dec_ref_known(v___x_3006_, 1);
                        v___x_3008_ = lean_mk_empty_array_with_capacity(v_numFields_2995_);
                        v___x_3009_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3009_, 0, v_a_3007_);
                        lean_ctor_set(v___x_3009_, 1, v___x_3008_);
                        v___x_3010_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg(v_numFields_2995_, v___x_3005_, v___x_3009_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
                        if lean_obj_tag(v___x_3010_) == 0 {
                            v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
                            v_isSharedCheck_3019_ = (!lean_is_exclusive(v___x_3010_)) as u8;
                            if v_isSharedCheck_3019_ == 0 {
                                v___x_3013_ = v___x_3010_;
                                v_isShared_3014_ = v_isSharedCheck_3019_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3011_);
                                lean_dec(v___x_3010_);
                                v___x_3013_ = lean_box(0);
                                v_isShared_3014_ = v_isSharedCheck_3019_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_3020_ = lean_ctor_get(v___x_3010_, 0);
                            v_isSharedCheck_3027_ = (!lean_is_exclusive(v___x_3010_)) as u8;
                            if v_isSharedCheck_3027_ == 0 {
                                v___x_3022_ = v___x_3010_;
                                v_isShared_3023_ = v_isSharedCheck_3027_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3020_);
                                lean_dec(v___x_3010_);
                                v___x_3022_ = lean_box(0);
                                v_isShared_3023_ = v_isSharedCheck_3027_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_3028_ = lean_ctor_get(v___x_3006_, 0);
                        v_isSharedCheck_3035_ = (!lean_is_exclusive(v___x_3006_)) as u8;
                        if v_isSharedCheck_3035_ == 0 {
                            v___x_3030_ = v___x_3006_;
                            v_isShared_3031_ = v_isSharedCheck_3035_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3028_);
                            lean_dec(v___x_3006_);
                            v___x_3030_ = lean_box(0);
                            v_isShared_3031_ = v_isSharedCheck_3035_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_a_3036_ = lean_ctor_get(v___x_3003_, 0);
                    v_isSharedCheck_3043_ = (!lean_is_exclusive(v___x_3003_)) as u8;
                    if v_isSharedCheck_3043_ == 0 {
                        v___x_3038_ = v___x_3003_;
                        v_isShared_3039_ = v_isSharedCheck_3043_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3036_);
                        lean_dec(v___x_3003_);
                        v___x_3038_ = lean_box(0);
                        v_isShared_3039_ = v_isSharedCheck_3043_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_3015_ = lean_ctor_get(v_a_3011_, 1);
                lean_inc(v_snd_3015_);
                lean_dec(v_a_3011_);
                if v_isShared_3014_ == 0 {
                    lean_ctor_set(v___x_3013_, 0, v_snd_3015_);
                    v___x_3017_ = v___x_3013_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_snd_3015_);
                    v___x_3017_ = v_reuseFailAlloc_3018_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3017_;
            }
            4 => {
                if v_isShared_3023_ == 0 {
                    v___x_3025_ = v___x_3022_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
                    v___x_3025_ = v_reuseFailAlloc_3026_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3025_;
            }
            6 => {
                if v_isShared_3031_ == 0 {
                    v___x_3033_ = v___x_3030_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
                    v___x_3033_ = v_reuseFailAlloc_3034_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3033_;
            }
            8 => {
                if v_isShared_3039_ == 0 {
                    v___x_3041_ = v___x_3038_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
                    v___x_3041_ = v_reuseFailAlloc_3042_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3041_;
            }
            10 => {
                if v_isShared_3054_ == 0 {
                    v___x_3056_ = v___x_3053_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
                    v___x_3056_ = v_reuseFailAlloc_3057_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType___boxed(
    mut v_ctorType_3059_: *mut LeanObject,
    mut v_numParams_3060_: *mut LeanObject,
    mut v_numFields_3061_: *mut LeanObject,
    mut v_a_3062_: *mut LeanObject,
    mut v_a_3063_: *mut LeanObject,
    mut v_a_3064_: *mut LeanObject,
    mut v_a_3065_: *mut LeanObject,
    mut v_a_3066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3067_: *mut LeanObject = core::ptr::null_mut();
    v_res_3067_ = l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType(
        v_ctorType_3059_,
        v_numParams_3060_,
        v_numFields_3061_,
        v_a_3062_,
        v_a_3063_,
        v_a_3064_,
        v_a_3065_,
    );
    lean_dec(v_a_3065_);
    lean_dec_ref(v_a_3064_);
    lean_dec(v_a_3063_);
    lean_dec_ref(v_a_3062_);
    lean_dec(v_numFields_3061_);
    lean_dec(v_numParams_3060_);
    return v_res_3067_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1(
    mut v_upperBound_3068_: *mut LeanObject,
    mut v_inst_3069_: *mut LeanObject,
    mut v_R_3070_: *mut LeanObject,
    mut v_a_3071_: *mut LeanObject,
    mut v_b_3072_: *mut LeanObject,
    mut v_c_3073_: *mut LeanObject,
    mut v___y_3074_: *mut LeanObject,
    mut v___y_3075_: *mut LeanObject,
    mut v___y_3076_: *mut LeanObject,
    mut v___y_3077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    v___x_3079_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg(v_upperBound_3068_, v_a_3071_, v_b_3072_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
    return v___x_3079_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___boxed(
    mut v_upperBound_3080_: *mut LeanObject,
    mut v_inst_3081_: *mut LeanObject,
    mut v_R_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_b_3084_: *mut LeanObject,
    mut v_c_3085_: *mut LeanObject,
    mut v___y_3086_: *mut LeanObject,
    mut v___y_3087_: *mut LeanObject,
    mut v___y_3088_: *mut LeanObject,
    mut v___y_3089_: *mut LeanObject,
    mut v___y_3090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3091_: *mut LeanObject = core::ptr::null_mut();
    v_res_3091_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1(v_upperBound_3080_, v_inst_3081_, v_R_3082_, v_a_3083_, v_b_3084_, v_c_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
    lean_dec(v___y_3089_);
    lean_dec_ref(v___y_3088_);
    lean_dec(v___y_3087_);
    lean_dec_ref(v___y_3086_);
    lean_dec(v_upperBound_3080_);
    return v_res_3091_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2(
    mut v_upperBound_3092_: *mut LeanObject,
    mut v_inst_3093_: *mut LeanObject,
    mut v_R_3094_: *mut LeanObject,
    mut v_a_3095_: *mut LeanObject,
    mut v_b_3096_: *mut LeanObject,
    mut v_c_3097_: *mut LeanObject,
    mut v___y_3098_: *mut LeanObject,
    mut v___y_3099_: *mut LeanObject,
    mut v___y_3100_: *mut LeanObject,
    mut v___y_3101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    v___x_3103_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___redArg(v_upperBound_3092_, v_a_3095_, v_b_3096_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
    return v___x_3103_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2___boxed(
    mut v_upperBound_3104_: *mut LeanObject,
    mut v_inst_3105_: *mut LeanObject,
    mut v_R_3106_: *mut LeanObject,
    mut v_a_3107_: *mut LeanObject,
    mut v_b_3108_: *mut LeanObject,
    mut v_c_3109_: *mut LeanObject,
    mut v___y_3110_: *mut LeanObject,
    mut v___y_3111_: *mut LeanObject,
    mut v___y_3112_: *mut LeanObject,
    mut v___y_3113_: *mut LeanObject,
    mut v___y_3114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3115_: *mut LeanObject = core::ptr::null_mut();
    v_res_3115_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__2(v_upperBound_3104_, v_inst_3105_, v_R_3106_, v_a_3107_, v_b_3108_, v_c_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
    lean_dec(v___y_3113_);
    lean_dec_ref(v___y_3112_);
    lean_dec(v___y_3111_);
    lean_dec_ref(v___y_3110_);
    lean_dec(v_upperBound_3104_);
    return v_res_3115_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    v___x_3116_ = lean_box(0);
    v___x_3117_ = lean_unsigned_to_nat(16);
    v___x_3118_ = lean_mk_array(v___x_3117_, v___x_3116_);
    return v___x_3118_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    v___x_3119_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__0,
    );
    v___x_3120_ = lean_unsigned_to_nat(0);
    v___x_3121_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3121_, 0, v___x_3120_);
    lean_ctor_set(v___x_3121_, 1, v___x_3119_);
    return v___x_3121_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    v___x_3122_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__1,
    );
    v___x_3123_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3123_, 0, v___x_3122_);
    lean_ctor_set(v___x_3123_, 1, v___x_3122_);
    return v___x_3123_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg(
    mut v_x_3124_: *mut LeanObject,
    mut v_a_3125_: *mut LeanObject,
    mut v_a_3126_: *mut LeanObject,
    mut v_a_3127_: *mut LeanObject,
    mut v_a_3128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3136_: u8 = 0;
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3130_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___closed__2,
                );
                v___x_3131_ = lean_st_mk_ref(v___x_3130_);
                lean_inc(v_a_3128_);
                lean_inc_ref(v_a_3127_);
                lean_inc(v_a_3126_);
                lean_inc_ref(v_a_3125_);
                lean_inc(v___x_3131_);
                v___x_3132_ = lean_apply_6(
                    v_x_3124_,
                    v___x_3131_,
                    v_a_3125_,
                    v_a_3126_,
                    v_a_3127_,
                    v_a_3128_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3132_) == 0 {
                    v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
                    v_isSharedCheck_3141_ = (!lean_is_exclusive(v___x_3132_)) as u8;
                    if v_isSharedCheck_3141_ == 0 {
                        v___x_3135_ = v___x_3132_;
                        v_isShared_3136_ = v_isSharedCheck_3141_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3133_);
                        lean_dec(v___x_3132_);
                        v___x_3135_ = lean_box(0);
                        v_isShared_3136_ = v_isSharedCheck_3141_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3131_);
                    return v___x_3132_;
                }
            }
            1 => {
                v___x_3137_ = lean_st_ref_get(v___x_3131_);
                lean_dec(v___x_3131_);
                lean_dec(v___x_3137_);
                if v_isShared_3136_ == 0 {
                    v___x_3139_ = v___x_3135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3133_);
                    v___x_3139_ = v_reuseFailAlloc_3140_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3139_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg___boxed(
    mut v_x_3142_: *mut LeanObject,
    mut v_a_3143_: *mut LeanObject,
    mut v_a_3144_: *mut LeanObject,
    mut v_a_3145_: *mut LeanObject,
    mut v_a_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3148_: *mut LeanObject = core::ptr::null_mut();
    v_res_3148_ = l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg(
        v_x_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_,
    );
    lean_dec(v_a_3146_);
    lean_dec_ref(v_a_3145_);
    lean_dec(v_a_3144_);
    lean_dec_ref(v_a_3143_);
    return v_res_3148_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_M_run(
    mut v_00_u03b1_3149_: *mut LeanObject,
    mut v_x_3150_: *mut LeanObject,
    mut v_a_3151_: *mut LeanObject,
    mut v_a_3152_: *mut LeanObject,
    mut v_a_3153_: *mut LeanObject,
    mut v_a_3154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    v___x_3156_ = l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg(
        v_x_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_,
    );
    return v___x_3156_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_M_run___boxed(
    mut v_00_u03b1_3157_: *mut LeanObject,
    mut v_x_3158_: *mut LeanObject,
    mut v_a_3159_: *mut LeanObject,
    mut v_a_3160_: *mut LeanObject,
    mut v_a_3161_: *mut LeanObject,
    mut v_a_3162_: *mut LeanObject,
    mut v_a_3163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3164_: *mut LeanObject = core::ptr::null_mut();
    v_res_3164_ = l_Lean_Compiler_LCNF_StructProjCases_M_run(
        v_00_u03b1_3157_,
        v_x_3158_,
        v_a_3159_,
        v_a_3160_,
        v_a_3161_,
        v_a_3162_,
    );
    lean_dec(v_a_3162_);
    lean_dec_ref(v_a_3161_);
    lean_dec(v_a_3160_);
    lean_dec_ref(v_a_3159_);
    return v_res_3164_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___redArg(
    mut v_a_3165_: *mut LeanObject,
    mut v_x_3166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: u8 = 0;
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3166_) == 0 {
                    v___x_3167_ = lean_box(0);
                    return v___x_3167_;
                } else {
                    v_key_3168_ = lean_ctor_get(v_x_3166_, 0);
                    v_value_3169_ = lean_ctor_get(v_x_3166_, 1);
                    v_tail_3170_ = lean_ctor_get(v_x_3166_, 2);
                    v___x_3171_ = l_Lean_instBEqFVarId_beq(v_key_3168_, v_a_3165_);
                    if v___x_3171_ == 0 {
                        v_x_3166_ = v_tail_3170_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_3169_);
                        v___x_3173_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3173_, 0, v_value_3169_);
                        return v___x_3173_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___redArg___boxed(
    mut v_a_3174_: *mut LeanObject,
    mut v_x_3175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3176_: *mut LeanObject = core::ptr::null_mut();
    v_res_3176_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___redArg(v_a_3174_, v_x_3175_);
    lean_dec(v_x_3175_);
    lean_dec(v_a_3174_);
    return v_res_3176_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(
    mut v_m_3177_: *mut LeanObject,
    mut v_a_3178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: u64 = 0;
    let mut v___x_3182_: u64 = 0;
    let mut v___x_3183_: u64 = 0;
    let mut v_fold_3184_: u64 = 0;
    let mut v___x_3185_: u64 = 0;
    let mut v___x_3186_: u64 = 0;
    let mut v___x_3187_: u64 = 0;
    let mut v___x_3188_: usize = 0;
    let mut v___x_3189_: usize = 0;
    let mut v___x_3190_: usize = 0;
    let mut v___x_3191_: usize = 0;
    let mut v___x_3192_: usize = 0;
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_3179_ = lean_ctor_get(v_m_3177_, 1);
    v___x_3180_ = lean_array_get_size(v_buckets_3179_);
    v___x_3181_ = l_Lean_instHashableFVarId_hash(v_a_3178_);
    v___x_3182_ = 32u64;
    v___x_3183_ = lean_uint64_shift_right(v___x_3181_, v___x_3182_);
    v_fold_3184_ = lean_uint64_xor(v___x_3181_, v___x_3183_);
    v___x_3185_ = 16u64;
    v___x_3186_ = lean_uint64_shift_right(v_fold_3184_, v___x_3185_);
    v___x_3187_ = lean_uint64_xor(v_fold_3184_, v___x_3186_);
    v___x_3188_ = lean_uint64_to_usize(v___x_3187_);
    v___x_3189_ = lean_usize_of_nat(v___x_3180_);
    v___x_3190_ = 1usize;
    v___x_3191_ = lean_usize_sub(v___x_3189_, v___x_3190_);
    v___x_3192_ = lean_usize_land(v___x_3188_, v___x_3191_);
    v___x_3193_ = lean_array_uget_borrowed(v_buckets_3179_, v___x_3192_);
    v___x_3194_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___redArg(v_a_3178_, v___x_3193_);
    return v___x_3194_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg___boxed(
    mut v_m_3195_: *mut LeanObject,
    mut v_a_3196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3197_: *mut LeanObject = core::ptr::null_mut();
    v_res_3197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(v_m_3195_, v_a_3196_);
    lean_dec(v_a_3196_);
    lean_dec_ref(v_m_3195_);
    return v_res_3197_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(
    mut v_fvarId_3198_: *mut LeanObject,
    mut v_a_3199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarMap_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3208_: u8 = 0;
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3201_ = lean_st_ref_get(v_a_3199_);
                v_fvarMap_3202_ = lean_ctor_get(v___x_3201_, 1);
                lean_inc_ref(v_fvarMap_3202_);
                lean_dec(v___x_3201_);
                v___x_3203_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(v_fvarMap_3202_, v_fvarId_3198_);
                lean_dec_ref(v_fvarMap_3202_);
                if lean_obj_tag(v___x_3203_) == 0 {
                    v___x_3204_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3204_, 0, v_fvarId_3198_);
                    return v___x_3204_;
                } else {
                    lean_dec(v_fvarId_3198_);
                    v_val_3205_ = lean_ctor_get(v___x_3203_, 0);
                    v_isSharedCheck_3212_ = (!lean_is_exclusive(v___x_3203_)) as u8;
                    if v_isSharedCheck_3212_ == 0 {
                        v___x_3207_ = v___x_3203_;
                        v_isShared_3208_ = v_isSharedCheck_3212_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3205_);
                        lean_dec(v___x_3203_);
                        v___x_3207_ = lean_box(0);
                        v_isShared_3208_ = v_isSharedCheck_3212_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3208_ == 0 {
                    lean_ctor_set_tag(v___x_3207_, 0);
                    v___x_3210_ = v___x_3207_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_val_3205_);
                    v___x_3210_ = v_reuseFailAlloc_3211_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg___boxed(
    mut v_fvarId_3213_: *mut LeanObject,
    mut v_a_3214_: *mut LeanObject,
    mut v_a_3215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3216_: *mut LeanObject = core::ptr::null_mut();
    v_res_3216_ =
        l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(v_fvarId_3213_, v_a_3214_);
    lean_dec(v_a_3214_);
    return v_res_3216_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_remapFVar(
    mut v_fvarId_3217_: *mut LeanObject,
    mut v_a_3218_: *mut LeanObject,
    mut v_a_3219_: *mut LeanObject,
    mut v_a_3220_: *mut LeanObject,
    mut v_a_3221_: *mut LeanObject,
    mut v_a_3222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    v___x_3224_ =
        l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(v_fvarId_3217_, v_a_3218_);
    return v___x_3224_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_remapFVar___boxed(
    mut v_fvarId_3225_: *mut LeanObject,
    mut v_a_3226_: *mut LeanObject,
    mut v_a_3227_: *mut LeanObject,
    mut v_a_3228_: *mut LeanObject,
    mut v_a_3229_: *mut LeanObject,
    mut v_a_3230_: *mut LeanObject,
    mut v_a_3231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3232_: *mut LeanObject = core::ptr::null_mut();
    v_res_3232_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar(
        v_fvarId_3225_,
        v_a_3226_,
        v_a_3227_,
        v_a_3228_,
        v_a_3229_,
        v_a_3230_,
    );
    lean_dec(v_a_3230_);
    lean_dec_ref(v_a_3229_);
    lean_dec(v_a_3228_);
    lean_dec_ref(v_a_3227_);
    lean_dec(v_a_3226_);
    return v_res_3232_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0(
    mut v_00_u03b2_3233_: *mut LeanObject,
    mut v_m_3234_: *mut LeanObject,
    mut v_a_3235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    v___x_3236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(v_m_3234_, v_a_3235_);
    return v___x_3236_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___boxed(
    mut v_00_u03b2_3237_: *mut LeanObject,
    mut v_m_3238_: *mut LeanObject,
    mut v_a_3239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3240_: *mut LeanObject = core::ptr::null_mut();
    v_res_3240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0(v_00_u03b2_3237_, v_m_3238_, v_a_3239_);
    lean_dec(v_a_3239_);
    lean_dec_ref(v_m_3238_);
    return v_res_3240_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0(
    mut v_00_u03b2_3241_: *mut LeanObject,
    mut v_a_3242_: *mut LeanObject,
    mut v_x_3243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    v___x_3244_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___redArg(v_a_3242_, v_x_3243_);
    return v___x_3244_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0___boxed(
    mut v_00_u03b2_3245_: *mut LeanObject,
    mut v_a_3246_: *mut LeanObject,
    mut v_x_3247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3248_: *mut LeanObject = core::ptr::null_mut();
    v_res_3248_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0_spec__0(v_00_u03b2_3245_, v_a_3246_, v_x_3247_);
    lean_dec(v_x_3247_);
    lean_dec(v_a_3246_);
    return v_res_3248_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_visitArg___redArg(
    mut v_arg_3249_: *mut LeanObject,
    mut v_a_3250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3257_: u8 = 0;
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3262_: u8 = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_arg_3249_) == 1 {
                    v_fvarId_3252_ = lean_ctor_get(v_arg_3249_, 0);
                    lean_inc(v_fvarId_3252_);
                    v___x_3253_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(
                        v_fvarId_3252_,
                        v_a_3250_,
                    );
                    v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
                    v_isSharedCheck_3262_ = (!lean_is_exclusive(v___x_3253_)) as u8;
                    if v_isSharedCheck_3262_ == 0 {
                        v___x_3256_ = v___x_3253_;
                        v_isShared_3257_ = v_isSharedCheck_3262_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3254_);
                        lean_dec(v___x_3253_);
                        v___x_3256_ = lean_box(0);
                        v_isShared_3257_ = v_isSharedCheck_3262_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3263_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3263_, 0, v_arg_3249_);
                    return v___x_3263_;
                }
            }
            1 => {
                v___x_3258_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(v_arg_3249_, v_a_3254_);
                if v_isShared_3257_ == 0 {
                    lean_ctor_set(v___x_3256_, 0, v___x_3258_);
                    v___x_3260_ = v___x_3256_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
                    v___x_3260_ = v_reuseFailAlloc_3261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_visitArg___redArg___boxed(
    mut v_arg_3264_: *mut LeanObject,
    mut v_a_3265_: *mut LeanObject,
    mut v_a_3266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3267_: *mut LeanObject = core::ptr::null_mut();
    v_res_3267_ = l_Lean_Compiler_LCNF_StructProjCases_visitArg___redArg(v_arg_3264_, v_a_3265_);
    lean_dec(v_a_3265_);
    return v_res_3267_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_visitArg(
    mut v_arg_3268_: *mut LeanObject,
    mut v_a_3269_: *mut LeanObject,
    mut v_a_3270_: *mut LeanObject,
    mut v_a_3271_: *mut LeanObject,
    mut v_a_3272_: *mut LeanObject,
    mut v_a_3273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    v___x_3275_ = l_Lean_Compiler_LCNF_StructProjCases_visitArg___redArg(v_arg_3268_, v_a_3269_);
    return v___x_3275_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_visitArg___boxed(
    mut v_arg_3276_: *mut LeanObject,
    mut v_a_3277_: *mut LeanObject,
    mut v_a_3278_: *mut LeanObject,
    mut v_a_3279_: *mut LeanObject,
    mut v_a_3280_: *mut LeanObject,
    mut v_a_3281_: *mut LeanObject,
    mut v_a_3282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3283_: *mut LeanObject = core::ptr::null_mut();
    v_res_3283_ = l_Lean_Compiler_LCNF_StructProjCases_visitArg(
        v_arg_3276_,
        v_a_3277_,
        v_a_3278_,
        v_a_3279_,
        v_a_3280_,
        v_a_3281_,
    );
    lean_dec(v_a_3281_);
    lean_dec_ref(v_a_3280_);
    lean_dec(v_a_3279_);
    lean_dec_ref(v_a_3278_);
    lean_dec(v_a_3277_);
    return v_res_3283_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    v___x_3286_ = 0;
    v___x_3287_ = l_Lean_Compiler_LCNF_instInhabitedLetValue_default(v___x_3286_);
    return v___x_3287_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0(
    mut v_msg_3288_: *mut LeanObject,
    mut v___y_3289_: *mut LeanObject,
    mut v___y_3290_: *mut LeanObject,
    mut v___y_3291_: *mut LeanObject,
    mut v___y_3292_: *mut LeanObject,
    mut v___y_3293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3300_: u8 = 0;
    let mut v_toFunctor_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3307_: u8 = 0;
    let mut v___f_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3324_: u8 = 0;
    let mut v_toFunctor_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3331_: u8 = 0;
    let mut v___f_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169__overap_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3351_: u8 = 0;
    let mut v_unused_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3353_: u8 = 0;
    let mut v_unused_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3357_: u8 = 0;
    let mut v_unused_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3359_: u8 = 0;
    let mut v_unused_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3295_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0);
                v___x_3296_ = l_StateRefT_x27_instMonad___redArg(v___x_3295_);
                v_toApplicative_3297_ = lean_ctor_get(v___x_3296_, 0);
                v_isSharedCheck_3359_ = (!lean_is_exclusive(v___x_3296_)) as u8;
                if v_isSharedCheck_3359_ == 0 {
                    v_unused_3360_ = lean_ctor_get(v___x_3296_, 1);
                    lean_dec(v_unused_3360_);
                    v___x_3299_ = v___x_3296_;
                    v_isShared_3300_ = v_isSharedCheck_3359_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3297_);
                    lean_dec(v___x_3296_);
                    v___x_3299_ = lean_box(0);
                    v_isShared_3300_ = v_isSharedCheck_3359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3301_ = lean_ctor_get(v_toApplicative_3297_, 0);
                v_toSeq_3302_ = lean_ctor_get(v_toApplicative_3297_, 2);
                v_toSeqLeft_3303_ = lean_ctor_get(v_toApplicative_3297_, 3);
                v_toSeqRight_3304_ = lean_ctor_get(v_toApplicative_3297_, 4);
                v_isSharedCheck_3357_ = (!lean_is_exclusive(v_toApplicative_3297_)) as u8;
                if v_isSharedCheck_3357_ == 0 {
                    v_unused_3358_ = lean_ctor_get(v_toApplicative_3297_, 1);
                    lean_dec(v_unused_3358_);
                    v___x_3306_ = v_toApplicative_3297_;
                    v_isShared_3307_ = v_isSharedCheck_3357_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_3304_);
                    lean_inc(v_toSeqLeft_3303_);
                    lean_inc(v_toSeq_3302_);
                    lean_inc(v_toFunctor_3301_);
                    lean_dec(v_toApplicative_3297_);
                    v___x_3306_ = lean_box(0);
                    v_isShared_3307_ = v_isSharedCheck_3357_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3308_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__1;
                v___f_3309_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_3301_);
                v___f_3310_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3310_, 0, v_toFunctor_3301_);
                v___f_3311_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3311_, 0, v_toFunctor_3301_);
                v___x_3312_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3312_, 0, v___f_3310_);
                lean_ctor_set(v___x_3312_, 1, v___f_3311_);
                v___f_3313_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3313_, 0, v_toSeqRight_3304_);
                v___f_3314_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3314_, 0, v_toSeqLeft_3303_);
                v___f_3315_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3315_, 0, v_toSeq_3302_);
                if v_isShared_3307_ == 0 {
                    lean_ctor_set(v___x_3306_, 4, v___f_3313_);
                    lean_ctor_set(v___x_3306_, 3, v___f_3314_);
                    lean_ctor_set(v___x_3306_, 2, v___f_3315_);
                    lean_ctor_set(v___x_3306_, 1, v___f_3308_);
                    lean_ctor_set(v___x_3306_, 0, v___x_3312_);
                    v___x_3317_ = v___x_3306_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3312_);
                    lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___f_3308_);
                    lean_ctor_set(v_reuseFailAlloc_3356_, 2, v___f_3315_);
                    lean_ctor_set(v_reuseFailAlloc_3356_, 3, v___f_3314_);
                    lean_ctor_set(v_reuseFailAlloc_3356_, 4, v___f_3313_);
                    v___x_3317_ = v_reuseFailAlloc_3356_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3300_ == 0 {
                    lean_ctor_set(v___x_3299_, 1, v___f_3309_);
                    lean_ctor_set(v___x_3299_, 0, v___x_3317_);
                    v___x_3319_ = v___x_3299_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3317_);
                    lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___f_3309_);
                    v___x_3319_ = v_reuseFailAlloc_3355_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3320_ = l_StateRefT_x27_instMonad___redArg(v___x_3319_);
                v_toApplicative_3321_ = lean_ctor_get(v___x_3320_, 0);
                v_isSharedCheck_3353_ = (!lean_is_exclusive(v___x_3320_)) as u8;
                if v_isSharedCheck_3353_ == 0 {
                    v_unused_3354_ = lean_ctor_get(v___x_3320_, 1);
                    lean_dec(v_unused_3354_);
                    v___x_3323_ = v___x_3320_;
                    v_isShared_3324_ = v_isSharedCheck_3353_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3321_);
                    lean_dec(v___x_3320_);
                    v___x_3323_ = lean_box(0);
                    v_isShared_3324_ = v_isSharedCheck_3353_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_3325_ = lean_ctor_get(v_toApplicative_3321_, 0);
                v_toSeq_3326_ = lean_ctor_get(v_toApplicative_3321_, 2);
                v_toSeqLeft_3327_ = lean_ctor_get(v_toApplicative_3321_, 3);
                v_toSeqRight_3328_ = lean_ctor_get(v_toApplicative_3321_, 4);
                v_isSharedCheck_3351_ = (!lean_is_exclusive(v_toApplicative_3321_)) as u8;
                if v_isSharedCheck_3351_ == 0 {
                    v_unused_3352_ = lean_ctor_get(v_toApplicative_3321_, 1);
                    lean_dec(v_unused_3352_);
                    v___x_3330_ = v_toApplicative_3321_;
                    v_isShared_3331_ = v_isSharedCheck_3351_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_3328_);
                    lean_inc(v_toSeqLeft_3327_);
                    lean_inc(v_toSeq_3326_);
                    lean_inc(v_toFunctor_3325_);
                    lean_dec(v_toApplicative_3321_);
                    v___x_3330_ = lean_box(0);
                    v_isShared_3331_ = v_isSharedCheck_3351_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_3332_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__0;
                v___f_3333_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__1;
                lean_inc_ref(v_toFunctor_3325_);
                v___f_3334_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3334_, 0, v_toFunctor_3325_);
                v___f_3335_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3335_, 0, v_toFunctor_3325_);
                v___x_3336_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3336_, 0, v___f_3334_);
                lean_ctor_set(v___x_3336_, 1, v___f_3335_);
                v___f_3337_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3337_, 0, v_toSeqRight_3328_);
                v___f_3338_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3338_, 0, v_toSeqLeft_3327_);
                v___f_3339_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3339_, 0, v_toSeq_3326_);
                if v_isShared_3331_ == 0 {
                    lean_ctor_set(v___x_3330_, 4, v___f_3337_);
                    lean_ctor_set(v___x_3330_, 3, v___f_3338_);
                    lean_ctor_set(v___x_3330_, 2, v___f_3339_);
                    lean_ctor_set(v___x_3330_, 1, v___f_3332_);
                    lean_ctor_set(v___x_3330_, 0, v___x_3336_);
                    v___x_3341_ = v___x_3330_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3336_);
                    lean_ctor_set(v_reuseFailAlloc_3350_, 1, v___f_3332_);
                    lean_ctor_set(v_reuseFailAlloc_3350_, 2, v___f_3339_);
                    lean_ctor_set(v_reuseFailAlloc_3350_, 3, v___f_3338_);
                    lean_ctor_set(v_reuseFailAlloc_3350_, 4, v___f_3337_);
                    v___x_3341_ = v_reuseFailAlloc_3350_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3324_ == 0 {
                    lean_ctor_set(v___x_3323_, 1, v___f_3333_);
                    lean_ctor_set(v___x_3323_, 0, v___x_3341_);
                    v___x_3343_ = v___x_3323_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3341_);
                    lean_ctor_set(v_reuseFailAlloc_3349_, 1, v___f_3333_);
                    v___x_3343_ = v_reuseFailAlloc_3349_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3344_ = l_StateRefT_x27_instMonad___redArg(v___x_3343_);
                v___x_3345_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__2), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__2_once), _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__2);
                v___x_3346_ = l_instInhabitedOfMonad___redArg(v___x_3344_, v___x_3345_);
                v___x_1169__overap_3347_ = lean_panic_fn_borrowed(v___x_3346_, v_msg_3288_);
                lean_dec(v___x_3346_);
                lean_inc(v___y_3293_);
                lean_inc_ref(v___y_3292_);
                lean_inc(v___y_3291_);
                lean_inc_ref(v___y_3290_);
                lean_inc(v___y_3289_);
                v___x_3348_ = lean_apply_6(
                    v___x_1169__overap_3347_,
                    v___y_3289_,
                    v___y_3290_,
                    v___y_3291_,
                    v___y_3292_,
                    v___y_3293_,
                    lean_box(0),
                );
                return v___x_3348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___boxed(
    mut v_msg_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3368_: *mut LeanObject = core::ptr::null_mut();
    v_res_3368_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0(
        v_msg_3361_,
        v___y_3362_,
        v___y_3363_,
        v___y_3364_,
        v___y_3365_,
        v___y_3366_,
    );
    lean_dec(v___y_3366_);
    lean_dec_ref(v___y_3365_);
    lean_dec(v___y_3364_);
    lean_dec_ref(v___y_3363_);
    lean_dec(v___y_3362_);
    return v_res_3368_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(
    mut v_sz_3369_: usize,
    mut v_i_3370_: usize,
    mut v_bs_3371_: *mut LeanObject,
    mut v___y_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3374_: u8 = 0;
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: usize = 0;
    let mut v___x_3382_: usize = 0;
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3388_: u8 = 0;
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3374_ = lean_usize_dec_lt(v_i_3370_, v_sz_3369_);
                if v___x_3374_ == 0 {
                    v___x_3375_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3375_, 0, v_bs_3371_);
                    return v___x_3375_;
                } else {
                    v_v_3376_ = lean_array_uget_borrowed(v_bs_3371_, v_i_3370_);
                    lean_inc(v_v_3376_);
                    v___x_3377_ = l_Lean_Compiler_LCNF_StructProjCases_visitArg___redArg(
                        v_v_3376_,
                        v___y_3372_,
                    );
                    if lean_obj_tag(v___x_3377_) == 0 {
                        v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
                        lean_inc(v_a_3378_);
                        lean_dec_ref_known(v___x_3377_, 1);
                        v___x_3379_ = lean_unsigned_to_nat(0);
                        v_bs_x27_3380_ = lean_array_uset(v_bs_3371_, v_i_3370_, v___x_3379_);
                        v___x_3381_ = 1usize;
                        v___x_3382_ = lean_usize_add(v_i_3370_, v___x_3381_);
                        v___x_3383_ = lean_array_uset(v_bs_x27_3380_, v_i_3370_, v_a_3378_);
                        v_i_3370_ = v___x_3382_;
                        v_bs_3371_ = v___x_3383_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_3371_);
                        v_a_3385_ = lean_ctor_get(v___x_3377_, 0);
                        v_isSharedCheck_3392_ = (!lean_is_exclusive(v___x_3377_)) as u8;
                        if v_isSharedCheck_3392_ == 0 {
                            v___x_3387_ = v___x_3377_;
                            v_isShared_3388_ = v_isSharedCheck_3392_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3385_);
                            lean_dec(v___x_3377_);
                            v___x_3387_ = lean_box(0);
                            v_isShared_3388_ = v_isSharedCheck_3392_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3388_ == 0 {
                    v___x_3390_ = v___x_3387_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
                    v___x_3390_ = v_reuseFailAlloc_3391_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3390_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg___boxed(
    mut v_sz_3393_: *mut LeanObject,
    mut v_i_3394_: *mut LeanObject,
    mut v_bs_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3398_: usize = 0;
    let mut v_i_boxed_3399_: usize = 0;
    let mut v_res_3400_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3398_ = lean_unbox_usize(v_sz_3393_);
    lean_dec(v_sz_3393_);
    v_i_boxed_3399_ = lean_unbox_usize(v_i_3394_);
    lean_dec(v_i_3394_);
    v_res_3400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(v_sz_boxed_3398_, v_i_boxed_3399_, v_bs_3395_, v___y_3396_);
    lean_dec(v___y_3396_);
    return v_res_3400_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__1()
-> *mut LeanObject {
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    v___x_3402_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2;
    v___x_3403_ = lean_unsigned_to_nat(16);
    v___x_3404_ = lean_unsigned_to_nat(117);
    v___x_3405_ = l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__0;
    v___x_3406_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0;
    v___x_3407_ = l_mkPanicMessageWithDecl(
        v___x_3406_,
        v___x_3405_,
        v___x_3404_,
        v___x_3403_,
        v___x_3402_,
    );
    return v___x_3407_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_visitLetValue(
    mut v_v_3408_: *mut LeanObject,
    mut v_a_3409_: *mut LeanObject,
    mut v_a_3410_: *mut LeanObject,
    mut v_a_3411_: *mut LeanObject,
    mut v_a_3412_: *mut LeanObject,
    mut v_a_3413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3418_: usize = 0;
    let mut v___x_3419_: usize = 0;
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v___x_3425_: u8 = 0;
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3430_: u8 = 0;
    let mut v_a_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3434_: u8 = 0;
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3438_: u8 = 0;
    let mut v_fvarId_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3443_: usize = 0;
    let mut v___x_3444_: usize = 0;
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3449_: u8 = 0;
    let mut v___x_3450_: u8 = 0;
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_a_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3459_: u8 = 0;
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3463_: u8 = 0;
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_v_3408_) {
                    2 => {
                        lean_dec_ref_known(v_v_3408_, 3);
                        v___x_3415_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__1_once
                            ),
                            _init_l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___closed__1,
                        );
                        v___x_3416_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0(v___x_3415_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
                        return v___x_3416_;
                    }
                    3 => {
                        v_args_3417_ = lean_ctor_get(v_v_3408_, 2);
                        v_sz_3418_ = lean_array_size(v_args_3417_);
                        v___x_3419_ = 0usize;
                        lean_inc_ref(v_args_3417_);
                        v___x_3420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(v_sz_3418_, v___x_3419_, v_args_3417_, v_a_3409_);
                        if lean_obj_tag(v___x_3420_) == 0 {
                            v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
                            v_isSharedCheck_3430_ = (!lean_is_exclusive(v___x_3420_)) as u8;
                            if v_isSharedCheck_3430_ == 0 {
                                v___x_3423_ = v___x_3420_;
                                v_isShared_3424_ = v_isSharedCheck_3430_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3421_);
                                lean_dec(v___x_3420_);
                                v___x_3423_ = lean_box(0);
                                v_isShared_3424_ = v_isSharedCheck_3430_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_v_3408_, 3);
                            v_a_3431_ = lean_ctor_get(v___x_3420_, 0);
                            v_isSharedCheck_3438_ = (!lean_is_exclusive(v___x_3420_)) as u8;
                            if v_isSharedCheck_3438_ == 0 {
                                v___x_3433_ = v___x_3420_;
                                v_isShared_3434_ = v_isSharedCheck_3438_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3431_);
                                lean_dec(v___x_3420_);
                                v___x_3433_ = lean_box(0);
                                v_isShared_3434_ = v_isSharedCheck_3438_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                    4 => {
                        v_fvarId_3439_ = lean_ctor_get(v_v_3408_, 0);
                        v_args_3440_ = lean_ctor_get(v_v_3408_, 1);
                        lean_inc(v_fvarId_3439_);
                        v___x_3441_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(
                            v_fvarId_3439_,
                            v_a_3409_,
                        );
                        v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
                        lean_inc(v_a_3442_);
                        lean_dec_ref(v___x_3441_);
                        v_sz_3443_ = lean_array_size(v_args_3440_);
                        v___x_3444_ = 0usize;
                        lean_inc_ref(v_args_3440_);
                        v___x_3445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(v_sz_3443_, v___x_3444_, v_args_3440_, v_a_3409_);
                        if lean_obj_tag(v___x_3445_) == 0 {
                            v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
                            v_isSharedCheck_3455_ = (!lean_is_exclusive(v___x_3445_)) as u8;
                            if v_isSharedCheck_3455_ == 0 {
                                v___x_3448_ = v___x_3445_;
                                v_isShared_3449_ = v_isSharedCheck_3455_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3446_);
                                lean_dec(v___x_3445_);
                                v___x_3448_ = lean_box(0);
                                v_isShared_3449_ = v_isSharedCheck_3455_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3442_);
                            lean_dec_ref_known(v_v_3408_, 2);
                            v_a_3456_ = lean_ctor_get(v___x_3445_, 0);
                            v_isSharedCheck_3463_ = (!lean_is_exclusive(v___x_3445_)) as u8;
                            if v_isSharedCheck_3463_ == 0 {
                                v___x_3458_ = v___x_3445_;
                                v_isShared_3459_ = v_isSharedCheck_3463_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_3456_);
                                lean_dec(v___x_3445_);
                                v___x_3458_ = lean_box(0);
                                v_isShared_3459_ = v_isSharedCheck_3463_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                    _ => {
                        v___x_3464_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3464_, 0, v_v_3408_);
                        return v___x_3464_;
                    }
                }
            }
            1 => {
                v___x_3425_ = 0;
                v___x_3426_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v___x_3425_, v_v_3408_, v_a_3421_);
                if v_isShared_3424_ == 0 {
                    lean_ctor_set(v___x_3423_, 0, v___x_3426_);
                    v___x_3428_ = v___x_3423_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3426_);
                    v___x_3428_ = v_reuseFailAlloc_3429_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3428_;
            }
            3 => {
                if v_isShared_3434_ == 0 {
                    v___x_3436_ = v___x_3433_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
                    v___x_3436_ = v_reuseFailAlloc_3437_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3436_;
            }
            5 => {
                v___x_3450_ = 0;
                v___x_3451_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v___x_3450_, v_v_3408_, v_a_3442_, v_a_3446_);
                lean_dec_ref_known(v_v_3408_, 2);
                if v_isShared_3449_ == 0 {
                    lean_ctor_set(v___x_3448_, 0, v___x_3451_);
                    v___x_3453_ = v___x_3448_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
                    v___x_3453_ = v_reuseFailAlloc_3454_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3453_;
            }
            7 => {
                if v_isShared_3459_ == 0 {
                    v___x_3461_ = v___x_3458_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
                    v___x_3461_ = v_reuseFailAlloc_3462_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_visitLetValue___boxed(
    mut v_v_3465_: *mut LeanObject,
    mut v_a_3466_: *mut LeanObject,
    mut v_a_3467_: *mut LeanObject,
    mut v_a_3468_: *mut LeanObject,
    mut v_a_3469_: *mut LeanObject,
    mut v_a_3470_: *mut LeanObject,
    mut v_a_3471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3472_: *mut LeanObject = core::ptr::null_mut();
    v_res_3472_ = l_Lean_Compiler_LCNF_StructProjCases_visitLetValue(
        v_v_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_,
    );
    lean_dec(v_a_3470_);
    lean_dec_ref(v_a_3469_);
    lean_dec(v_a_3468_);
    lean_dec_ref(v_a_3467_);
    lean_dec(v_a_3466_);
    return v_res_3472_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1(
    mut v_sz_3473_: usize,
    mut v_i_3474_: usize,
    mut v_bs_3475_: *mut LeanObject,
    mut v___y_3476_: *mut LeanObject,
    mut v___y_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    v___x_3482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(v_sz_3473_, v_i_3474_, v_bs_3475_, v___y_3476_);
    return v___x_3482_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___boxed(
    mut v_sz_3483_: *mut LeanObject,
    mut v_i_3484_: *mut LeanObject,
    mut v_bs_3485_: *mut LeanObject,
    mut v___y_3486_: *mut LeanObject,
    mut v___y_3487_: *mut LeanObject,
    mut v___y_3488_: *mut LeanObject,
    mut v___y_3489_: *mut LeanObject,
    mut v___y_3490_: *mut LeanObject,
    mut v___y_3491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3492_: usize = 0;
    let mut v_i_boxed_3493_: usize = 0;
    let mut v_res_3494_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3492_ = lean_unbox_usize(v_sz_3483_);
    lean_dec(v_sz_3483_);
    v_i_boxed_3493_ = lean_unbox_usize(v_i_3484_);
    lean_dec(v_i_3484_);
    v_res_3494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1(v_sz_boxed_3492_, v_i_boxed_3493_, v_bs_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
    lean_dec(v___y_3490_);
    lean_dec_ref(v___y_3489_);
    lean_dec(v___y_3488_);
    lean_dec_ref(v___y_3487_);
    lean_dec(v___y_3486_);
    return v_res_3494_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__4___redArg(
    mut v_a_3495_: *mut LeanObject,
    mut v_b_3496_: *mut LeanObject,
    mut v_x_3497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3503_: u8 = 0;
    let mut v___x_3504_: u8 = 0;
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3497_) == 0 {
                    lean_dec(v_b_3496_);
                    lean_dec(v_a_3495_);
                    return v_x_3497_;
                } else {
                    v_key_3498_ = lean_ctor_get(v_x_3497_, 0);
                    v_value_3499_ = lean_ctor_get(v_x_3497_, 1);
                    v_tail_3500_ = lean_ctor_get(v_x_3497_, 2);
                    v_isSharedCheck_3512_ = (!lean_is_exclusive(v_x_3497_)) as u8;
                    if v_isSharedCheck_3512_ == 0 {
                        v___x_3502_ = v_x_3497_;
                        v_isShared_3503_ = v_isSharedCheck_3512_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3500_);
                        lean_inc(v_value_3499_);
                        lean_inc(v_key_3498_);
                        lean_dec(v_x_3497_);
                        v___x_3502_ = lean_box(0);
                        v_isShared_3503_ = v_isSharedCheck_3512_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3504_ = l_Lean_instBEqFVarId_beq(v_key_3498_, v_a_3495_);
                if v___x_3504_ == 0 {
                    v___x_3505_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__4___redArg(v_a_3495_, v_b_3496_, v_tail_3500_);
                    if v_isShared_3503_ == 0 {
                        lean_ctor_set(v___x_3502_, 2, v___x_3505_);
                        v___x_3507_ = v___x_3502_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_key_3498_);
                        lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_value_3499_);
                        lean_ctor_set(v_reuseFailAlloc_3508_, 2, v___x_3505_);
                        v___x_3507_ = v_reuseFailAlloc_3508_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_3499_);
                    lean_dec(v_key_3498_);
                    if v_isShared_3503_ == 0 {
                        lean_ctor_set(v___x_3502_, 1, v_b_3496_);
                        lean_ctor_set(v___x_3502_, 0, v_a_3495_);
                        v___x_3510_ = v___x_3502_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3495_);
                        lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_b_3496_);
                        lean_ctor_set(v_reuseFailAlloc_3511_, 2, v_tail_3500_);
                        v___x_3510_ = v_reuseFailAlloc_3511_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3507_;
            }
            3 => {
                return v___x_3510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5_spec__10___redArg(
    mut v_x_3513_: *mut LeanObject,
    mut v_x_3514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3520_: u8 = 0;
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: u64 = 0;
    let mut v___x_3523_: u64 = 0;
    let mut v___x_3524_: u64 = 0;
    let mut v_fold_3525_: u64 = 0;
    let mut v___x_3526_: u64 = 0;
    let mut v___x_3527_: u64 = 0;
    let mut v___x_3528_: u64 = 0;
    let mut v___x_3529_: usize = 0;
    let mut v___x_3530_: usize = 0;
    let mut v___x_3531_: usize = 0;
    let mut v___x_3532_: usize = 0;
    let mut v___x_3533_: usize = 0;
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3514_) == 0 {
                    return v_x_3513_;
                } else {
                    v_key_3515_ = lean_ctor_get(v_x_3514_, 0);
                    v_value_3516_ = lean_ctor_get(v_x_3514_, 1);
                    v_tail_3517_ = lean_ctor_get(v_x_3514_, 2);
                    v_isSharedCheck_3540_ = (!lean_is_exclusive(v_x_3514_)) as u8;
                    if v_isSharedCheck_3540_ == 0 {
                        v___x_3519_ = v_x_3514_;
                        v_isShared_3520_ = v_isSharedCheck_3540_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3517_);
                        lean_inc(v_value_3516_);
                        lean_inc(v_key_3515_);
                        lean_dec(v_x_3514_);
                        v___x_3519_ = lean_box(0);
                        v_isShared_3520_ = v_isSharedCheck_3540_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3521_ = lean_array_get_size(v_x_3513_);
                v___x_3522_ = l_Lean_instHashableFVarId_hash(v_key_3515_);
                v___x_3523_ = 32u64;
                v___x_3524_ = lean_uint64_shift_right(v___x_3522_, v___x_3523_);
                v_fold_3525_ = lean_uint64_xor(v___x_3522_, v___x_3524_);
                v___x_3526_ = 16u64;
                v___x_3527_ = lean_uint64_shift_right(v_fold_3525_, v___x_3526_);
                v___x_3528_ = lean_uint64_xor(v_fold_3525_, v___x_3527_);
                v___x_3529_ = lean_uint64_to_usize(v___x_3528_);
                v___x_3530_ = lean_usize_of_nat(v___x_3521_);
                v___x_3531_ = 1usize;
                v___x_3532_ = lean_usize_sub(v___x_3530_, v___x_3531_);
                v___x_3533_ = lean_usize_land(v___x_3529_, v___x_3532_);
                v___x_3534_ = lean_array_uget_borrowed(v_x_3513_, v___x_3533_);
                lean_inc(v___x_3534_);
                if v_isShared_3520_ == 0 {
                    lean_ctor_set(v___x_3519_, 2, v___x_3534_);
                    v___x_3536_ = v___x_3519_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_key_3515_);
                    lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_value_3516_);
                    lean_ctor_set(v_reuseFailAlloc_3539_, 2, v___x_3534_);
                    v___x_3536_ = v_reuseFailAlloc_3539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3537_ = lean_array_uset(v_x_3513_, v___x_3533_, v___x_3536_);
                v_x_3513_ = v___x_3537_;
                v_x_3514_ = v_tail_3517_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5___redArg(
    mut v_i_3541_: *mut LeanObject,
    mut v_source_3542_: *mut LeanObject,
    mut v_target_3543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: u8 = 0;
    let mut v_es_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3544_ = lean_array_get_size(v_source_3542_);
                v___x_3545_ = lean_nat_dec_lt(v_i_3541_, v___x_3544_);
                if v___x_3545_ == 0 {
                    lean_dec_ref(v_source_3542_);
                    lean_dec(v_i_3541_);
                    return v_target_3543_;
                } else {
                    v_es_3546_ = lean_array_fget(v_source_3542_, v_i_3541_);
                    v___x_3547_ = lean_box(0);
                    v_source_3548_ = lean_array_fset(v_source_3542_, v_i_3541_, v___x_3547_);
                    v_target_3549_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5_spec__10___redArg(v_target_3543_, v_es_3546_);
                    v___x_3550_ = lean_unsigned_to_nat(1);
                    v___x_3551_ = lean_nat_add(v_i_3541_, v___x_3550_);
                    lean_dec(v_i_3541_);
                    v_i_3541_ = v___x_3551_;
                    v_source_3542_ = v_source_3548_;
                    v_target_3543_ = v_target_3549_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3___redArg(
    mut v_data_3553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    v___x_3554_ = lean_array_get_size(v_data_3553_);
    v___x_3555_ = lean_unsigned_to_nat(2);
    v_nbuckets_3556_ = lean_nat_mul(v___x_3554_, v___x_3555_);
    v___x_3557_ = lean_unsigned_to_nat(0);
    v___x_3558_ = lean_box(0);
    v___x_3559_ = lean_mk_array(v_nbuckets_3556_, v___x_3558_);
    v___x_3560_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5___redArg(v___x_3557_, v_data_3553_, v___x_3559_);
    return v___x_3560_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg(
    mut v_a_3561_: *mut LeanObject,
    mut v_x_3562_: *mut LeanObject,
) -> u8 {
    let mut v___x_3563_: u8 = 0;
    let mut v_key_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3562_) == 0 {
                    v___x_3563_ = 0;
                    return v___x_3563_;
                } else {
                    v_key_3564_ = lean_ctor_get(v_x_3562_, 0);
                    v_tail_3565_ = lean_ctor_get(v_x_3562_, 2);
                    v___x_3566_ = l_Lean_instBEqFVarId_beq(v_key_3564_, v_a_3561_);
                    if v___x_3566_ == 0 {
                        v_x_3562_ = v_tail_3565_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3566_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg___boxed(
    mut v_a_3568_: *mut LeanObject,
    mut v_x_3569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3570_: u8 = 0;
    let mut v_r_3571_: *mut LeanObject = core::ptr::null_mut();
    v_res_3570_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg(v_a_3568_, v_x_3569_);
    lean_dec(v_x_3569_);
    lean_dec(v_a_3568_);
    v_r_3571_ = lean_box((v_res_3570_) as usize);
    return v_r_3571_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(
    mut v_m_3572_: *mut LeanObject,
    mut v_a_3573_: *mut LeanObject,
    mut v_b_3574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3579_: u8 = 0;
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: u64 = 0;
    let mut v___x_3582_: u64 = 0;
    let mut v___x_3583_: u64 = 0;
    let mut v_fold_3584_: u64 = 0;
    let mut v___x_3585_: u64 = 0;
    let mut v___x_3586_: u64 = 0;
    let mut v___x_3587_: u64 = 0;
    let mut v___x_3588_: usize = 0;
    let mut v___x_3589_: usize = 0;
    let mut v___x_3590_: usize = 0;
    let mut v___x_3591_: usize = 0;
    let mut v___x_3592_: usize = 0;
    let mut v_bkt_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: u8 = 0;
    let mut v_val_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3575_ = lean_ctor_get(v_m_3572_, 0);
                v_buckets_3576_ = lean_ctor_get(v_m_3572_, 1);
                v_isSharedCheck_3619_ = (!lean_is_exclusive(v_m_3572_)) as u8;
                if v_isSharedCheck_3619_ == 0 {
                    v___x_3578_ = v_m_3572_;
                    v_isShared_3579_ = v_isSharedCheck_3619_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3576_);
                    lean_inc(v_size_3575_);
                    lean_dec(v_m_3572_);
                    v___x_3578_ = lean_box(0);
                    v_isShared_3579_ = v_isSharedCheck_3619_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3580_ = lean_array_get_size(v_buckets_3576_);
                v___x_3581_ = l_Lean_instHashableFVarId_hash(v_a_3573_);
                v___x_3582_ = 32u64;
                v___x_3583_ = lean_uint64_shift_right(v___x_3581_, v___x_3582_);
                v_fold_3584_ = lean_uint64_xor(v___x_3581_, v___x_3583_);
                v___x_3585_ = 16u64;
                v___x_3586_ = lean_uint64_shift_right(v_fold_3584_, v___x_3585_);
                v___x_3587_ = lean_uint64_xor(v_fold_3584_, v___x_3586_);
                v___x_3588_ = lean_uint64_to_usize(v___x_3587_);
                v___x_3589_ = lean_usize_of_nat(v___x_3580_);
                v___x_3590_ = 1usize;
                v___x_3591_ = lean_usize_sub(v___x_3589_, v___x_3590_);
                v___x_3592_ = lean_usize_land(v___x_3588_, v___x_3591_);
                v_bkt_3593_ = lean_array_uget_borrowed(v_buckets_3576_, v___x_3592_);
                v___x_3594_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg(v_a_3573_, v_bkt_3593_);
                if v___x_3594_ == 0 {
                    v___x_3595_ = lean_unsigned_to_nat(1);
                    v_size_x27_3596_ = lean_nat_add(v_size_3575_, v___x_3595_);
                    lean_dec(v_size_3575_);
                    lean_inc(v_bkt_3593_);
                    v___x_3597_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3597_, 0, v_a_3573_);
                    lean_ctor_set(v___x_3597_, 1, v_b_3574_);
                    lean_ctor_set(v___x_3597_, 2, v_bkt_3593_);
                    v_buckets_x27_3598_ =
                        lean_array_uset(v_buckets_3576_, v___x_3592_, v___x_3597_);
                    v___x_3599_ = lean_unsigned_to_nat(4);
                    v___x_3600_ = lean_nat_mul(v_size_x27_3596_, v___x_3599_);
                    v___x_3601_ = lean_unsigned_to_nat(3);
                    v___x_3602_ = lean_nat_div(v___x_3600_, v___x_3601_);
                    lean_dec(v___x_3600_);
                    v___x_3603_ = lean_array_get_size(v_buckets_x27_3598_);
                    v___x_3604_ = lean_nat_dec_le(v___x_3602_, v___x_3603_);
                    lean_dec(v___x_3602_);
                    if v___x_3604_ == 0 {
                        v_val_3605_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3___redArg(v_buckets_x27_3598_);
                        if v_isShared_3579_ == 0 {
                            lean_ctor_set(v___x_3578_, 1, v_val_3605_);
                            lean_ctor_set(v___x_3578_, 0, v_size_x27_3596_);
                            v___x_3607_ = v___x_3578_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_size_x27_3596_);
                            lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_val_3605_);
                            v___x_3607_ = v_reuseFailAlloc_3608_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3579_ == 0 {
                            lean_ctor_set(v___x_3578_, 1, v_buckets_x27_3598_);
                            lean_ctor_set(v___x_3578_, 0, v_size_x27_3596_);
                            v___x_3610_ = v___x_3578_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_size_x27_3596_);
                            lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_buckets_x27_3598_);
                            v___x_3610_ = v_reuseFailAlloc_3611_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3593_);
                    v___x_3612_ = lean_box(0);
                    v_buckets_x27_3613_ =
                        lean_array_uset(v_buckets_3576_, v___x_3592_, v___x_3612_);
                    v___x_3614_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__4___redArg(v_a_3573_, v_b_3574_, v_bkt_3593_);
                    v___x_3615_ = lean_array_uset(v_buckets_x27_3613_, v___x_3592_, v___x_3614_);
                    if v_isShared_3579_ == 0 {
                        lean_ctor_set(v___x_3578_, 1, v___x_3615_);
                        v___x_3617_ = v___x_3578_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_size_3575_);
                        lean_ctor_set(v_reuseFailAlloc_3618_, 1, v___x_3615_);
                        v___x_3617_ = v_reuseFailAlloc_3618_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3607_;
            }
            3 => {
                return v___x_3610_;
            }
            4 => {
                return v___x_3617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___redArg(
    mut v_as_3620_: *mut LeanObject,
    mut v_sz_3621_: usize,
    mut v_i_3622_: usize,
    mut v_b_3623_: *mut LeanObject,
    mut v___y_3624_: *mut LeanObject,
    mut v___y_3625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3627_: u8 = 0;
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: u8 = 0;
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3636_: u8 = 0;
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projMap_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarMap_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3642_: u8 = 0;
    let mut v_a_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: u8 = 0;
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: usize = 0;
    let mut v___x_3657_: usize = 0;
    let mut v_reuseFailAlloc_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3667_: u8 = 0;
    let mut v_reuseFailAlloc_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3669_: u8 = 0;
    let mut v_isSharedCheck_3670_: u8 = 0;
    let mut v_unused_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3627_ = lean_usize_dec_lt(v_i_3622_, v_sz_3621_);
                if v___x_3627_ == 0 {
                    v___x_3628_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3628_, 0, v_b_3623_);
                    return v___x_3628_;
                } else {
                    v_array_3629_ = lean_ctor_get(v_b_3623_, 0);
                    v_start_3630_ = lean_ctor_get(v_b_3623_, 1);
                    v_stop_3631_ = lean_ctor_get(v_b_3623_, 2);
                    v___x_3632_ = lean_nat_dec_lt(v_start_3630_, v_stop_3631_);
                    if v___x_3632_ == 0 {
                        v___x_3633_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3633_, 0, v_b_3623_);
                        return v___x_3633_;
                    } else {
                        lean_inc(v_stop_3631_);
                        lean_inc(v_start_3630_);
                        lean_inc_ref(v_array_3629_);
                        v_isSharedCheck_3670_ = (!lean_is_exclusive(v_b_3623_)) as u8;
                        if v_isSharedCheck_3670_ == 0 {
                            v_unused_3671_ = lean_ctor_get(v_b_3623_, 2);
                            lean_dec(v_unused_3671_);
                            v_unused_3672_ = lean_ctor_get(v_b_3623_, 1);
                            lean_dec(v_unused_3672_);
                            v_unused_3673_ = lean_ctor_get(v_b_3623_, 0);
                            lean_dec(v_unused_3673_);
                            v___x_3635_ = v_b_3623_;
                            v_isShared_3636_ = v_isSharedCheck_3670_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_b_3623_);
                            v___x_3635_ = lean_box(0);
                            v_isShared_3636_ = v_isSharedCheck_3670_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3637_ = lean_st_ref_take(v___y_3624_);
                v_projMap_3638_ = lean_ctor_get(v___x_3637_, 0);
                v_fvarMap_3639_ = lean_ctor_get(v___x_3637_, 1);
                v_isSharedCheck_3669_ = (!lean_is_exclusive(v___x_3637_)) as u8;
                if v_isSharedCheck_3669_ == 0 {
                    v___x_3641_ = v___x_3637_;
                    v_isShared_3642_ = v_isSharedCheck_3669_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fvarMap_3639_);
                    lean_inc(v_projMap_3638_);
                    lean_dec(v___x_3637_);
                    v___x_3641_ = lean_box(0);
                    v_isShared_3642_ = v_isSharedCheck_3669_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3643_ = lean_array_uget_borrowed(v_as_3620_, v_i_3622_);
                v_fvarId_3644_ = lean_ctor_get(v_a_3643_, 0);
                v___x_3645_ = lean_array_fget_borrowed(v_array_3629_, v_start_3630_);
                lean_inc(v___x_3645_);
                lean_inc(v_fvarId_3644_);
                v___x_3646_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(v_fvarMap_3639_, v_fvarId_3644_, v___x_3645_);
                if v_isShared_3642_ == 0 {
                    lean_ctor_set(v___x_3641_, 1, v___x_3646_);
                    v___x_3648_ = v___x_3641_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_projMap_3638_);
                    lean_ctor_set(v_reuseFailAlloc_3668_, 1, v___x_3646_);
                    v___x_3648_ = v_reuseFailAlloc_3668_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3649_ = lean_st_ref_set(v___y_3624_, v___x_3648_);
                v___x_3650_ = 0;
                v___x_3651_ =
                    l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_3650_, v_a_3643_, v___y_3625_);
                if lean_obj_tag(v___x_3651_) == 0 {
                    lean_dec_ref_known(v___x_3651_, 1);
                    v___x_3652_ = lean_unsigned_to_nat(1);
                    v___x_3653_ = lean_nat_add(v_start_3630_, v___x_3652_);
                    lean_dec(v_start_3630_);
                    if v_isShared_3636_ == 0 {
                        lean_ctor_set(v___x_3635_, 1, v___x_3653_);
                        v___x_3655_ = v___x_3635_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_array_3629_);
                        lean_ctor_set(v_reuseFailAlloc_3659_, 1, v___x_3653_);
                        lean_ctor_set(v_reuseFailAlloc_3659_, 2, v_stop_3631_);
                        v___x_3655_ = v_reuseFailAlloc_3659_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3635_);
                    lean_dec(v_stop_3631_);
                    lean_dec(v_start_3630_);
                    lean_dec_ref(v_array_3629_);
                    v_a_3660_ = lean_ctor_get(v___x_3651_, 0);
                    v_isSharedCheck_3667_ = (!lean_is_exclusive(v___x_3651_)) as u8;
                    if v_isSharedCheck_3667_ == 0 {
                        v___x_3662_ = v___x_3651_;
                        v_isShared_3663_ = v_isSharedCheck_3667_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3660_);
                        lean_dec(v___x_3651_);
                        v___x_3662_ = lean_box(0);
                        v_isShared_3663_ = v_isSharedCheck_3667_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3656_ = 1usize;
                v___x_3657_ = lean_usize_add(v_i_3622_, v___x_3656_);
                v_i_3622_ = v___x_3657_;
                v_b_3623_ = v___x_3655_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_3663_ == 0 {
                    v___x_3665_ = v___x_3662_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
                    v___x_3665_ = v_reuseFailAlloc_3666_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___redArg___boxed(
    mut v_as_3674_: *mut LeanObject,
    mut v_sz_3675_: *mut LeanObject,
    mut v_i_3676_: *mut LeanObject,
    mut v_b_3677_: *mut LeanObject,
    mut v___y_3678_: *mut LeanObject,
    mut v___y_3679_: *mut LeanObject,
    mut v___y_3680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3681_: usize = 0;
    let mut v_i_boxed_3682_: usize = 0;
    let mut v_res_3683_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3681_ = lean_unbox_usize(v_sz_3675_);
    lean_dec(v_sz_3675_);
    v_i_boxed_3682_ = lean_unbox_usize(v_i_3676_);
    lean_dec(v_i_3676_);
    v_res_3683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___redArg(v_as_3674_, v_sz_boxed_3681_, v_i_boxed_3682_, v_b_3677_, v___y_3678_, v___y_3679_);
    lean_dec(v___y_3679_);
    lean_dec(v___y_3678_);
    lean_dec_ref(v_as_3674_);
    return v_res_3683_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_3684_: u8 = 0;
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    v___x_3684_ = 0;
    v___x_3685_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_3684_);
    return v___x_3685_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4(
    mut v_msg_3686_: *mut LeanObject,
    mut v___y_3687_: *mut LeanObject,
    mut v___y_3688_: *mut LeanObject,
    mut v___y_3689_: *mut LeanObject,
    mut v___y_3690_: *mut LeanObject,
    mut v___y_3691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v_toFunctor_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3705_: u8 = 0;
    let mut v___f_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3722_: u8 = 0;
    let mut v_toFunctor_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3729_: u8 = 0;
    let mut v___f_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_14859__overap_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3749_: u8 = 0;
    let mut v_unused_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3751_: u8 = 0;
    let mut v_unused_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3755_: u8 = 0;
    let mut v_unused_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3757_: u8 = 0;
    let mut v_unused_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3693_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__0);
                v___x_3694_ = l_StateRefT_x27_instMonad___redArg(v___x_3693_);
                v_toApplicative_3695_ = lean_ctor_get(v___x_3694_, 0);
                v_isSharedCheck_3757_ = (!lean_is_exclusive(v___x_3694_)) as u8;
                if v_isSharedCheck_3757_ == 0 {
                    v_unused_3758_ = lean_ctor_get(v___x_3694_, 1);
                    lean_dec(v_unused_3758_);
                    v___x_3697_ = v___x_3694_;
                    v_isShared_3698_ = v_isSharedCheck_3757_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3695_);
                    lean_dec(v___x_3694_);
                    v___x_3697_ = lean_box(0);
                    v_isShared_3698_ = v_isSharedCheck_3757_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3699_ = lean_ctor_get(v_toApplicative_3695_, 0);
                v_toSeq_3700_ = lean_ctor_get(v_toApplicative_3695_, 2);
                v_toSeqLeft_3701_ = lean_ctor_get(v_toApplicative_3695_, 3);
                v_toSeqRight_3702_ = lean_ctor_get(v_toApplicative_3695_, 4);
                v_isSharedCheck_3755_ = (!lean_is_exclusive(v_toApplicative_3695_)) as u8;
                if v_isSharedCheck_3755_ == 0 {
                    v_unused_3756_ = lean_ctor_get(v_toApplicative_3695_, 1);
                    lean_dec(v_unused_3756_);
                    v___x_3704_ = v_toApplicative_3695_;
                    v_isShared_3705_ = v_isSharedCheck_3755_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_3702_);
                    lean_inc(v_toSeqLeft_3701_);
                    lean_inc(v_toSeq_3700_);
                    lean_inc(v_toFunctor_3699_);
                    lean_dec(v_toApplicative_3695_);
                    v___x_3704_ = lean_box(0);
                    v_isShared_3705_ = v_isSharedCheck_3755_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3706_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__1;
                v___f_3707_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_3699_);
                v___f_3708_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3708_, 0, v_toFunctor_3699_);
                v___f_3709_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3709_, 0, v_toFunctor_3699_);
                v___x_3710_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3710_, 0, v___f_3708_);
                lean_ctor_set(v___x_3710_, 1, v___f_3709_);
                v___f_3711_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3711_, 0, v_toSeqRight_3702_);
                v___f_3712_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3712_, 0, v_toSeqLeft_3701_);
                v___f_3713_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3713_, 0, v_toSeq_3700_);
                if v_isShared_3705_ == 0 {
                    lean_ctor_set(v___x_3704_, 4, v___f_3711_);
                    lean_ctor_set(v___x_3704_, 3, v___f_3712_);
                    lean_ctor_set(v___x_3704_, 2, v___f_3713_);
                    lean_ctor_set(v___x_3704_, 1, v___f_3706_);
                    lean_ctor_set(v___x_3704_, 0, v___x_3710_);
                    v___x_3715_ = v___x_3704_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3710_);
                    lean_ctor_set(v_reuseFailAlloc_3754_, 1, v___f_3706_);
                    lean_ctor_set(v_reuseFailAlloc_3754_, 2, v___f_3713_);
                    lean_ctor_set(v_reuseFailAlloc_3754_, 3, v___f_3712_);
                    lean_ctor_set(v_reuseFailAlloc_3754_, 4, v___f_3711_);
                    v___x_3715_ = v_reuseFailAlloc_3754_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3698_ == 0 {
                    lean_ctor_set(v___x_3697_, 1, v___f_3707_);
                    lean_ctor_set(v___x_3697_, 0, v___x_3715_);
                    v___x_3717_ = v___x_3697_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3715_);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 1, v___f_3707_);
                    v___x_3717_ = v_reuseFailAlloc_3753_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3718_ = l_StateRefT_x27_instMonad___redArg(v___x_3717_);
                v_toApplicative_3719_ = lean_ctor_get(v___x_3718_, 0);
                v_isSharedCheck_3751_ = (!lean_is_exclusive(v___x_3718_)) as u8;
                if v_isSharedCheck_3751_ == 0 {
                    v_unused_3752_ = lean_ctor_get(v___x_3718_, 1);
                    lean_dec(v_unused_3752_);
                    v___x_3721_ = v___x_3718_;
                    v_isShared_3722_ = v_isSharedCheck_3751_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3719_);
                    lean_dec(v___x_3718_);
                    v___x_3721_ = lean_box(0);
                    v_isShared_3722_ = v_isSharedCheck_3751_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_3723_ = lean_ctor_get(v_toApplicative_3719_, 0);
                v_toSeq_3724_ = lean_ctor_get(v_toApplicative_3719_, 2);
                v_toSeqLeft_3725_ = lean_ctor_get(v_toApplicative_3719_, 3);
                v_toSeqRight_3726_ = lean_ctor_get(v_toApplicative_3719_, 4);
                v_isSharedCheck_3749_ = (!lean_is_exclusive(v_toApplicative_3719_)) as u8;
                if v_isSharedCheck_3749_ == 0 {
                    v_unused_3750_ = lean_ctor_get(v_toApplicative_3719_, 1);
                    lean_dec(v_unused_3750_);
                    v___x_3728_ = v_toApplicative_3719_;
                    v_isShared_3729_ = v_isSharedCheck_3749_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_3726_);
                    lean_inc(v_toSeqLeft_3725_);
                    lean_inc(v_toSeq_3724_);
                    lean_inc(v_toFunctor_3723_);
                    lean_dec(v_toApplicative_3719_);
                    v___x_3728_ = lean_box(0);
                    v_isShared_3729_ = v_isSharedCheck_3749_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_3730_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__0;
                v___f_3731_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__0___closed__1;
                lean_inc_ref(v_toFunctor_3723_);
                v___f_3732_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3732_, 0, v_toFunctor_3723_);
                v___f_3733_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3733_, 0, v_toFunctor_3723_);
                v___x_3734_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3734_, 0, v___f_3732_);
                lean_ctor_set(v___x_3734_, 1, v___f_3733_);
                v___f_3735_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3735_, 0, v_toSeqRight_3726_);
                v___f_3736_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3736_, 0, v_toSeqLeft_3725_);
                v___f_3737_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3737_, 0, v_toSeq_3724_);
                if v_isShared_3729_ == 0 {
                    lean_ctor_set(v___x_3728_, 4, v___f_3735_);
                    lean_ctor_set(v___x_3728_, 3, v___f_3736_);
                    lean_ctor_set(v___x_3728_, 2, v___f_3737_);
                    lean_ctor_set(v___x_3728_, 1, v___f_3730_);
                    lean_ctor_set(v___x_3728_, 0, v___x_3734_);
                    v___x_3739_ = v___x_3728_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3734_);
                    lean_ctor_set(v_reuseFailAlloc_3748_, 1, v___f_3730_);
                    lean_ctor_set(v_reuseFailAlloc_3748_, 2, v___f_3737_);
                    lean_ctor_set(v_reuseFailAlloc_3748_, 3, v___f_3736_);
                    lean_ctor_set(v_reuseFailAlloc_3748_, 4, v___f_3735_);
                    v___x_3739_ = v_reuseFailAlloc_3748_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3722_ == 0 {
                    lean_ctor_set(v___x_3721_, 1, v___f_3731_);
                    lean_ctor_set(v___x_3721_, 0, v___x_3739_);
                    v___x_3741_ = v___x_3721_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3739_);
                    lean_ctor_set(v_reuseFailAlloc_3747_, 1, v___f_3731_);
                    v___x_3741_ = v_reuseFailAlloc_3747_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3742_ = l_StateRefT_x27_instMonad___redArg(v___x_3741_);
                v___x_3743_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0);
                v___x_3744_ = l_instInhabitedOfMonad___redArg(v___x_3742_, v___x_3743_);
                v___x_14859__overap_3745_ = lean_panic_fn_borrowed(v___x_3744_, v_msg_3686_);
                lean_dec(v___x_3744_);
                lean_inc(v___y_3691_);
                lean_inc_ref(v___y_3690_);
                lean_inc(v___y_3689_);
                lean_inc_ref(v___y_3688_);
                lean_inc(v___y_3687_);
                v___x_3746_ = lean_apply_6(
                    v___x_14859__overap_3745_,
                    v___y_3687_,
                    v___y_3688_,
                    v___y_3689_,
                    v___y_3690_,
                    v___y_3691_,
                    lean_box(0),
                );
                return v___x_3746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___boxed(
    mut v_msg_3759_: *mut LeanObject,
    mut v___y_3760_: *mut LeanObject,
    mut v___y_3761_: *mut LeanObject,
    mut v___y_3762_: *mut LeanObject,
    mut v___y_3763_: *mut LeanObject,
    mut v___y_3764_: *mut LeanObject,
    mut v___y_3765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3766_: *mut LeanObject = core::ptr::null_mut();
    v_res_3766_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4(
        v_msg_3759_,
        v___y_3760_,
        v___y_3761_,
        v___y_3762_,
        v___y_3763_,
        v___y_3764_,
    );
    lean_dec(v___y_3764_);
    lean_dec_ref(v___y_3763_);
    lean_dec(v___y_3762_);
    lean_dec_ref(v___y_3761_);
    lean_dec(v___y_3760_);
    return v_res_3766_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__0(
    mut v_msg_3767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    v___x_3768_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0_once
        ),
        _init_l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4___closed__0,
    );
    v___x_3769_ = lean_panic_fn_borrowed(v___x_3768_, v_msg_3767_);
    return v___x_3769_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__2(
    mut v_sz_3770_: usize,
    mut v_i_3771_: usize,
    mut v_bs_3772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3773_: u8 = 0;
    let mut v_v_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: usize = 0;
    let mut v___x_3779_: usize = 0;
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3773_ = lean_usize_dec_lt(v_i_3771_, v_sz_3770_);
                if v___x_3773_ == 0 {
                    return v_bs_3772_;
                } else {
                    v_v_3774_ = lean_array_uget_borrowed(v_bs_3772_, v_i_3771_);
                    v_fvarId_3775_ = lean_ctor_get(v_v_3774_, 0);
                    lean_inc(v_fvarId_3775_);
                    v___x_3776_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3777_ = lean_array_uset(v_bs_3772_, v_i_3771_, v___x_3776_);
                    v___x_3778_ = 1usize;
                    v___x_3779_ = lean_usize_add(v_i_3771_, v___x_3778_);
                    v___x_3780_ = lean_array_uset(v_bs_x27_3777_, v_i_3771_, v_fvarId_3775_);
                    v_i_3771_ = v___x_3779_;
                    v_bs_3772_ = v___x_3780_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__2___boxed(
    mut v_sz_3782_: *mut LeanObject,
    mut v_i_3783_: *mut LeanObject,
    mut v_bs_3784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3785_: usize = 0;
    let mut v_i_boxed_3786_: usize = 0;
    let mut v_res_3787_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3785_ = lean_unbox_usize(v_sz_3782_);
    lean_dec(v_sz_3782_);
    v_i_boxed_3786_ = lean_unbox_usize(v_i_3783_);
    lean_dec(v_i_3783_);
    v_res_3787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__2(v_sz_boxed_3785_, v_i_boxed_3786_, v_bs_3784_);
    return v_res_3787_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg(
    mut v_a_3788_: *mut LeanObject,
    mut v_x_3789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3795_: u8 = 0;
    let mut v___x_3796_: u8 = 0;
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3801_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3789_) == 0 {
                    return v_x_3789_;
                } else {
                    v_key_3790_ = lean_ctor_get(v_x_3789_, 0);
                    v_value_3791_ = lean_ctor_get(v_x_3789_, 1);
                    v_tail_3792_ = lean_ctor_get(v_x_3789_, 2);
                    v_isSharedCheck_3801_ = (!lean_is_exclusive(v_x_3789_)) as u8;
                    if v_isSharedCheck_3801_ == 0 {
                        v___x_3794_ = v_x_3789_;
                        v_isShared_3795_ = v_isSharedCheck_3801_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3792_);
                        lean_inc(v_value_3791_);
                        lean_inc(v_key_3790_);
                        lean_dec(v_x_3789_);
                        v___x_3794_ = lean_box(0);
                        v_isShared_3795_ = v_isSharedCheck_3801_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3796_ = l_Lean_instBEqFVarId_beq(v_key_3790_, v_a_3788_);
                if v___x_3796_ == 0 {
                    v___x_3797_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg(v_a_3788_, v_tail_3792_);
                    if v_isShared_3795_ == 0 {
                        lean_ctor_set(v___x_3794_, 2, v___x_3797_);
                        v___x_3799_ = v___x_3794_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_key_3790_);
                        lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_value_3791_);
                        lean_ctor_set(v_reuseFailAlloc_3800_, 2, v___x_3797_);
                        v___x_3799_ = v_reuseFailAlloc_3800_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3794_);
                    lean_dec(v_value_3791_);
                    lean_dec(v_key_3790_);
                    return v_tail_3792_;
                }
            }
            2 => {
                return v___x_3799_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg___boxed(
    mut v_a_3802_: *mut LeanObject,
    mut v_x_3803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3804_: *mut LeanObject = core::ptr::null_mut();
    v_res_3804_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg(v_a_3802_, v_x_3803_);
    lean_dec(v_a_3802_);
    return v_res_3804_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg(
    mut v_m_3805_: *mut LeanObject,
    mut v_a_3806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: u64 = 0;
    let mut v___x_3811_: u64 = 0;
    let mut v___x_3812_: u64 = 0;
    let mut v_fold_3813_: u64 = 0;
    let mut v___x_3814_: u64 = 0;
    let mut v___x_3815_: u64 = 0;
    let mut v___x_3816_: u64 = 0;
    let mut v___x_3817_: usize = 0;
    let mut v___x_3818_: usize = 0;
    let mut v___x_3819_: usize = 0;
    let mut v___x_3820_: usize = 0;
    let mut v___x_3821_: usize = 0;
    let mut v_bkt_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3826_: u8 = 0;
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3836_: u8 = 0;
    let mut v_unused_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3807_ = lean_ctor_get(v_m_3805_, 0);
                v_buckets_3808_ = lean_ctor_get(v_m_3805_, 1);
                v___x_3809_ = lean_array_get_size(v_buckets_3808_);
                v___x_3810_ = l_Lean_instHashableFVarId_hash(v_a_3806_);
                v___x_3811_ = 32u64;
                v___x_3812_ = lean_uint64_shift_right(v___x_3810_, v___x_3811_);
                v_fold_3813_ = lean_uint64_xor(v___x_3810_, v___x_3812_);
                v___x_3814_ = 16u64;
                v___x_3815_ = lean_uint64_shift_right(v_fold_3813_, v___x_3814_);
                v___x_3816_ = lean_uint64_xor(v_fold_3813_, v___x_3815_);
                v___x_3817_ = lean_uint64_to_usize(v___x_3816_);
                v___x_3818_ = lean_usize_of_nat(v___x_3809_);
                v___x_3819_ = 1usize;
                v___x_3820_ = lean_usize_sub(v___x_3818_, v___x_3819_);
                v___x_3821_ = lean_usize_land(v___x_3817_, v___x_3820_);
                v_bkt_3822_ = lean_array_uget_borrowed(v_buckets_3808_, v___x_3821_);
                v___x_3823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg(v_a_3806_, v_bkt_3822_);
                if v___x_3823_ == 0 {
                    return v_m_3805_;
                } else {
                    lean_inc(v_bkt_3822_);
                    lean_inc_ref(v_buckets_3808_);
                    lean_inc(v_size_3807_);
                    v_isSharedCheck_3836_ = (!lean_is_exclusive(v_m_3805_)) as u8;
                    if v_isSharedCheck_3836_ == 0 {
                        v_unused_3837_ = lean_ctor_get(v_m_3805_, 1);
                        lean_dec(v_unused_3837_);
                        v_unused_3838_ = lean_ctor_get(v_m_3805_, 0);
                        lean_dec(v_unused_3838_);
                        v___x_3825_ = v_m_3805_;
                        v_isShared_3826_ = v_isSharedCheck_3836_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_3805_);
                        v___x_3825_ = lean_box(0);
                        v_isShared_3826_ = v_isSharedCheck_3836_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3827_ = lean_box(0);
                v_buckets_x27_3828_ = lean_array_uset(v_buckets_3808_, v___x_3821_, v___x_3827_);
                v___x_3829_ = lean_unsigned_to_nat(1);
                v___x_3830_ = lean_nat_sub(v_size_3807_, v___x_3829_);
                lean_dec(v_size_3807_);
                v___x_3831_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg(v_a_3806_, v_bkt_3822_);
                v___x_3832_ = lean_array_uset(v_buckets_x27_3828_, v___x_3821_, v___x_3831_);
                if v_isShared_3826_ == 0 {
                    lean_ctor_set(v___x_3825_, 1, v___x_3832_);
                    lean_ctor_set(v___x_3825_, 0, v___x_3830_);
                    v___x_3834_ = v___x_3825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3830_);
                    lean_ctor_set(v_reuseFailAlloc_3835_, 1, v___x_3832_);
                    v___x_3834_ = v_reuseFailAlloc_3835_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg___boxed(
    mut v_m_3839_: *mut LeanObject,
    mut v_a_3840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3841_: *mut LeanObject = core::ptr::null_mut();
    v_res_3841_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg(v_m_3839_, v_a_3840_);
    lean_dec(v_a_3840_);
    return v_res_3841_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__2() -> *mut LeanObject
{
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    v___x_3844_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__2;
    v___x_3845_ = lean_unsigned_to_nat(9);
    v___x_3846_ = lean_unsigned_to_nat(641);
    v___x_3847_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__1;
    v___x_3848_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__0;
    v___x_3849_ = l_mkPanicMessageWithDecl(
        v___x_3848_,
        v___x_3847_,
        v___x_3846_,
        v___x_3845_,
        v___x_3844_,
    );
    return v___x_3849_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__5() -> *mut LeanObject
{
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    v___x_3852_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__4;
    v___x_3853_ = lean_unsigned_to_nat(59);
    v___x_3854_ = lean_unsigned_to_nat(67);
    v___x_3855_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__3;
    v___x_3856_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0;
    v___x_3857_ = l_mkPanicMessageWithDecl(
        v___x_3856_,
        v___x_3855_,
        v___x_3854_,
        v___x_3853_,
        v___x_3852_,
    );
    return v___x_3857_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__5(
    mut v_i_3858_: *mut LeanObject,
    mut v_as_3859_: *mut LeanObject,
    mut v___y_3860_: *mut LeanObject,
    mut v___y_3861_: *mut LeanObject,
    mut v___y_3862_: *mut LeanObject,
    mut v___y_3863_: *mut LeanObject,
    mut v___y_3864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: usize = 0;
    let mut v___x_3873_: usize = 0;
    let mut v___x_3874_: u8 = 0;
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3885_: u8 = 0;
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3866_ = lean_array_get_size(v_as_3859_);
                v___x_3867_ = lean_nat_dec_lt(v_i_3858_, v___x_3866_);
                if v___x_3867_ == 0 {
                    lean_dec(v_i_3858_);
                    v___x_3868_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3868_, 0, v_as_3859_);
                    return v___x_3868_;
                } else {
                    v_a_3869_ = lean_array_fget_borrowed(v_as_3859_, v_i_3858_);
                    lean_inc(v_a_3869_);
                    v___x_3870_ = l_Lean_Compiler_LCNF_StructProjCases_visitAlt(
                        v_a_3869_,
                        v___y_3860_,
                        v___y_3861_,
                        v___y_3862_,
                        v___y_3863_,
                        v___y_3864_,
                    );
                    if lean_obj_tag(v___x_3870_) == 0 {
                        v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
                        lean_inc(v_a_3871_);
                        lean_dec_ref_known(v___x_3870_, 1);
                        v___x_3872_ = lean_ptr_addr(v_a_3869_);
                        v___x_3873_ = lean_ptr_addr(v_a_3871_);
                        v___x_3874_ = lean_usize_dec_eq(v___x_3872_, v___x_3873_);
                        if v___x_3874_ == 0 {
                            v___x_3875_ = lean_unsigned_to_nat(1);
                            v___x_3876_ = lean_nat_add(v_i_3858_, v___x_3875_);
                            v___x_3877_ = lean_array_fset(v_as_3859_, v_i_3858_, v_a_3871_);
                            lean_dec(v_i_3858_);
                            v_i_3858_ = v___x_3876_;
                            v_as_3859_ = v___x_3877_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_3871_);
                            v___x_3879_ = lean_unsigned_to_nat(1);
                            v___x_3880_ = lean_nat_add(v_i_3858_, v___x_3879_);
                            lean_dec(v_i_3858_);
                            v_i_3858_ = v___x_3880_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_as_3859_);
                        lean_dec(v_i_3858_);
                        v_a_3882_ = lean_ctor_get(v___x_3870_, 0);
                        v_isSharedCheck_3889_ = (!lean_is_exclusive(v___x_3870_)) as u8;
                        if v_isSharedCheck_3889_ == 0 {
                            v___x_3884_ = v___x_3870_;
                            v_isShared_3885_ = v_isSharedCheck_3889_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3882_);
                            lean_dec(v___x_3870_);
                            v___x_3884_ = lean_box(0);
                            v_isShared_3885_ = v_isSharedCheck_3889_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3885_ == 0 {
                    v___x_3887_ = v___x_3884_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
                    v___x_3887_ = v_reuseFailAlloc_3888_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3887_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__7() -> *mut LeanObject
{
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    v___x_3891_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__6;
    v___x_3892_ = lean_unsigned_to_nat(8);
    v___x_3893_ = lean_unsigned_to_nat(90);
    v___x_3894_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__3;
    v___x_3895_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType_spec__1___redArg___closed__0;
    v___x_3896_ = l_mkPanicMessageWithDecl(
        v___x_3895_,
        v___x_3894_,
        v___x_3893_,
        v___x_3892_,
        v___x_3891_,
    );
    return v___x_3896_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_visitCode(
    mut v_code_3897_: *mut LeanObject,
    mut v_a_3898_: *mut LeanObject,
    mut v_a_3899_: *mut LeanObject,
    mut v_a_3900_: *mut LeanObject,
    mut v_a_3901_: *mut LeanObject,
    mut v_a_3902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: u8 = 0;
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3914_: u8 = 0;
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: u8 = 0;
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: usize = 0;
    let mut v___x_3939_: usize = 0;
    let mut v___x_3940_: u8 = 0;
    let mut v___x_3941_: usize = 0;
    let mut v___x_3942_: usize = 0;
    let mut v___x_3943_: u8 = 0;
    let mut v_a_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: usize = 0;
    let mut v___x_3948_: usize = 0;
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: usize = 0;
    let mut v___x_3951_: usize = 0;
    let mut v___x_3952_: u8 = 0;
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3955_: u8 = 0;
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3961_: u8 = 0;
    let mut v_unused_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3966_: u8 = 0;
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3970_: u8 = 0;
    let mut v_decl_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: u8 = 0;
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3982_: u8 = 0;
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projMap_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projMap_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarMap_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3995_: u8 = 0;
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4003_: u8 = 0;
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projMap_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarMap_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4022_: u8 = 0;
    let mut v_sz_4023_: usize = 0;
    let mut v___x_4024_: usize = 0;
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4036_: u8 = 0;
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projMap_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarMap_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4042_: u8 = 0;
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4053_: u8 = 0;
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4069_: u8 = 0;
    let mut v_a_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4073_: u8 = 0;
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut v_a_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4085_: u8 = 0;
    let mut v_reuseFailAlloc_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4087_: u8 = 0;
    let mut v_isSharedCheck_4088_: u8 = 0;
    let mut v_reuseFailAlloc_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4090_: u8 = 0;
    let mut v_a_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4094_: u8 = 0;
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_isSharedCheck_4099_: u8 = 0;
    let mut v_unused_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4106_: u8 = 0;
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4110_: u8 = 0;
    let mut v_a_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4114_: u8 = 0;
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4118_: u8 = 0;
    let mut v_a_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4122_: u8 = 0;
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4126_: u8 = 0;
    let mut v_isSharedCheck_4127_: u8 = 0;
    let mut v_unused_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: u8 = 0;
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4142_: u8 = 0;
    let mut v___y_4144_: u8 = 0;
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4147_: u8 = 0;
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4154_: u8 = 0;
    let mut v_unused_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: usize = 0;
    let mut v___x_4161_: usize = 0;
    let mut v___x_4162_: u8 = 0;
    let mut v___x_4163_: usize = 0;
    let mut v___x_4164_: usize = 0;
    let mut v___x_4165_: u8 = 0;
    let mut v_isSharedCheck_4166_: u8 = 0;
    let mut v_a_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4170_: u8 = 0;
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4174_: u8 = 0;
    let mut v_a_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4178_: u8 = 0;
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4182_: u8 = 0;
    let mut v_fvarId_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4187_: usize = 0;
    let mut v___x_4188_: usize = 0;
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4193_: u8 = 0;
    let mut v___y_4195_: u8 = 0;
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4198_: u8 = 0;
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4205_: u8 = 0;
    let mut v_unused_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: u8 = 0;
    let mut v___x_4212_: usize = 0;
    let mut v___x_4213_: usize = 0;
    let mut v___x_4214_: u8 = 0;
    let mut v_isSharedCheck_4215_: u8 = 0;
    let mut v_a_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4219_: u8 = 0;
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4223_: u8 = 0;
    let mut v_a_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4227_: u8 = 0;
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4231_: u8 = 0;
    let mut v_cases_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4239_: u8 = 0;
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4244_: u8 = 0;
    let mut v___y_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4256_: u8 = 0;
    let mut v___x_4257_: u8 = 0;
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: usize = 0;
    let mut v___x_4269_: usize = 0;
    let mut v___x_4270_: u8 = 0;
    let mut v___x_4271_: usize = 0;
    let mut v___x_4272_: u8 = 0;
    let mut v_a_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4276_: u8 = 0;
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4280_: u8 = 0;
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: u8 = 0;
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4291_: u8 = 0;
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projMap_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: u8 = 0;
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4302_: usize = 0;
    let mut v___x_4303_: usize = 0;
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4309_: u8 = 0;
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4313_: u8 = 0;
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projMap_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarMap_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4319_: u8 = 0;
    let mut v_sz_4320_: usize = 0;
    let mut v___x_4321_: usize = 0;
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4331_: u8 = 0;
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_projMap_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarMap_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4337_: u8 = 0;
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4353_: u8 = 0;
    let mut v___x_4354_: u8 = 0;
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: usize = 0;
    let mut v___x_4357_: usize = 0;
    let mut v___x_4358_: u8 = 0;
    let mut v___x_4359_: usize = 0;
    let mut v___x_4360_: u8 = 0;
    let mut v_reuseFailAlloc_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4363_: u8 = 0;
    let mut v_isSharedCheck_4364_: u8 = 0;
    let mut v_reuseFailAlloc_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4366_: u8 = 0;
    let mut v_isSharedCheck_4367_: u8 = 0;
    let mut v_isSharedCheck_4368_: u8 = 0;
    let mut v_a_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4372_: u8 = 0;
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4376_: u8 = 0;
    let mut v_isSharedCheck_4377_: u8 = 0;
    let mut v_fvarId_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4383_: u8 = 0;
    let mut v___x_4384_: u8 = 0;
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4394_: u8 = 0;
    let mut v_unused_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4399_: u8 = 0;
    let mut v_a_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4403_: u8 = 0;
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4407_: u8 = 0;
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_3897_) {
                0 => {
                    v_decl_3971_ = lean_ctor_get(v_code_3897_, 0);
                    lean_inc_ref(v_decl_3971_);
                    v_value_3972_ = lean_ctor_get(v_decl_3971_, 3);
                    if lean_obj_tag(v_value_3972_) == 2 {
                        v_k_3973_ = lean_ctor_get(v_code_3897_, 1);
                        lean_inc_ref(v_k_3973_);
                        lean_dec_ref_known(v_code_3897_, 2);
                        v_fvarId_3974_ = lean_ctor_get(v_decl_3971_, 0);
                        lean_inc(v_fvarId_3974_);
                        v_typeName_3975_ = lean_ctor_get(v_value_3972_, 0);
                        lean_inc(v_typeName_3975_);
                        v_idx_3976_ = lean_ctor_get(v_value_3972_, 1);
                        lean_inc(v_idx_3976_);
                        v_struct_3977_ = lean_ctor_get(v_value_3972_, 2);
                        lean_inc(v_struct_3977_);
                        v___x_3978_ = 0;
                        v___x_3979_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(
                            v___x_3978_,
                            v_decl_3971_,
                            v_a_3900_,
                        );
                        v_isSharedCheck_4127_ = (!lean_is_exclusive(v_decl_3971_)) as u8;
                        if v_isSharedCheck_4127_ == 0 {
                            v_unused_4128_ = lean_ctor_get(v_decl_3971_, 3);
                            lean_dec(v_unused_4128_);
                            v_unused_4129_ = lean_ctor_get(v_decl_3971_, 2);
                            lean_dec(v_unused_4129_);
                            v_unused_4130_ = lean_ctor_get(v_decl_3971_, 1);
                            lean_dec(v_unused_4130_);
                            v_unused_4131_ = lean_ctor_get(v_decl_3971_, 0);
                            lean_dec(v_unused_4131_);
                            v___x_3981_ = v_decl_3971_;
                            v_isShared_3982_ = v_isSharedCheck_4127_;
                            state = 8;
                            continue;
                        } else {
                            lean_dec(v_decl_3971_);
                            v___x_3981_ = lean_box(0);
                            v_isShared_3982_ = v_isSharedCheck_4127_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_k_4132_ = lean_ctor_get(v_code_3897_, 1);
                        lean_inc(v_value_3972_);
                        v___x_4133_ = l_Lean_Compiler_LCNF_StructProjCases_visitLetValue(
                            v_value_3972_,
                            v_a_3898_,
                            v_a_3899_,
                            v_a_3900_,
                            v_a_3901_,
                            v_a_3902_,
                        );
                        if lean_obj_tag(v___x_4133_) == 0 {
                            v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
                            lean_inc(v_a_4134_);
                            lean_dec_ref_known(v___x_4133_, 1);
                            v___x_4135_ = 0;
                            lean_inc_ref(v_decl_3971_);
                            v___x_4136_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                                v___x_4135_,
                                v_decl_3971_,
                                v_a_4134_,
                                v_a_3900_,
                            );
                            if lean_obj_tag(v___x_4136_) == 0 {
                                v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
                                lean_inc(v_a_4137_);
                                lean_dec_ref_known(v___x_4136_, 1);
                                lean_inc_ref(v_k_4132_);
                                v___x_4138_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(
                                    v_k_4132_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_,
                                    v_a_3902_,
                                );
                                if lean_obj_tag(v___x_4138_) == 0 {
                                    v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
                                    v_isSharedCheck_4166_ = (!lean_is_exclusive(v___x_4138_)) as u8;
                                    if v_isSharedCheck_4166_ == 0 {
                                        v___x_4141_ = v___x_4138_;
                                        v_isShared_4142_ = v_isSharedCheck_4166_;
                                        state = 34;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4139_);
                                        lean_dec(v___x_4138_);
                                        v___x_4141_ = lean_box(0);
                                        v_isShared_4142_ = v_isSharedCheck_4166_;
                                        state = 34;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_4137_);
                                    lean_dec_ref_known(v_code_3897_, 2);
                                    lean_dec_ref(v_decl_3971_);
                                    return v___x_4138_;
                                }
                            } else {
                                lean_dec_ref_known(v_code_3897_, 2);
                                lean_dec_ref(v_decl_3971_);
                                v_a_4167_ = lean_ctor_get(v___x_4136_, 0);
                                v_isSharedCheck_4174_ = (!lean_is_exclusive(v___x_4136_)) as u8;
                                if v_isSharedCheck_4174_ == 0 {
                                    v___x_4169_ = v___x_4136_;
                                    v_isShared_4170_ = v_isSharedCheck_4174_;
                                    state = 40;
                                    continue;
                                } else {
                                    lean_inc(v_a_4167_);
                                    lean_dec(v___x_4136_);
                                    v___x_4169_ = lean_box(0);
                                    v_isShared_4170_ = v_isSharedCheck_4174_;
                                    state = 40;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_code_3897_, 2);
                            lean_dec_ref(v_decl_3971_);
                            v_a_4175_ = lean_ctor_get(v___x_4133_, 0);
                            v_isSharedCheck_4182_ = (!lean_is_exclusive(v___x_4133_)) as u8;
                            if v_isSharedCheck_4182_ == 0 {
                                v___x_4177_ = v___x_4133_;
                                v_isShared_4178_ = v_isSharedCheck_4182_;
                                state = 42;
                                continue;
                            } else {
                                lean_inc(v_a_4175_);
                                lean_dec(v___x_4133_);
                                v___x_4177_ = lean_box(0);
                                v_isShared_4178_ = v_isSharedCheck_4182_;
                                state = 42;
                                continue;
                            }
                        }
                    }
                }
                3 => {
                    v_fvarId_4183_ = lean_ctor_get(v_code_3897_, 0);
                    v_args_4184_ = lean_ctor_get(v_code_3897_, 1);
                    lean_inc(v_fvarId_4183_);
                    v___x_4185_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(
                        v_fvarId_4183_,
                        v_a_3898_,
                    );
                    if lean_obj_tag(v___x_4185_) == 0 {
                        v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
                        lean_inc(v_a_4186_);
                        lean_dec_ref_known(v___x_4185_, 1);
                        v_sz_4187_ = lean_array_size(v_args_4184_);
                        v___x_4188_ = 0usize;
                        lean_inc_ref(v_args_4184_);
                        v___x_4189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitLetValue_spec__1___redArg(v_sz_4187_, v___x_4188_, v_args_4184_, v_a_3898_);
                        if lean_obj_tag(v___x_4189_) == 0 {
                            v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
                            v_isSharedCheck_4215_ = (!lean_is_exclusive(v___x_4189_)) as u8;
                            if v_isSharedCheck_4215_ == 0 {
                                v___x_4192_ = v___x_4189_;
                                v_isShared_4193_ = v_isSharedCheck_4215_;
                                state = 44;
                                continue;
                            } else {
                                lean_inc(v_a_4190_);
                                lean_dec(v___x_4189_);
                                v___x_4192_ = lean_box(0);
                                v_isShared_4193_ = v_isSharedCheck_4215_;
                                state = 44;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4186_);
                            lean_dec_ref_known(v_code_3897_, 2);
                            v_a_4216_ = lean_ctor_get(v___x_4189_, 0);
                            v_isSharedCheck_4223_ = (!lean_is_exclusive(v___x_4189_)) as u8;
                            if v_isSharedCheck_4223_ == 0 {
                                v___x_4218_ = v___x_4189_;
                                v_isShared_4219_ = v_isSharedCheck_4223_;
                                state = 50;
                                continue;
                            } else {
                                lean_inc(v_a_4216_);
                                lean_dec(v___x_4189_);
                                v___x_4218_ = lean_box(0);
                                v_isShared_4219_ = v_isSharedCheck_4223_;
                                state = 50;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_code_3897_, 2);
                        v_a_4224_ = lean_ctor_get(v___x_4185_, 0);
                        v_isSharedCheck_4231_ = (!lean_is_exclusive(v___x_4185_)) as u8;
                        if v_isSharedCheck_4231_ == 0 {
                            v___x_4226_ = v___x_4185_;
                            v_isShared_4227_ = v_isSharedCheck_4231_;
                            state = 52;
                            continue;
                        } else {
                            lean_inc(v_a_4224_);
                            lean_dec(v___x_4185_);
                            v___x_4226_ = lean_box(0);
                            v_isShared_4227_ = v_isSharedCheck_4231_;
                            state = 52;
                            continue;
                        }
                    }
                }
                4 => {
                    v_cases_4232_ = lean_ctor_get(v_code_3897_, 0);
                    lean_inc_ref(v_cases_4232_);
                    v_typeName_4233_ = lean_ctor_get(v_cases_4232_, 0);
                    v_resultType_4234_ = lean_ctor_get(v_cases_4232_, 1);
                    v_discr_4235_ = lean_ctor_get(v_cases_4232_, 2);
                    v_alts_4236_ = lean_ctor_get(v_cases_4232_, 3);
                    v_isSharedCheck_4377_ = (!lean_is_exclusive(v_cases_4232_)) as u8;
                    if v_isSharedCheck_4377_ == 0 {
                        v___x_4238_ = v_cases_4232_;
                        v_isShared_4239_ = v_isSharedCheck_4377_;
                        state = 54;
                        continue;
                    } else {
                        lean_inc(v_alts_4236_);
                        lean_inc(v_discr_4235_);
                        lean_inc(v_resultType_4234_);
                        lean_inc(v_typeName_4233_);
                        lean_dec(v_cases_4232_);
                        v___x_4238_ = lean_box(0);
                        v_isShared_4239_ = v_isSharedCheck_4377_;
                        state = 54;
                        continue;
                    }
                }
                5 => {
                    v_fvarId_4378_ = lean_ctor_get(v_code_3897_, 0);
                    lean_inc(v_fvarId_4378_);
                    v___x_4379_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(
                        v_fvarId_4378_,
                        v_a_3898_,
                    );
                    if lean_obj_tag(v___x_4379_) == 0 {
                        v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
                        v_isSharedCheck_4399_ = (!lean_is_exclusive(v___x_4379_)) as u8;
                        if v_isSharedCheck_4399_ == 0 {
                            v___x_4382_ = v___x_4379_;
                            v_isShared_4383_ = v_isSharedCheck_4399_;
                            state = 77;
                            continue;
                        } else {
                            lean_inc(v_a_4380_);
                            lean_dec(v___x_4379_);
                            v___x_4382_ = lean_box(0);
                            v_isShared_4383_ = v_isSharedCheck_4399_;
                            state = 77;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_3897_, 1);
                        v_a_4400_ = lean_ctor_get(v___x_4379_, 0);
                        v_isSharedCheck_4407_ = (!lean_is_exclusive(v___x_4379_)) as u8;
                        if v_isSharedCheck_4407_ == 0 {
                            v___x_4402_ = v___x_4379_;
                            v_isShared_4403_ = v_isSharedCheck_4407_;
                            state = 82;
                            continue;
                        } else {
                            lean_inc(v_a_4400_);
                            lean_dec(v___x_4379_);
                            v___x_4402_ = lean_box(0);
                            v_isShared_4403_ = v_isSharedCheck_4407_;
                            state = 82;
                            continue;
                        }
                    }
                }
                6 => {
                    v___x_4408_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4408_, 0, v_code_3897_);
                    return v___x_4408_;
                }
                _ => {
                    v_decl_4409_ = lean_ctor_get(v_code_3897_, 0);
                    v_k_4410_ = lean_ctor_get(v_code_3897_, 1);
                    lean_inc_ref(v_k_4410_);
                    lean_inc_ref(v_decl_4409_);
                    v_decl_3919_ = v_decl_4409_;
                    v_k_3920_ = v_k_4410_;
                    v___y_3921_ = v_a_3898_;
                    v___y_3922_ = v_a_3899_;
                    v___y_3923_ = v_a_3900_;
                    v___y_3924_ = v_a_3901_;
                    v___y_3925_ = v_a_3902_;
                    state = 3;
                    continue;
                }
            },
            1 => {
                if v___y_3907_ == 0 {
                    lean_dec_ref(v_code_3897_);
                    v___x_3908_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3908_, 0, v___y_3906_);
                    lean_ctor_set(v___x_3908_, 1, v___y_3905_);
                    v___x_3909_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3909_, 0, v___x_3908_);
                    return v___x_3909_;
                } else {
                    lean_dec_ref(v___y_3906_);
                    lean_dec_ref(v___y_3905_);
                    v___x_3910_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3910_, 0, v_code_3897_);
                    return v___x_3910_;
                }
            }
            2 => {
                if v___y_3914_ == 0 {
                    lean_dec_ref(v_code_3897_);
                    v___x_3915_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3915_, 0, v___y_3913_);
                    lean_ctor_set(v___x_3915_, 1, v___y_3912_);
                    v___x_3916_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3916_, 0, v___x_3915_);
                    return v___x_3916_;
                } else {
                    lean_dec_ref(v___y_3913_);
                    lean_dec_ref(v___y_3912_);
                    v___x_3917_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3917_, 0, v_code_3897_);
                    return v___x_3917_;
                }
            }
            3 => {
                v_params_3926_ = lean_ctor_get(v_decl_3919_, 2);
                lean_inc_ref(v_params_3926_);
                v_type_3927_ = lean_ctor_get(v_decl_3919_, 3);
                lean_inc_ref(v_type_3927_);
                v_value_3928_ = lean_ctor_get(v_decl_3919_, 4);
                lean_inc_ref(v_value_3928_);
                v___x_3929_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(
                    v_value_3928_,
                    v___y_3921_,
                    v___y_3922_,
                    v___y_3923_,
                    v___y_3924_,
                    v___y_3925_,
                );
                if lean_obj_tag(v___x_3929_) == 0 {
                    v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
                    lean_inc(v_a_3930_);
                    lean_dec_ref_known(v___x_3929_, 1);
                    v___x_3931_ = 0;
                    v___x_3932_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3931_, v_decl_3919_, v_type_3927_, v_params_3926_, v_a_3930_, v___y_3923_);
                    if lean_obj_tag(v___x_3932_) == 0 {
                        v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
                        lean_inc(v_a_3933_);
                        lean_dec_ref_known(v___x_3932_, 1);
                        v___x_3934_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(
                            v_k_3920_,
                            v___y_3921_,
                            v___y_3922_,
                            v___y_3923_,
                            v___y_3924_,
                            v___y_3925_,
                        );
                        if lean_obj_tag(v___x_3934_) == 0 {
                            match lean_obj_tag(v_code_3897_) {
                                1 => {
                                    v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
                                    lean_inc(v_a_3935_);
                                    lean_dec_ref_known(v___x_3934_, 1);
                                    v_decl_3936_ = lean_ctor_get(v_code_3897_, 0);
                                    v_k_3937_ = lean_ctor_get(v_code_3897_, 1);
                                    v___x_3938_ = lean_ptr_addr(v_k_3937_);
                                    v___x_3939_ = lean_ptr_addr(v_a_3935_);
                                    v___x_3940_ = lean_usize_dec_eq(v___x_3938_, v___x_3939_);
                                    if v___x_3940_ == 0 {
                                        v___y_3905_ = v_a_3935_;
                                        v___y_3906_ = v_a_3933_;
                                        v___y_3907_ = v___x_3940_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3941_ = lean_ptr_addr(v_decl_3936_);
                                        v___x_3942_ = lean_ptr_addr(v_a_3933_);
                                        v___x_3943_ = lean_usize_dec_eq(v___x_3941_, v___x_3942_);
                                        v___y_3905_ = v_a_3935_;
                                        v___y_3906_ = v_a_3933_;
                                        v___y_3907_ = v___x_3943_;
                                        state = 1;
                                        continue;
                                    }
                                }
                                2 => {
                                    v_a_3944_ = lean_ctor_get(v___x_3934_, 0);
                                    lean_inc(v_a_3944_);
                                    lean_dec_ref_known(v___x_3934_, 1);
                                    v_decl_3945_ = lean_ctor_get(v_code_3897_, 0);
                                    v_k_3946_ = lean_ctor_get(v_code_3897_, 1);
                                    v___x_3947_ = lean_ptr_addr(v_k_3946_);
                                    v___x_3948_ = lean_ptr_addr(v_a_3944_);
                                    v___x_3949_ = lean_usize_dec_eq(v___x_3947_, v___x_3948_);
                                    if v___x_3949_ == 0 {
                                        v___y_3912_ = v_a_3944_;
                                        v___y_3913_ = v_a_3933_;
                                        v___y_3914_ = v___x_3949_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_3950_ = lean_ptr_addr(v_decl_3945_);
                                        v___x_3951_ = lean_ptr_addr(v_a_3933_);
                                        v___x_3952_ = lean_usize_dec_eq(v___x_3950_, v___x_3951_);
                                        v___y_3912_ = v_a_3944_;
                                        v___y_3913_ = v_a_3933_;
                                        v___y_3914_ = v___x_3952_;
                                        state = 2;
                                        continue;
                                    }
                                }
                                _ => {
                                    lean_dec(v_a_3933_);
                                    lean_dec_ref(v_code_3897_);
                                    v_isSharedCheck_3961_ = (!lean_is_exclusive(v___x_3934_)) as u8;
                                    if v_isSharedCheck_3961_ == 0 {
                                        v_unused_3962_ = lean_ctor_get(v___x_3934_, 0);
                                        lean_dec(v_unused_3962_);
                                        v___x_3954_ = v___x_3934_;
                                        v_isShared_3955_ = v_isSharedCheck_3961_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_dec(v___x_3934_);
                                        v___x_3954_ = lean_box(0);
                                        v_isShared_3955_ = v_isSharedCheck_3961_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_3933_);
                            lean_dec_ref(v_code_3897_);
                            return v___x_3934_;
                        }
                    } else {
                        lean_dec_ref(v_k_3920_);
                        lean_dec_ref(v_code_3897_);
                        v_a_3963_ = lean_ctor_get(v___x_3932_, 0);
                        v_isSharedCheck_3970_ = (!lean_is_exclusive(v___x_3932_)) as u8;
                        if v_isSharedCheck_3970_ == 0 {
                            v___x_3965_ = v___x_3932_;
                            v_isShared_3966_ = v_isSharedCheck_3970_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3963_);
                            lean_dec(v___x_3932_);
                            v___x_3965_ = lean_box(0);
                            v_isShared_3966_ = v_isSharedCheck_3970_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_3927_);
                    lean_dec_ref(v_params_3926_);
                    lean_dec_ref(v_k_3920_);
                    lean_dec_ref(v_decl_3919_);
                    lean_dec_ref(v_code_3897_);
                    return v___x_3929_;
                }
            }
            4 => {
                v___x_3956_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__2,
                );
                v___x_3957_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__0(
                    v___x_3956_,
                );
                if v_isShared_3955_ == 0 {
                    lean_ctor_set(v___x_3954_, 0, v___x_3957_);
                    v___x_3959_ = v___x_3954_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3957_);
                    v___x_3959_ = v_reuseFailAlloc_3960_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3959_;
            }
            6 => {
                if v_isShared_3966_ == 0 {
                    v___x_3968_ = v___x_3965_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
                    v___x_3968_ = v_reuseFailAlloc_3969_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3968_;
            }
            8 => {
                if lean_obj_tag(v___x_3979_) == 0 {
                    lean_dec_ref_known(v___x_3979_, 1);
                    v___x_3983_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(
                        v_struct_3977_,
                        v_a_3898_,
                    );
                    if lean_obj_tag(v___x_3983_) == 0 {
                        v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
                        lean_inc(v_a_3984_);
                        lean_dec_ref_known(v___x_3983_, 1);
                        v___x_3985_ = lean_st_ref_get(v_a_3898_);
                        v_projMap_3986_ = lean_ctor_get(v___x_3985_, 0);
                        lean_inc_ref(v_projMap_3986_);
                        lean_dec(v___x_3985_);
                        v___x_3987_ = lean_box(0);
                        v___x_3988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(v_projMap_3986_, v_a_3984_);
                        lean_dec_ref(v_projMap_3986_);
                        if lean_obj_tag(v___x_3988_) == 1 {
                            lean_dec(v_a_3984_);
                            lean_del_object(v___x_3981_);
                            lean_dec(v_typeName_3975_);
                            v_val_3989_ = lean_ctor_get(v___x_3988_, 0);
                            lean_inc(v_val_3989_);
                            lean_dec_ref_known(v___x_3988_, 1);
                            v___x_3990_ = lean_st_ref_take(v_a_3898_);
                            v_projMap_3991_ = lean_ctor_get(v___x_3990_, 0);
                            v_fvarMap_3992_ = lean_ctor_get(v___x_3990_, 1);
                            v_isSharedCheck_4003_ = (!lean_is_exclusive(v___x_3990_)) as u8;
                            if v_isSharedCheck_4003_ == 0 {
                                v___x_3994_ = v___x_3990_;
                                v_isShared_3995_ = v_isSharedCheck_4003_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_fvarMap_3992_);
                                lean_inc(v_projMap_3991_);
                                lean_dec(v___x_3990_);
                                v___x_3994_ = lean_box(0);
                                v_isShared_3995_ = v_isSharedCheck_4003_;
                                state = 9;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3988_);
                            lean_inc(v_typeName_3975_);
                            v___x_4004_ =
                                l_Lean_Compiler_LCNF_StructProjCases_findStructCtorInfo_x3f(
                                    v_typeName_3975_,
                                    v_a_3901_,
                                    v_a_3902_,
                                );
                            if lean_obj_tag(v___x_4004_) == 0 {
                                v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
                                lean_inc(v_a_4005_);
                                lean_dec_ref_known(v___x_4004_, 1);
                                if lean_obj_tag(v_a_4005_) == 1 {
                                    v_val_4006_ = lean_ctor_get(v_a_4005_, 0);
                                    lean_inc(v_val_4006_);
                                    lean_dec_ref_known(v_a_4005_, 1);
                                    v_toConstantVal_4007_ = lean_ctor_get(v_val_4006_, 0);
                                    lean_inc_ref(v_toConstantVal_4007_);
                                    v_numParams_4008_ = lean_ctor_get(v_val_4006_, 3);
                                    lean_inc(v_numParams_4008_);
                                    v_numFields_4009_ = lean_ctor_get(v_val_4006_, 4);
                                    lean_inc(v_numFields_4009_);
                                    lean_dec(v_val_4006_);
                                    v_name_4010_ = lean_ctor_get(v_toConstantVal_4007_, 0);
                                    v_type_4011_ = lean_ctor_get(v_toConstantVal_4007_, 2);
                                    v_isSharedCheck_4099_ =
                                        (!lean_is_exclusive(v_toConstantVal_4007_)) as u8;
                                    if v_isSharedCheck_4099_ == 0 {
                                        v_unused_4100_ = lean_ctor_get(v_toConstantVal_4007_, 1);
                                        lean_dec(v_unused_4100_);
                                        v___x_4013_ = v_toConstantVal_4007_;
                                        v_isShared_4014_ = v_isSharedCheck_4099_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_type_4011_);
                                        lean_inc(v_name_4010_);
                                        lean_dec(v_toConstantVal_4007_);
                                        v___x_4013_ = lean_box(0);
                                        v_isShared_4014_ = v_isSharedCheck_4099_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_4005_);
                                    lean_dec(v_a_3984_);
                                    lean_del_object(v___x_3981_);
                                    lean_dec(v_idx_3976_);
                                    lean_dec(v_typeName_3975_);
                                    lean_dec(v_fvarId_3974_);
                                    lean_dec_ref(v_k_3973_);
                                    v___x_4101_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__5), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__5_once), _init_l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__5);
                                    v___x_4102_ = l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4(v___x_4101_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                                    return v___x_4102_;
                                }
                            } else {
                                lean_dec(v_a_3984_);
                                lean_del_object(v___x_3981_);
                                lean_dec(v_idx_3976_);
                                lean_dec(v_typeName_3975_);
                                lean_dec(v_fvarId_3974_);
                                lean_dec_ref(v_k_3973_);
                                v_a_4103_ = lean_ctor_get(v___x_4004_, 0);
                                v_isSharedCheck_4110_ = (!lean_is_exclusive(v___x_4004_)) as u8;
                                if v_isSharedCheck_4110_ == 0 {
                                    v___x_4105_ = v___x_4004_;
                                    v_isShared_4106_ = v_isSharedCheck_4110_;
                                    state = 28;
                                    continue;
                                } else {
                                    lean_inc(v_a_4103_);
                                    lean_dec(v___x_4004_);
                                    v___x_4105_ = lean_box(0);
                                    v_isShared_4106_ = v_isSharedCheck_4110_;
                                    state = 28;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_3981_);
                        lean_dec(v_idx_3976_);
                        lean_dec(v_typeName_3975_);
                        lean_dec(v_fvarId_3974_);
                        lean_dec_ref(v_k_3973_);
                        v_a_4111_ = lean_ctor_get(v___x_3983_, 0);
                        v_isSharedCheck_4118_ = (!lean_is_exclusive(v___x_3983_)) as u8;
                        if v_isSharedCheck_4118_ == 0 {
                            v___x_4113_ = v___x_3983_;
                            v_isShared_4114_ = v_isSharedCheck_4118_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_4111_);
                            lean_dec(v___x_3983_);
                            v___x_4113_ = lean_box(0);
                            v_isShared_4114_ = v_isSharedCheck_4118_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3981_);
                    lean_dec(v_struct_3977_);
                    lean_dec(v_idx_3976_);
                    lean_dec(v_typeName_3975_);
                    lean_dec(v_fvarId_3974_);
                    lean_dec_ref(v_k_3973_);
                    v_a_4119_ = lean_ctor_get(v___x_3979_, 0);
                    v_isSharedCheck_4126_ = (!lean_is_exclusive(v___x_3979_)) as u8;
                    if v_isSharedCheck_4126_ == 0 {
                        v___x_4121_ = v___x_3979_;
                        v_isShared_4122_ = v_isSharedCheck_4126_;
                        state = 32;
                        continue;
                    } else {
                        lean_inc(v_a_4119_);
                        lean_dec(v___x_3979_);
                        v___x_4121_ = lean_box(0);
                        v_isShared_4122_ = v_isSharedCheck_4126_;
                        state = 32;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3996_ = lean_array_get(v___x_3987_, v_val_3989_, v_idx_3976_);
                lean_dec(v_idx_3976_);
                lean_dec(v_val_3989_);
                v___x_3997_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(v_fvarMap_3992_, v_fvarId_3974_, v___x_3996_);
                if v_isShared_3995_ == 0 {
                    lean_ctor_set(v___x_3994_, 1, v___x_3997_);
                    v___x_3999_ = v___x_3994_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_projMap_3991_);
                    lean_ctor_set(v_reuseFailAlloc_4002_, 1, v___x_3997_);
                    v___x_3999_ = v_reuseFailAlloc_4002_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4000_ = lean_st_ref_set(v_a_3898_, v___x_3999_);
                v_code_3897_ = v_k_3973_;
                state = 0;
                continue;
            }
            11 => {
                v___x_4015_ = l_Lean_Compiler_LCNF_StructProjCases_mkFieldParamsForCtorType(
                    v_type_4011_,
                    v_numParams_4008_,
                    v_numFields_4009_,
                    v_a_3899_,
                    v_a_3900_,
                    v_a_3901_,
                    v_a_3902_,
                );
                lean_dec(v_numFields_4009_);
                lean_dec(v_numParams_4008_);
                if lean_obj_tag(v___x_4015_) == 0 {
                    v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
                    lean_inc(v_a_4016_);
                    lean_dec_ref_known(v___x_4015_, 1);
                    v___x_4017_ = lean_st_ref_take(v_a_3898_);
                    v_projMap_4018_ = lean_ctor_get(v___x_4017_, 0);
                    v_fvarMap_4019_ = lean_ctor_get(v___x_4017_, 1);
                    v_isSharedCheck_4090_ = (!lean_is_exclusive(v___x_4017_)) as u8;
                    if v_isSharedCheck_4090_ == 0 {
                        v___x_4021_ = v___x_4017_;
                        v_isShared_4022_ = v_isSharedCheck_4090_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_fvarMap_4019_);
                        lean_inc(v_projMap_4018_);
                        lean_dec(v___x_4017_);
                        v___x_4021_ = lean_box(0);
                        v_isShared_4022_ = v_isSharedCheck_4090_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4013_);
                    lean_dec(v_name_4010_);
                    lean_dec(v_a_3984_);
                    lean_del_object(v___x_3981_);
                    lean_dec(v_idx_3976_);
                    lean_dec(v_typeName_3975_);
                    lean_dec(v_fvarId_3974_);
                    lean_dec_ref(v_k_3973_);
                    v_a_4091_ = lean_ctor_get(v___x_4015_, 0);
                    v_isSharedCheck_4098_ = (!lean_is_exclusive(v___x_4015_)) as u8;
                    if v_isSharedCheck_4098_ == 0 {
                        v___x_4093_ = v___x_4015_;
                        v_isShared_4094_ = v_isSharedCheck_4098_;
                        state = 26;
                        continue;
                    } else {
                        lean_inc(v_a_4091_);
                        lean_dec(v___x_4015_);
                        v___x_4093_ = lean_box(0);
                        v_isShared_4094_ = v_isSharedCheck_4098_;
                        state = 26;
                        continue;
                    }
                }
            }
            12 => {
                v_sz_4023_ = lean_array_size(v_a_4016_);
                v___x_4024_ = 0usize;
                lean_inc(v_a_4016_);
                v___x_4025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__2(v_sz_4023_, v___x_4024_, v_a_4016_);
                lean_inc_ref(v___x_4025_);
                lean_inc(v_a_3984_);
                v___x_4026_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(v_projMap_4018_, v_a_3984_, v___x_4025_);
                v___x_4027_ = lean_array_get(v___x_3987_, v___x_4025_, v_idx_3976_);
                lean_dec(v_idx_3976_);
                lean_dec_ref(v___x_4025_);
                v___x_4028_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(v_fvarMap_4019_, v_fvarId_3974_, v___x_4027_);
                if v_isShared_4022_ == 0 {
                    lean_ctor_set(v___x_4021_, 1, v___x_4028_);
                    lean_ctor_set(v___x_4021_, 0, v___x_4026_);
                    v___x_4030_ = v___x_4021_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4026_);
                    lean_ctor_set(v_reuseFailAlloc_4089_, 1, v___x_4028_);
                    v___x_4030_ = v_reuseFailAlloc_4089_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4031_ = lean_st_ref_set(v_a_3898_, v___x_4030_);
                v___x_4032_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(
                    v_k_3973_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_,
                );
                if lean_obj_tag(v___x_4032_) == 0 {
                    v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
                    v_isSharedCheck_4088_ = (!lean_is_exclusive(v___x_4032_)) as u8;
                    if v_isSharedCheck_4088_ == 0 {
                        v___x_4035_ = v___x_4032_;
                        v_isShared_4036_ = v_isSharedCheck_4088_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_4033_);
                        lean_dec(v___x_4032_);
                        v___x_4035_ = lean_box(0);
                        v_isShared_4036_ = v_isSharedCheck_4088_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4016_);
                    lean_del_object(v___x_4013_);
                    lean_dec(v_name_4010_);
                    lean_dec(v_a_3984_);
                    lean_del_object(v___x_3981_);
                    lean_dec(v_typeName_3975_);
                    return v___x_4032_;
                }
            }
            14 => {
                v___x_4037_ = lean_st_ref_take(v_a_3898_);
                v_projMap_4038_ = lean_ctor_get(v___x_4037_, 0);
                v_fvarMap_4039_ = lean_ctor_get(v___x_4037_, 1);
                v_isSharedCheck_4087_ = (!lean_is_exclusive(v___x_4037_)) as u8;
                if v_isSharedCheck_4087_ == 0 {
                    v___x_4041_ = v___x_4037_;
                    v_isShared_4042_ = v_isSharedCheck_4087_;
                    state = 15;
                    continue;
                } else {
                    lean_inc(v_fvarMap_4039_);
                    lean_inc(v_projMap_4038_);
                    lean_dec(v___x_4037_);
                    v___x_4041_ = lean_box(0);
                    v_isShared_4042_ = v_isSharedCheck_4087_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4043_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg(v_projMap_4038_, v_a_3984_);
                if v_isShared_4042_ == 0 {
                    lean_ctor_set(v___x_4041_, 0, v___x_4043_);
                    v___x_4045_ = v___x_4041_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4043_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 1, v_fvarMap_4039_);
                    v___x_4045_ = v_reuseFailAlloc_4086_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4046_ = lean_st_ref_set(v_a_3898_, v___x_4045_);
                lean_inc(v_a_4033_);
                v___x_4047_ = l_Lean_Compiler_LCNF_Code_inferType(
                    v___x_3978_,
                    v_a_4033_,
                    v_a_3899_,
                    v_a_3900_,
                    v_a_3901_,
                    v_a_3902_,
                );
                if lean_obj_tag(v___x_4047_) == 0 {
                    v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
                    lean_inc(v_a_4048_);
                    lean_dec_ref_known(v___x_4047_, 1);
                    v___x_4049_ = l_Lean_Compiler_LCNF_toMonoType(v_a_4048_, v_a_3901_, v_a_3902_);
                    if lean_obj_tag(v___x_4049_) == 0 {
                        v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
                        v_isSharedCheck_4069_ = (!lean_is_exclusive(v___x_4049_)) as u8;
                        if v_isSharedCheck_4069_ == 0 {
                            v___x_4052_ = v___x_4049_;
                            v_isShared_4053_ = v_isSharedCheck_4069_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_4050_);
                            lean_dec(v___x_4049_);
                            v___x_4052_ = lean_box(0);
                            v_isShared_4053_ = v_isSharedCheck_4069_;
                            state = 17;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4035_);
                        lean_dec(v_a_4033_);
                        lean_dec(v_a_4016_);
                        lean_del_object(v___x_4013_);
                        lean_dec(v_name_4010_);
                        lean_dec(v_a_3984_);
                        lean_del_object(v___x_3981_);
                        lean_dec(v_typeName_3975_);
                        v_a_4070_ = lean_ctor_get(v___x_4049_, 0);
                        v_isSharedCheck_4077_ = (!lean_is_exclusive(v___x_4049_)) as u8;
                        if v_isSharedCheck_4077_ == 0 {
                            v___x_4072_ = v___x_4049_;
                            v_isShared_4073_ = v_isSharedCheck_4077_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_4070_);
                            lean_dec(v___x_4049_);
                            v___x_4072_ = lean_box(0);
                            v_isShared_4073_ = v_isSharedCheck_4077_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4035_);
                    lean_dec(v_a_4033_);
                    lean_dec(v_a_4016_);
                    lean_del_object(v___x_4013_);
                    lean_dec(v_name_4010_);
                    lean_dec(v_a_3984_);
                    lean_del_object(v___x_3981_);
                    lean_dec(v_typeName_3975_);
                    v_a_4078_ = lean_ctor_get(v___x_4047_, 0);
                    v_isSharedCheck_4085_ = (!lean_is_exclusive(v___x_4047_)) as u8;
                    if v_isSharedCheck_4085_ == 0 {
                        v___x_4080_ = v___x_4047_;
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_4078_);
                        lean_dec(v___x_4047_);
                        v___x_4080_ = lean_box(0);
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 24;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_4014_ == 0 {
                    lean_ctor_set(v___x_4013_, 2, v_a_4033_);
                    lean_ctor_set(v___x_4013_, 1, v_a_4016_);
                    v___x_4055_ = v___x_4013_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_name_4010_);
                    lean_ctor_set(v_reuseFailAlloc_4068_, 1, v_a_4016_);
                    lean_ctor_set(v_reuseFailAlloc_4068_, 2, v_a_4033_);
                    v___x_4055_ = v_reuseFailAlloc_4068_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_4056_ = lean_unsigned_to_nat(1);
                v___x_4057_ = lean_mk_empty_array_with_capacity(v___x_4056_);
                v___x_4058_ = lean_array_push(v___x_4057_, v___x_4055_);
                if v_isShared_3982_ == 0 {
                    lean_ctor_set(v___x_3981_, 3, v___x_4058_);
                    lean_ctor_set(v___x_3981_, 2, v_a_3984_);
                    lean_ctor_set(v___x_3981_, 1, v_a_4050_);
                    lean_ctor_set(v___x_3981_, 0, v_typeName_3975_);
                    v___x_4060_ = v___x_3981_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_typeName_3975_);
                    lean_ctor_set(v_reuseFailAlloc_4067_, 1, v_a_4050_);
                    lean_ctor_set(v_reuseFailAlloc_4067_, 2, v_a_3984_);
                    lean_ctor_set(v_reuseFailAlloc_4067_, 3, v___x_4058_);
                    v___x_4060_ = v_reuseFailAlloc_4067_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4036_ == 0 {
                    lean_ctor_set_tag(v___x_4035_, 4);
                    lean_ctor_set(v___x_4035_, 0, v___x_4060_);
                    v___x_4062_ = v___x_4035_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4066_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4060_);
                    v___x_4062_ = v_reuseFailAlloc_4066_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_4053_ == 0 {
                    lean_ctor_set(v___x_4052_, 0, v___x_4062_);
                    v___x_4064_ = v___x_4052_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4062_);
                    v___x_4064_ = v_reuseFailAlloc_4065_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4064_;
            }
            22 => {
                if v_isShared_4073_ == 0 {
                    v___x_4075_ = v___x_4072_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
                    v___x_4075_ = v_reuseFailAlloc_4076_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4075_;
            }
            24 => {
                if v_isShared_4081_ == 0 {
                    v___x_4083_ = v___x_4080_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
                    v___x_4083_ = v_reuseFailAlloc_4084_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4083_;
            }
            26 => {
                if v_isShared_4094_ == 0 {
                    v___x_4096_ = v___x_4093_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
                    v___x_4096_ = v_reuseFailAlloc_4097_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4096_;
            }
            28 => {
                if v_isShared_4106_ == 0 {
                    v___x_4108_ = v___x_4105_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
                    v___x_4108_ = v_reuseFailAlloc_4109_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4108_;
            }
            30 => {
                if v_isShared_4114_ == 0 {
                    v___x_4116_ = v___x_4113_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
                    v___x_4116_ = v_reuseFailAlloc_4117_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4116_;
            }
            32 => {
                if v_isShared_4122_ == 0 {
                    v___x_4124_ = v___x_4121_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
                    v___x_4124_ = v_reuseFailAlloc_4125_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4124_;
            }
            34 => {
                v___x_4160_ = lean_ptr_addr(v_k_4132_);
                v___x_4161_ = lean_ptr_addr(v_a_4139_);
                v___x_4162_ = lean_usize_dec_eq(v___x_4160_, v___x_4161_);
                if v___x_4162_ == 0 {
                    lean_dec_ref(v_decl_3971_);
                    v___y_4144_ = v___x_4162_;
                    state = 35;
                    continue;
                } else {
                    v___x_4163_ = lean_ptr_addr(v_decl_3971_);
                    lean_dec_ref(v_decl_3971_);
                    v___x_4164_ = lean_ptr_addr(v_a_4137_);
                    v___x_4165_ = lean_usize_dec_eq(v___x_4163_, v___x_4164_);
                    v___y_4144_ = v___x_4165_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v___y_4144_ == 0 {
                    v_isSharedCheck_4154_ = (!lean_is_exclusive(v_code_3897_)) as u8;
                    if v_isSharedCheck_4154_ == 0 {
                        v_unused_4155_ = lean_ctor_get(v_code_3897_, 1);
                        lean_dec(v_unused_4155_);
                        v_unused_4156_ = lean_ctor_get(v_code_3897_, 0);
                        lean_dec(v_unused_4156_);
                        v___x_4146_ = v_code_3897_;
                        v_isShared_4147_ = v_isSharedCheck_4154_;
                        state = 36;
                        continue;
                    } else {
                        lean_dec(v_code_3897_);
                        v___x_4146_ = lean_box(0);
                        v_isShared_4147_ = v_isSharedCheck_4154_;
                        state = 36;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4139_);
                    lean_dec(v_a_4137_);
                    if v_isShared_4142_ == 0 {
                        lean_ctor_set(v___x_4141_, 0, v_code_3897_);
                        v___x_4158_ = v___x_4141_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_code_3897_);
                        v___x_4158_ = v_reuseFailAlloc_4159_;
                        state = 39;
                        continue;
                    }
                }
            }
            36 => {
                if v_isShared_4147_ == 0 {
                    lean_ctor_set(v___x_4146_, 1, v_a_4139_);
                    lean_ctor_set(v___x_4146_, 0, v_a_4137_);
                    v___x_4149_ = v___x_4146_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4137_);
                    lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_a_4139_);
                    v___x_4149_ = v_reuseFailAlloc_4153_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_4142_ == 0 {
                    lean_ctor_set(v___x_4141_, 0, v___x_4149_);
                    v___x_4151_ = v___x_4141_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4149_);
                    v___x_4151_ = v_reuseFailAlloc_4152_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4151_;
            }
            39 => {
                return v___x_4158_;
            }
            40 => {
                if v_isShared_4170_ == 0 {
                    v___x_4172_ = v___x_4169_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
                    v___x_4172_ = v_reuseFailAlloc_4173_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_4172_;
            }
            42 => {
                if v_isShared_4178_ == 0 {
                    v___x_4180_ = v___x_4177_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
                    v___x_4180_ = v_reuseFailAlloc_4181_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_4180_;
            }
            44 => {
                v___x_4211_ = l_Lean_instBEqFVarId_beq(v_fvarId_4183_, v_a_4186_);
                if v___x_4211_ == 0 {
                    v___y_4195_ = v___x_4211_;
                    state = 45;
                    continue;
                } else {
                    v___x_4212_ = lean_ptr_addr(v_args_4184_);
                    v___x_4213_ = lean_ptr_addr(v_a_4190_);
                    v___x_4214_ = lean_usize_dec_eq(v___x_4212_, v___x_4213_);
                    v___y_4195_ = v___x_4214_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v___y_4195_ == 0 {
                    v_isSharedCheck_4205_ = (!lean_is_exclusive(v_code_3897_)) as u8;
                    if v_isSharedCheck_4205_ == 0 {
                        v_unused_4206_ = lean_ctor_get(v_code_3897_, 1);
                        lean_dec(v_unused_4206_);
                        v_unused_4207_ = lean_ctor_get(v_code_3897_, 0);
                        lean_dec(v_unused_4207_);
                        v___x_4197_ = v_code_3897_;
                        v_isShared_4198_ = v_isSharedCheck_4205_;
                        state = 46;
                        continue;
                    } else {
                        lean_dec(v_code_3897_);
                        v___x_4197_ = lean_box(0);
                        v_isShared_4198_ = v_isSharedCheck_4205_;
                        state = 46;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4190_);
                    lean_dec(v_a_4186_);
                    if v_isShared_4193_ == 0 {
                        lean_ctor_set(v___x_4192_, 0, v_code_3897_);
                        v___x_4209_ = v___x_4192_;
                        state = 49;
                        continue;
                    } else {
                        v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_code_3897_);
                        v___x_4209_ = v_reuseFailAlloc_4210_;
                        state = 49;
                        continue;
                    }
                }
            }
            46 => {
                if v_isShared_4198_ == 0 {
                    lean_ctor_set(v___x_4197_, 1, v_a_4190_);
                    lean_ctor_set(v___x_4197_, 0, v_a_4186_);
                    v___x_4200_ = v___x_4197_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4204_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4186_);
                    lean_ctor_set(v_reuseFailAlloc_4204_, 1, v_a_4190_);
                    v___x_4200_ = v_reuseFailAlloc_4204_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                if v_isShared_4193_ == 0 {
                    lean_ctor_set(v___x_4192_, 0, v___x_4200_);
                    v___x_4202_ = v___x_4192_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4200_);
                    v___x_4202_ = v_reuseFailAlloc_4203_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_4202_;
            }
            49 => {
                return v___x_4209_;
            }
            50 => {
                if v_isShared_4219_ == 0 {
                    v___x_4221_ = v___x_4218_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
                    v___x_4221_ = v_reuseFailAlloc_4222_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_4221_;
            }
            52 => {
                if v_isShared_4227_ == 0 {
                    v___x_4229_ = v___x_4226_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
                    v___x_4229_ = v_reuseFailAlloc_4230_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_4229_;
            }
            54 => {
                lean_inc(v_discr_4235_);
                v___x_4240_ = l_Lean_Compiler_LCNF_StructProjCases_remapFVar___redArg(
                    v_discr_4235_,
                    v_a_3898_,
                );
                if lean_obj_tag(v___x_4240_) == 0 {
                    v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
                    v_isSharedCheck_4368_ = (!lean_is_exclusive(v___x_4240_)) as u8;
                    if v_isSharedCheck_4368_ == 0 {
                        v___x_4243_ = v___x_4240_;
                        v_isShared_4244_ = v_isSharedCheck_4368_;
                        state = 55;
                        continue;
                    } else {
                        lean_inc(v_a_4241_);
                        lean_dec(v___x_4240_);
                        v___x_4243_ = lean_box(0);
                        v_isShared_4244_ = v_isSharedCheck_4368_;
                        state = 55;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4238_);
                    lean_dec_ref(v_alts_4236_);
                    lean_dec(v_discr_4235_);
                    lean_dec_ref(v_resultType_4234_);
                    lean_dec(v_typeName_4233_);
                    lean_dec_ref_known(v_code_3897_, 1);
                    v_a_4369_ = lean_ctor_get(v___x_4240_, 0);
                    v_isSharedCheck_4376_ = (!lean_is_exclusive(v___x_4240_)) as u8;
                    if v_isSharedCheck_4376_ == 0 {
                        v___x_4371_ = v___x_4240_;
                        v_isShared_4372_ = v_isSharedCheck_4376_;
                        state = 75;
                        continue;
                    } else {
                        lean_inc(v_a_4369_);
                        lean_dec(v___x_4240_);
                        v___x_4371_ = lean_box(0);
                        v_isShared_4372_ = v_isSharedCheck_4376_;
                        state = 75;
                        continue;
                    }
                }
            }
            55 => {
                v___x_4281_ = lean_array_get_size(v_alts_4236_);
                v___x_4282_ = lean_unsigned_to_nat(1);
                v___x_4283_ = lean_nat_dec_eq(v___x_4281_, v___x_4282_);
                if v___x_4283_ == 0 {
                    v___y_4260_ = v_a_3898_;
                    v___y_4261_ = v_a_3899_;
                    v___y_4262_ = v_a_3900_;
                    v___y_4263_ = v_a_3901_;
                    v___y_4264_ = v_a_3902_;
                    state = 60;
                    continue;
                } else {
                    v___x_4284_ = lean_unsigned_to_nat(0);
                    v___x_4285_ = lean_array_fget(v_alts_4236_, v___x_4284_);
                    if lean_obj_tag(v___x_4285_) == 0 {
                        lean_del_object(v___x_4243_);
                        lean_del_object(v___x_4238_);
                        v_ctorName_4286_ = lean_ctor_get(v___x_4285_, 0);
                        v_params_4287_ = lean_ctor_get(v___x_4285_, 1);
                        v_code_4288_ = lean_ctor_get(v___x_4285_, 2);
                        v_isSharedCheck_4367_ = (!lean_is_exclusive(v___x_4285_)) as u8;
                        if v_isSharedCheck_4367_ == 0 {
                            v___x_4290_ = v___x_4285_;
                            v_isShared_4291_ = v_isSharedCheck_4367_;
                            state = 63;
                            continue;
                        } else {
                            lean_inc(v_code_4288_);
                            lean_inc(v_params_4287_);
                            lean_inc(v_ctorName_4286_);
                            lean_dec(v___x_4285_);
                            v___x_4290_ = lean_box(0);
                            v_isShared_4291_ = v_isSharedCheck_4367_;
                            state = 63;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4285_);
                        v___y_4260_ = v_a_3898_;
                        v___y_4261_ = v_a_3899_;
                        v___y_4262_ = v_a_3900_;
                        v___y_4263_ = v_a_3901_;
                        v___y_4264_ = v_a_3902_;
                        state = 60;
                        continue;
                    }
                }
            }
            56 => {
                if v_isShared_4239_ == 0 {
                    lean_ctor_set(v___x_4238_, 3, v___y_4246_);
                    lean_ctor_set(v___x_4238_, 2, v_a_4241_);
                    v___x_4248_ = v___x_4238_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_typeName_4233_);
                    lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_resultType_4234_);
                    lean_ctor_set(v_reuseFailAlloc_4253_, 2, v_a_4241_);
                    lean_ctor_set(v_reuseFailAlloc_4253_, 3, v___y_4246_);
                    v___x_4248_ = v_reuseFailAlloc_4253_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                v___x_4249_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_4249_, 0, v___x_4248_);
                if v_isShared_4244_ == 0 {
                    lean_ctor_set(v___x_4243_, 0, v___x_4249_);
                    v___x_4251_ = v___x_4243_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4249_);
                    v___x_4251_ = v_reuseFailAlloc_4252_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_4251_;
            }
            59 => {
                if v___y_4256_ == 0 {
                    lean_dec(v_discr_4235_);
                    lean_dec_ref_known(v_code_3897_, 1);
                    v___y_4246_ = v___y_4255_;
                    state = 56;
                    continue;
                } else {
                    v___x_4257_ = l_Lean_instBEqFVarId_beq(v_discr_4235_, v_a_4241_);
                    lean_dec(v_discr_4235_);
                    if v___x_4257_ == 0 {
                        lean_dec_ref_known(v_code_3897_, 1);
                        v___y_4246_ = v___y_4255_;
                        state = 56;
                        continue;
                    } else {
                        lean_dec_ref(v___y_4255_);
                        lean_del_object(v___x_4243_);
                        lean_dec(v_a_4241_);
                        lean_del_object(v___x_4238_);
                        lean_dec_ref(v_resultType_4234_);
                        lean_dec(v_typeName_4233_);
                        v___x_4258_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4258_, 0, v_code_3897_);
                        return v___x_4258_;
                    }
                }
            }
            60 => {
                v___x_4265_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_alts_4236_);
                v___x_4266_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__5(v___x_4265_, v_alts_4236_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
                if lean_obj_tag(v___x_4266_) == 0 {
                    v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
                    lean_inc(v_a_4267_);
                    lean_dec_ref_known(v___x_4266_, 1);
                    v___x_4268_ = lean_ptr_addr(v_alts_4236_);
                    lean_dec_ref(v_alts_4236_);
                    v___x_4269_ = lean_ptr_addr(v_a_4267_);
                    v___x_4270_ = lean_usize_dec_eq(v___x_4268_, v___x_4269_);
                    if v___x_4270_ == 0 {
                        v___y_4255_ = v_a_4267_;
                        v___y_4256_ = v___x_4270_;
                        state = 59;
                        continue;
                    } else {
                        v___x_4271_ = lean_ptr_addr(v_resultType_4234_);
                        v___x_4272_ = lean_usize_dec_eq(v___x_4271_, v___x_4271_);
                        v___y_4255_ = v_a_4267_;
                        v___y_4256_ = v___x_4272_;
                        state = 59;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4243_);
                    lean_dec(v_a_4241_);
                    lean_del_object(v___x_4238_);
                    lean_dec_ref(v_alts_4236_);
                    lean_dec(v_discr_4235_);
                    lean_dec_ref(v_resultType_4234_);
                    lean_dec(v_typeName_4233_);
                    lean_dec_ref_known(v_code_3897_, 1);
                    v_a_4273_ = lean_ctor_get(v___x_4266_, 0);
                    v_isSharedCheck_4280_ = (!lean_is_exclusive(v___x_4266_)) as u8;
                    if v_isSharedCheck_4280_ == 0 {
                        v___x_4275_ = v___x_4266_;
                        v_isShared_4276_ = v_isSharedCheck_4280_;
                        state = 61;
                        continue;
                    } else {
                        lean_inc(v_a_4273_);
                        lean_dec(v___x_4266_);
                        v___x_4275_ = lean_box(0);
                        v_isShared_4276_ = v_isSharedCheck_4280_;
                        state = 61;
                        continue;
                    }
                }
            }
            61 => {
                if v_isShared_4276_ == 0 {
                    v___x_4278_ = v___x_4275_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
                    v___x_4278_ = v_reuseFailAlloc_4279_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_4278_;
            }
            63 => {
                v___x_4292_ = lean_st_ref_get(v_a_3898_);
                v_projMap_4293_ = lean_ctor_get(v___x_4292_, 0);
                lean_inc_ref(v_projMap_4293_);
                lean_dec(v___x_4292_);
                v___x_4294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_StructProjCases_remapFVar_spec__0___redArg(v_projMap_4293_, v_a_4241_);
                lean_dec_ref(v_projMap_4293_);
                if lean_obj_tag(v___x_4294_) == 1 {
                    lean_del_object(v___x_4290_);
                    lean_dec(v_ctorName_4286_);
                    lean_dec(v_a_4241_);
                    lean_dec_ref(v_alts_4236_);
                    lean_dec(v_discr_4235_);
                    lean_dec_ref(v_resultType_4234_);
                    lean_dec(v_typeName_4233_);
                    lean_dec_ref_known(v_code_3897_, 1);
                    v_val_4295_ = lean_ctor_get(v___x_4294_, 0);
                    lean_inc(v_val_4295_);
                    lean_dec_ref_known(v___x_4294_, 1);
                    v___x_4296_ = lean_array_get_size(v_val_4295_);
                    v___x_4297_ = lean_array_get_size(v_params_4287_);
                    v___x_4298_ = lean_nat_dec_eq(v___x_4296_, v___x_4297_);
                    if v___x_4298_ == 0 {
                        lean_dec(v_val_4295_);
                        lean_dec_ref(v_code_4288_);
                        lean_dec_ref(v_params_4287_);
                        v___x_4299_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__7_once
                            ),
                            _init_l_Lean_Compiler_LCNF_StructProjCases_visitCode___closed__7,
                        );
                        v___x_4300_ =
                            l_panic___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__4(
                                v___x_4299_,
                                v_a_3898_,
                                v_a_3899_,
                                v_a_3900_,
                                v_a_3901_,
                                v_a_3902_,
                            );
                        return v___x_4300_;
                    } else {
                        v___x_4301_ =
                            l_Array_toSubarray___redArg(v_val_4295_, v___x_4284_, v___x_4296_);
                        v_sz_4302_ = lean_array_size(v_params_4287_);
                        v___x_4303_ = 0usize;
                        v___x_4304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___redArg(v_params_4287_, v_sz_4302_, v___x_4303_, v___x_4301_, v_a_3898_, v_a_3900_);
                        lean_dec_ref(v_params_4287_);
                        if lean_obj_tag(v___x_4304_) == 0 {
                            lean_dec_ref_known(v___x_4304_, 1);
                            v_code_3897_ = v_code_4288_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_code_4288_);
                            v_a_4306_ = lean_ctor_get(v___x_4304_, 0);
                            v_isSharedCheck_4313_ = (!lean_is_exclusive(v___x_4304_)) as u8;
                            if v_isSharedCheck_4313_ == 0 {
                                v___x_4308_ = v___x_4304_;
                                v_isShared_4309_ = v_isSharedCheck_4313_;
                                state = 64;
                                continue;
                            } else {
                                lean_inc(v_a_4306_);
                                lean_dec(v___x_4304_);
                                v___x_4308_ = lean_box(0);
                                v_isShared_4309_ = v_isSharedCheck_4313_;
                                state = 64;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_4294_);
                    v___x_4314_ = lean_st_ref_take(v_a_3898_);
                    v_projMap_4315_ = lean_ctor_get(v___x_4314_, 0);
                    v_fvarMap_4316_ = lean_ctor_get(v___x_4314_, 1);
                    v_isSharedCheck_4366_ = (!lean_is_exclusive(v___x_4314_)) as u8;
                    if v_isSharedCheck_4366_ == 0 {
                        v___x_4318_ = v___x_4314_;
                        v_isShared_4319_ = v_isSharedCheck_4366_;
                        state = 66;
                        continue;
                    } else {
                        lean_inc(v_fvarMap_4316_);
                        lean_inc(v_projMap_4315_);
                        lean_dec(v___x_4314_);
                        v___x_4318_ = lean_box(0);
                        v_isShared_4319_ = v_isSharedCheck_4366_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_4309_ == 0 {
                    v___x_4311_ = v___x_4308_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
                    v___x_4311_ = v_reuseFailAlloc_4312_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_4311_;
            }
            66 => {
                v_sz_4320_ = lean_array_size(v_params_4287_);
                v___x_4321_ = 0usize;
                lean_inc_ref(v_params_4287_);
                v___x_4322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__2(v_sz_4320_, v___x_4321_, v_params_4287_);
                lean_inc(v_a_4241_);
                v___x_4323_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(v_projMap_4315_, v_a_4241_, v___x_4322_);
                if v_isShared_4319_ == 0 {
                    lean_ctor_set(v___x_4318_, 0, v___x_4323_);
                    v___x_4325_ = v___x_4318_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4323_);
                    lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_fvarMap_4316_);
                    v___x_4325_ = v_reuseFailAlloc_4365_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                v___x_4326_ = lean_st_ref_set(v_a_3898_, v___x_4325_);
                v___x_4327_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(
                    v_code_4288_,
                    v_a_3898_,
                    v_a_3899_,
                    v_a_3900_,
                    v_a_3901_,
                    v_a_3902_,
                );
                if lean_obj_tag(v___x_4327_) == 0 {
                    v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
                    v_isSharedCheck_4364_ = (!lean_is_exclusive(v___x_4327_)) as u8;
                    if v_isSharedCheck_4364_ == 0 {
                        v___x_4330_ = v___x_4327_;
                        v_isShared_4331_ = v_isSharedCheck_4364_;
                        state = 68;
                        continue;
                    } else {
                        lean_inc(v_a_4328_);
                        lean_dec(v___x_4327_);
                        v___x_4330_ = lean_box(0);
                        v_isShared_4331_ = v_isSharedCheck_4364_;
                        state = 68;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4290_);
                    lean_dec_ref(v_params_4287_);
                    lean_dec(v_ctorName_4286_);
                    lean_dec(v_a_4241_);
                    lean_dec_ref(v_alts_4236_);
                    lean_dec(v_discr_4235_);
                    lean_dec_ref(v_resultType_4234_);
                    lean_dec(v_typeName_4233_);
                    lean_dec_ref_known(v_code_3897_, 1);
                    return v___x_4327_;
                }
            }
            68 => {
                v___x_4332_ = lean_st_ref_take(v_a_3898_);
                v_projMap_4333_ = lean_ctor_get(v___x_4332_, 0);
                v_fvarMap_4334_ = lean_ctor_get(v___x_4332_, 1);
                v_isSharedCheck_4363_ = (!lean_is_exclusive(v___x_4332_)) as u8;
                if v_isSharedCheck_4363_ == 0 {
                    v___x_4336_ = v___x_4332_;
                    v_isShared_4337_ = v_isSharedCheck_4363_;
                    state = 69;
                    continue;
                } else {
                    lean_inc(v_fvarMap_4334_);
                    lean_inc(v_projMap_4333_);
                    lean_dec(v___x_4332_);
                    v___x_4336_ = lean_box(0);
                    v_isShared_4337_ = v_isSharedCheck_4363_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_4338_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg(v_projMap_4333_, v_a_4241_);
                if v_isShared_4337_ == 0 {
                    lean_ctor_set(v___x_4336_, 0, v___x_4338_);
                    v___x_4340_ = v___x_4336_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4362_, 0, v___x_4338_);
                    lean_ctor_set(v_reuseFailAlloc_4362_, 1, v_fvarMap_4334_);
                    v___x_4340_ = v_reuseFailAlloc_4362_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                v___x_4341_ = lean_st_ref_set(v_a_3898_, v___x_4340_);
                if v_isShared_4291_ == 0 {
                    lean_ctor_set(v___x_4290_, 2, v_a_4328_);
                    v___x_4343_ = v___x_4290_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_ctorName_4286_);
                    lean_ctor_set(v_reuseFailAlloc_4361_, 1, v_params_4287_);
                    lean_ctor_set(v_reuseFailAlloc_4361_, 2, v_a_4328_);
                    v___x_4343_ = v_reuseFailAlloc_4361_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                v___x_4344_ = lean_mk_empty_array_with_capacity(v___x_4282_);
                v___x_4345_ = lean_array_push(v___x_4344_, v___x_4343_);
                v___x_4356_ = lean_ptr_addr(v_alts_4236_);
                lean_dec_ref(v_alts_4236_);
                v___x_4357_ = lean_ptr_addr(v___x_4345_);
                v___x_4358_ = lean_usize_dec_eq(v___x_4356_, v___x_4357_);
                if v___x_4358_ == 0 {
                    v___y_4353_ = v___x_4358_;
                    state = 74;
                    continue;
                } else {
                    v___x_4359_ = lean_ptr_addr(v_resultType_4234_);
                    v___x_4360_ = lean_usize_dec_eq(v___x_4359_, v___x_4359_);
                    v___y_4353_ = v___x_4360_;
                    state = 74;
                    continue;
                }
            }
            72 => {
                v___x_4347_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_4347_, 0, v_typeName_4233_);
                lean_ctor_set(v___x_4347_, 1, v_resultType_4234_);
                lean_ctor_set(v___x_4347_, 2, v_a_4241_);
                lean_ctor_set(v___x_4347_, 3, v___x_4345_);
                v___x_4348_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_4348_, 0, v___x_4347_);
                if v_isShared_4331_ == 0 {
                    lean_ctor_set(v___x_4330_, 0, v___x_4348_);
                    v___x_4350_ = v___x_4330_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4348_);
                    v___x_4350_ = v_reuseFailAlloc_4351_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                return v___x_4350_;
            }
            74 => {
                if v___y_4353_ == 0 {
                    lean_dec(v_discr_4235_);
                    lean_dec_ref_known(v_code_3897_, 1);
                    state = 72;
                    continue;
                } else {
                    v___x_4354_ = l_Lean_instBEqFVarId_beq(v_discr_4235_, v_a_4241_);
                    lean_dec(v_discr_4235_);
                    if v___x_4354_ == 0 {
                        lean_dec_ref_known(v_code_3897_, 1);
                        state = 72;
                        continue;
                    } else {
                        lean_dec_ref(v___x_4345_);
                        lean_del_object(v___x_4330_);
                        lean_dec(v_a_4241_);
                        lean_dec_ref(v_resultType_4234_);
                        lean_dec(v_typeName_4233_);
                        v___x_4355_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4355_, 0, v_code_3897_);
                        return v___x_4355_;
                    }
                }
            }
            75 => {
                if v_isShared_4372_ == 0 {
                    v___x_4374_ = v___x_4371_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_a_4369_);
                    v___x_4374_ = v_reuseFailAlloc_4375_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                return v___x_4374_;
            }
            77 => {
                v___x_4384_ = l_Lean_instBEqFVarId_beq(v_fvarId_4378_, v_a_4380_);
                if v___x_4384_ == 0 {
                    v_isSharedCheck_4394_ = (!lean_is_exclusive(v_code_3897_)) as u8;
                    if v_isSharedCheck_4394_ == 0 {
                        v_unused_4395_ = lean_ctor_get(v_code_3897_, 0);
                        lean_dec(v_unused_4395_);
                        v___x_4386_ = v_code_3897_;
                        v_isShared_4387_ = v_isSharedCheck_4394_;
                        state = 78;
                        continue;
                    } else {
                        lean_dec(v_code_3897_);
                        v___x_4386_ = lean_box(0);
                        v_isShared_4387_ = v_isSharedCheck_4394_;
                        state = 78;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4380_);
                    if v_isShared_4383_ == 0 {
                        lean_ctor_set(v___x_4382_, 0, v_code_3897_);
                        v___x_4397_ = v___x_4382_;
                        state = 81;
                        continue;
                    } else {
                        v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_code_3897_);
                        v___x_4397_ = v_reuseFailAlloc_4398_;
                        state = 81;
                        continue;
                    }
                }
            }
            78 => {
                if v_isShared_4387_ == 0 {
                    lean_ctor_set(v___x_4386_, 0, v_a_4380_);
                    v___x_4389_ = v___x_4386_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_4393_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_a_4380_);
                    v___x_4389_ = v_reuseFailAlloc_4393_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                if v_isShared_4383_ == 0 {
                    lean_ctor_set(v___x_4382_, 0, v___x_4389_);
                    v___x_4391_ = v___x_4382_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 0, v___x_4389_);
                    v___x_4391_ = v_reuseFailAlloc_4392_;
                    state = 80;
                    continue;
                }
            }
            80 => {
                return v___x_4391_;
            }
            81 => {
                return v___x_4397_;
            }
            82 => {
                if v_isShared_4403_ == 0 {
                    v___x_4405_ = v___x_4402_;
                    state = 83;
                    continue;
                } else {
                    v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
                    v___x_4405_ = v_reuseFailAlloc_4406_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                return v___x_4405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_visitAlt(
    mut v_alt_4411_: *mut LeanObject,
    mut v_a_4412_: *mut LeanObject,
    mut v_a_4413_: *mut LeanObject,
    mut v_a_4414_: *mut LeanObject,
    mut v_a_4415_: *mut LeanObject,
    mut v_a_4416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4424_: u8 = 0;
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4429_: u8 = 0;
    let mut v_a_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4433_: u8 = 0;
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4437_: u8 = 0;
    let mut v_code_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_alt_4411_) {
                0 => {
                    v_code_4438_ = lean_ctor_get(v_alt_4411_, 2);
                    lean_inc_ref(v_code_4438_);
                    v___y_4419_ = v_code_4438_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_code_4439_ = lean_ctor_get(v_alt_4411_, 1);
                    lean_inc_ref(v_code_4439_);
                    v___y_4419_ = v_code_4439_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_code_4440_ = lean_ctor_get(v_alt_4411_, 0);
                    lean_inc_ref(v_code_4440_);
                    v___y_4419_ = v_code_4440_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_4420_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(
                    v___y_4419_,
                    v_a_4412_,
                    v_a_4413_,
                    v_a_4414_,
                    v_a_4415_,
                    v_a_4416_,
                );
                if lean_obj_tag(v___x_4420_) == 0 {
                    v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
                    v_isSharedCheck_4429_ = (!lean_is_exclusive(v___x_4420_)) as u8;
                    if v_isSharedCheck_4429_ == 0 {
                        v___x_4423_ = v___x_4420_;
                        v_isShared_4424_ = v_isSharedCheck_4429_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4421_);
                        lean_dec(v___x_4420_);
                        v___x_4423_ = lean_box(0);
                        v_isShared_4424_ = v_isSharedCheck_4429_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_alt_4411_);
                    v_a_4430_ = lean_ctor_get(v___x_4420_, 0);
                    v_isSharedCheck_4437_ = (!lean_is_exclusive(v___x_4420_)) as u8;
                    if v_isSharedCheck_4437_ == 0 {
                        v___x_4432_ = v___x_4420_;
                        v_isShared_4433_ = v_isSharedCheck_4437_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4430_);
                        lean_dec(v___x_4420_);
                        v___x_4432_ = lean_box(0);
                        v_isShared_4433_ = v_isSharedCheck_4437_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4425_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_4411_, v_a_4421_);
                if v_isShared_4424_ == 0 {
                    lean_ctor_set(v___x_4423_, 0, v___x_4425_);
                    v___x_4427_ = v___x_4423_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4428_, 0, v___x_4425_);
                    v___x_4427_ = v_reuseFailAlloc_4428_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4427_;
            }
            4 => {
                if v_isShared_4433_ == 0 {
                    v___x_4435_ = v___x_4432_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
                    v___x_4435_ = v_reuseFailAlloc_4436_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_visitAlt___boxed(
    mut v_alt_4441_: *mut LeanObject,
    mut v_a_4442_: *mut LeanObject,
    mut v_a_4443_: *mut LeanObject,
    mut v_a_4444_: *mut LeanObject,
    mut v_a_4445_: *mut LeanObject,
    mut v_a_4446_: *mut LeanObject,
    mut v_a_4447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4448_: *mut LeanObject = core::ptr::null_mut();
    v_res_4448_ = l_Lean_Compiler_LCNF_StructProjCases_visitAlt(
        v_alt_4441_,
        v_a_4442_,
        v_a_4443_,
        v_a_4444_,
        v_a_4445_,
        v_a_4446_,
    );
    lean_dec(v_a_4446_);
    lean_dec_ref(v_a_4445_);
    lean_dec(v_a_4444_);
    lean_dec_ref(v_a_4443_);
    lean_dec(v_a_4442_);
    return v_res_4448_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__5___boxed(
    mut v_i_4449_: *mut LeanObject,
    mut v_as_4450_: *mut LeanObject,
    mut v___y_4451_: *mut LeanObject,
    mut v___y_4452_: *mut LeanObject,
    mut v___y_4453_: *mut LeanObject,
    mut v___y_4454_: *mut LeanObject,
    mut v___y_4455_: *mut LeanObject,
    mut v___y_4456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4457_: *mut LeanObject = core::ptr::null_mut();
    v_res_4457_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__5(v_i_4449_, v_as_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
    lean_dec(v___y_4455_);
    lean_dec_ref(v___y_4454_);
    lean_dec(v___y_4453_);
    lean_dec_ref(v___y_4452_);
    lean_dec(v___y_4451_);
    return v_res_4457_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_visitCode___boxed(
    mut v_code_4458_: *mut LeanObject,
    mut v_a_4459_: *mut LeanObject,
    mut v_a_4460_: *mut LeanObject,
    mut v_a_4461_: *mut LeanObject,
    mut v_a_4462_: *mut LeanObject,
    mut v_a_4463_: *mut LeanObject,
    mut v_a_4464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4465_: *mut LeanObject = core::ptr::null_mut();
    v_res_4465_ = l_Lean_Compiler_LCNF_StructProjCases_visitCode(
        v_code_4458_,
        v_a_4459_,
        v_a_4460_,
        v_a_4461_,
        v_a_4462_,
        v_a_4463_,
    );
    lean_dec(v_a_4463_);
    lean_dec_ref(v_a_4462_);
    lean_dec(v_a_4461_);
    lean_dec_ref(v_a_4460_);
    lean_dec(v_a_4459_);
    return v_res_4465_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1(
    mut v_00_u03b2_4466_: *mut LeanObject,
    mut v_m_4467_: *mut LeanObject,
    mut v_a_4468_: *mut LeanObject,
    mut v_b_4469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    v___x_4470_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1___redArg(v_m_4467_, v_a_4468_, v_b_4469_);
    return v___x_4470_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3(
    mut v_00_u03b2_4471_: *mut LeanObject,
    mut v_m_4472_: *mut LeanObject,
    mut v_a_4473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    v___x_4474_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___redArg(v_m_4472_, v_a_4473_);
    return v___x_4474_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3___boxed(
    mut v_00_u03b2_4475_: *mut LeanObject,
    mut v_m_4476_: *mut LeanObject,
    mut v_a_4477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4478_: *mut LeanObject = core::ptr::null_mut();
    v_res_4478_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3(v_00_u03b2_4475_, v_m_4476_, v_a_4477_);
    lean_dec(v_a_4477_);
    return v_res_4478_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6(
    mut v_as_4479_: *mut LeanObject,
    mut v_sz_4480_: usize,
    mut v_i_4481_: usize,
    mut v_b_4482_: *mut LeanObject,
    mut v___y_4483_: *mut LeanObject,
    mut v___y_4484_: *mut LeanObject,
    mut v___y_4485_: *mut LeanObject,
    mut v___y_4486_: *mut LeanObject,
    mut v___y_4487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    v___x_4489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___redArg(v_as_4479_, v_sz_4480_, v_i_4481_, v_b_4482_, v___y_4483_, v___y_4485_);
    return v___x_4489_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6___boxed(
    mut v_as_4490_: *mut LeanObject,
    mut v_sz_4491_: *mut LeanObject,
    mut v_i_4492_: *mut LeanObject,
    mut v_b_4493_: *mut LeanObject,
    mut v___y_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
    mut v___y_4496_: *mut LeanObject,
    mut v___y_4497_: *mut LeanObject,
    mut v___y_4498_: *mut LeanObject,
    mut v___y_4499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4500_: usize = 0;
    let mut v_i_boxed_4501_: usize = 0;
    let mut v_res_4502_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4500_ = lean_unbox_usize(v_sz_4491_);
    lean_dec(v_sz_4491_);
    v_i_boxed_4501_ = lean_unbox_usize(v_i_4492_);
    lean_dec(v_i_4492_);
    v_res_4502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__6(v_as_4490_, v_sz_boxed_4500_, v_i_boxed_4501_, v_b_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
    lean_dec(v___y_4498_);
    lean_dec_ref(v___y_4497_);
    lean_dec(v___y_4496_);
    lean_dec_ref(v___y_4495_);
    lean_dec(v___y_4494_);
    lean_dec_ref(v_as_4490_);
    return v_res_4502_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2(
    mut v_00_u03b2_4503_: *mut LeanObject,
    mut v_a_4504_: *mut LeanObject,
    mut v_x_4505_: *mut LeanObject,
) -> u8 {
    let mut v___x_4506_: u8 = 0;
    v___x_4506_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___redArg(v_a_4504_, v_x_4505_);
    return v___x_4506_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2___boxed(
    mut v_00_u03b2_4507_: *mut LeanObject,
    mut v_a_4508_: *mut LeanObject,
    mut v_x_4509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4510_: u8 = 0;
    let mut v_r_4511_: *mut LeanObject = core::ptr::null_mut();
    v_res_4510_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__2(v_00_u03b2_4507_, v_a_4508_, v_x_4509_);
    lean_dec(v_x_4509_);
    lean_dec(v_a_4508_);
    v_r_4511_ = lean_box((v_res_4510_) as usize);
    return v_r_4511_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3(
    mut v_00_u03b2_4512_: *mut LeanObject,
    mut v_data_4513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    v___x_4514_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3___redArg(v_data_4513_);
    return v___x_4514_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__4(
    mut v_00_u03b2_4515_: *mut LeanObject,
    mut v_a_4516_: *mut LeanObject,
    mut v_b_4517_: *mut LeanObject,
    mut v_x_4518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    v___x_4519_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__4___redArg(v_a_4516_, v_b_4517_, v_x_4518_);
    return v___x_4519_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7(
    mut v_00_u03b2_4520_: *mut LeanObject,
    mut v_a_4521_: *mut LeanObject,
    mut v_x_4522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    v___x_4523_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___redArg(v_a_4521_, v_x_4522_);
    return v___x_4523_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7___boxed(
    mut v_00_u03b2_4524_: *mut LeanObject,
    mut v_a_4525_: *mut LeanObject,
    mut v_x_4526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4527_: *mut LeanObject = core::ptr::null_mut();
    v_res_4527_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__3_spec__7(v_00_u03b2_4524_, v_a_4525_, v_x_4526_);
    lean_dec(v_a_4525_);
    return v_res_4527_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5(
    mut v_00_u03b2_4528_: *mut LeanObject,
    mut v_i_4529_: *mut LeanObject,
    mut v_source_4530_: *mut LeanObject,
    mut v_target_4531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    v___x_4532_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5___redArg(v_i_4529_, v_source_4530_, v_target_4531_);
    return v___x_4532_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5_spec__10(
    mut v_00_u03b2_4533_: *mut LeanObject,
    mut v_x_4534_: *mut LeanObject,
    mut v_x_4535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    v___x_4536_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_StructProjCases_visitCode_spec__1_spec__3_spec__5_spec__10___redArg(v_x_4534_, v_x_4535_);
    return v___x_4536_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___redArg(
    mut v_f_4537_: *mut LeanObject,
    mut v_v_4538_: *mut LeanObject,
    mut v___y_4539_: *mut LeanObject,
    mut v___y_4540_: *mut LeanObject,
    mut v___y_4541_: *mut LeanObject,
    mut v___y_4542_: *mut LeanObject,
    mut v___y_4543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4548_: u8 = 0;
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4553_: u8 = 0;
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4560_: u8 = 0;
    let mut v_a_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4564_: u8 = 0;
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4568_: u8 = 0;
    let mut v_isSharedCheck_4569_: u8 = 0;
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_4538_) == 0 {
                    v_code_4545_ = lean_ctor_get(v_v_4538_, 0);
                    v_isSharedCheck_4569_ = (!lean_is_exclusive(v_v_4538_)) as u8;
                    if v_isSharedCheck_4569_ == 0 {
                        v___x_4547_ = v_v_4538_;
                        v_isShared_4548_ = v_isSharedCheck_4569_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_code_4545_);
                        lean_dec(v_v_4538_);
                        v___x_4547_ = lean_box(0);
                        v_isShared_4548_ = v_isSharedCheck_4569_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_4537_);
                    v___x_4570_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4570_, 0, v_v_4538_);
                    return v___x_4570_;
                }
            }
            1 => {
                lean_inc(v___y_4543_);
                lean_inc_ref(v___y_4542_);
                lean_inc(v___y_4541_);
                lean_inc_ref(v___y_4540_);
                lean_inc(v___y_4539_);
                v___x_4549_ = lean_apply_7(
                    v_f_4537_,
                    v_code_4545_,
                    v___y_4539_,
                    v___y_4540_,
                    v___y_4541_,
                    v___y_4542_,
                    v___y_4543_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4549_) == 0 {
                    v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
                    v_isSharedCheck_4560_ = (!lean_is_exclusive(v___x_4549_)) as u8;
                    if v_isSharedCheck_4560_ == 0 {
                        v___x_4552_ = v___x_4549_;
                        v_isShared_4553_ = v_isSharedCheck_4560_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4550_);
                        lean_dec(v___x_4549_);
                        v___x_4552_ = lean_box(0);
                        v_isShared_4553_ = v_isSharedCheck_4560_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4547_);
                    v_a_4561_ = lean_ctor_get(v___x_4549_, 0);
                    v_isSharedCheck_4568_ = (!lean_is_exclusive(v___x_4549_)) as u8;
                    if v_isSharedCheck_4568_ == 0 {
                        v___x_4563_ = v___x_4549_;
                        v_isShared_4564_ = v_isSharedCheck_4568_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4561_);
                        lean_dec(v___x_4549_);
                        v___x_4563_ = lean_box(0);
                        v_isShared_4564_ = v_isSharedCheck_4568_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4548_ == 0 {
                    lean_ctor_set(v___x_4547_, 0, v_a_4550_);
                    v___x_4555_ = v___x_4547_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4550_);
                    v___x_4555_ = v_reuseFailAlloc_4559_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4553_ == 0 {
                    lean_ctor_set(v___x_4552_, 0, v___x_4555_);
                    v___x_4557_ = v___x_4552_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4555_);
                    v___x_4557_ = v_reuseFailAlloc_4558_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4557_;
            }
            5 => {
                if v_isShared_4564_ == 0 {
                    v___x_4566_ = v___x_4563_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
                    v___x_4566_ = v_reuseFailAlloc_4567_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___redArg___boxed(
    mut v_f_4571_: *mut LeanObject,
    mut v_v_4572_: *mut LeanObject,
    mut v___y_4573_: *mut LeanObject,
    mut v___y_4574_: *mut LeanObject,
    mut v___y_4575_: *mut LeanObject,
    mut v___y_4576_: *mut LeanObject,
    mut v___y_4577_: *mut LeanObject,
    mut v___y_4578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4579_: *mut LeanObject = core::ptr::null_mut();
    v_res_4579_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___redArg(v_f_4571_, v_v_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
    lean_dec(v___y_4577_);
    lean_dec_ref(v___y_4576_);
    lean_dec(v___y_4575_);
    lean_dec_ref(v___y_4574_);
    lean_dec(v___y_4573_);
    return v_res_4579_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0(
    mut v_pu_4580_: u8,
    mut v_f_4581_: *mut LeanObject,
    mut v_v_4582_: *mut LeanObject,
    mut v___y_4583_: *mut LeanObject,
    mut v___y_4584_: *mut LeanObject,
    mut v___y_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
    mut v___y_4587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    v___x_4589_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___redArg(v_f_4581_, v_v_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_);
    return v___x_4589_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___boxed(
    mut v_pu_4590_: *mut LeanObject,
    mut v_f_4591_: *mut LeanObject,
    mut v_v_4592_: *mut LeanObject,
    mut v___y_4593_: *mut LeanObject,
    mut v___y_4594_: *mut LeanObject,
    mut v___y_4595_: *mut LeanObject,
    mut v___y_4596_: *mut LeanObject,
    mut v___y_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4599_: u8 = 0;
    let mut v_res_4600_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4599_ = (lean_unbox(v_pu_4590_) as u8);
    v_res_4600_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0(v_pu_boxed_4599_, v_f_4591_, v_v_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
    lean_dec(v___y_4597_);
    lean_dec_ref(v___y_4596_);
    lean_dec(v___y_4595_);
    lean_dec_ref(v___y_4594_);
    lean_dec(v___y_4593_);
    return v_res_4600_;
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_visitDecl(
    mut v_decl_4602_: *mut LeanObject,
    mut v_a_4603_: *mut LeanObject,
    mut v_a_4604_: *mut LeanObject,
    mut v_a_4605_: *mut LeanObject,
    mut v_a_4606_: *mut LeanObject,
    mut v_a_4607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_4611_: u8 = 0;
    let mut v_inlineAttr_x3f_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4615_: u8 = 0;
    let mut v___f_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4621_: u8 = 0;
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4628_: u8 = 0;
    let mut v_a_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4632_: u8 = 0;
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4636_: u8 = 0;
    let mut v_isSharedCheck_4637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_4609_ = lean_ctor_get(v_decl_4602_, 0);
                v_value_4610_ = lean_ctor_get(v_decl_4602_, 1);
                v_recursive_4611_ = lean_ctor_get_uint8(
                    v_decl_4602_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_4612_ = lean_ctor_get(v_decl_4602_, 2);
                v_isSharedCheck_4637_ = (!lean_is_exclusive(v_decl_4602_)) as u8;
                if v_isSharedCheck_4637_ == 0 {
                    v___x_4614_ = v_decl_4602_;
                    v_isShared_4615_ = v_isSharedCheck_4637_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inlineAttr_x3f_4612_);
                    lean_inc(v_value_4610_);
                    lean_inc(v_toSignature_4609_);
                    lean_dec(v_decl_4602_);
                    v___x_4614_ = lean_box(0);
                    v_isShared_4615_ = v_isSharedCheck_4637_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_4616_ = l_Lean_Compiler_LCNF_StructProjCases_visitDecl___closed__0;
                v___x_4617_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_StructProjCases_visitDecl_spec__0___redArg(v___f_4616_, v_value_4610_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_);
                if lean_obj_tag(v___x_4617_) == 0 {
                    v_a_4618_ = lean_ctor_get(v___x_4617_, 0);
                    v_isSharedCheck_4628_ = (!lean_is_exclusive(v___x_4617_)) as u8;
                    if v_isSharedCheck_4628_ == 0 {
                        v___x_4620_ = v___x_4617_;
                        v_isShared_4621_ = v_isSharedCheck_4628_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4618_);
                        lean_dec(v___x_4617_);
                        v___x_4620_ = lean_box(0);
                        v_isShared_4621_ = v_isSharedCheck_4628_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4614_);
                    lean_dec(v_inlineAttr_x3f_4612_);
                    lean_dec_ref(v_toSignature_4609_);
                    v_a_4629_ = lean_ctor_get(v___x_4617_, 0);
                    v_isSharedCheck_4636_ = (!lean_is_exclusive(v___x_4617_)) as u8;
                    if v_isSharedCheck_4636_ == 0 {
                        v___x_4631_ = v___x_4617_;
                        v_isShared_4632_ = v_isSharedCheck_4636_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4629_);
                        lean_dec(v___x_4617_);
                        v___x_4631_ = lean_box(0);
                        v_isShared_4632_ = v_isSharedCheck_4636_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4615_ == 0 {
                    lean_ctor_set(v___x_4614_, 1, v_a_4618_);
                    v___x_4623_ = v___x_4614_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_toSignature_4609_);
                    lean_ctor_set(v_reuseFailAlloc_4627_, 1, v_a_4618_);
                    lean_ctor_set(v_reuseFailAlloc_4627_, 2, v_inlineAttr_x3f_4612_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4627_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_recursive_4611_,
                    );
                    v___x_4623_ = v_reuseFailAlloc_4627_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4621_ == 0 {
                    lean_ctor_set(v___x_4620_, 0, v___x_4623_);
                    v___x_4625_ = v___x_4620_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
                    v___x_4625_ = v_reuseFailAlloc_4626_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4625_;
            }
            5 => {
                if v_isShared_4632_ == 0 {
                    v___x_4634_ = v___x_4631_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4635_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
                    v___x_4634_ = v_reuseFailAlloc_4635_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_StructProjCases_visitDecl___boxed(
    mut v_decl_4638_: *mut LeanObject,
    mut v_a_4639_: *mut LeanObject,
    mut v_a_4640_: *mut LeanObject,
    mut v_a_4641_: *mut LeanObject,
    mut v_a_4642_: *mut LeanObject,
    mut v_a_4643_: *mut LeanObject,
    mut v_a_4644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4645_: *mut LeanObject = core::ptr::null_mut();
    v_res_4645_ = l_Lean_Compiler_LCNF_StructProjCases_visitDecl(
        v_decl_4638_,
        v_a_4639_,
        v_a_4640_,
        v_a_4641_,
        v_a_4642_,
        v_a_4643_,
    );
    lean_dec(v_a_4643_);
    lean_dec_ref(v_a_4642_);
    lean_dec(v_a_4641_);
    lean_dec_ref(v_a_4640_);
    lean_dec(v_a_4639_);
    return v_res_4645_;
}
pub unsafe fn l_Lean_Compiler_LCNF_structProjCases___lam__0(
    mut v_x_4646_: *mut LeanObject,
    mut v___y_4647_: *mut LeanObject,
    mut v___y_4648_: *mut LeanObject,
    mut v___y_4649_: *mut LeanObject,
    mut v___y_4650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    v___x_4652_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_StructProjCases_visitDecl___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___x_4652_, 0, v_x_4646_);
    v___x_4653_ = l_Lean_Compiler_LCNF_StructProjCases_M_run___redArg(
        v___x_4652_,
        v___y_4647_,
        v___y_4648_,
        v___y_4649_,
        v___y_4650_,
    );
    return v___x_4653_;
}
pub unsafe fn l_Lean_Compiler_LCNF_structProjCases___lam__0___boxed(
    mut v_x_4654_: *mut LeanObject,
    mut v___y_4655_: *mut LeanObject,
    mut v___y_4656_: *mut LeanObject,
    mut v___y_4657_: *mut LeanObject,
    mut v___y_4658_: *mut LeanObject,
    mut v___y_4659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4660_: *mut LeanObject = core::ptr::null_mut();
    v_res_4660_ = l_Lean_Compiler_LCNF_structProjCases___lam__0(
        v_x_4654_,
        v___y_4655_,
        v___y_4656_,
        v___y_4657_,
        v___y_4658_,
    );
    lean_dec(v___y_4658_);
    lean_dec_ref(v___y_4657_);
    lean_dec(v___y_4656_);
    lean_dec_ref(v___y_4655_);
    return v_res_4660_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_structProjCases___closed__3() -> *mut LeanObject {
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: u8 = 0;
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    v___x_4665_ = lean_unsigned_to_nat(0);
    v___f_4666_ = l_Lean_Compiler_LCNF_structProjCases___closed__0;
    v___x_4667_ = 1;
    v___x_4668_ = l_Lean_Compiler_LCNF_structProjCases___closed__2;
    v___x_4669_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_4668_,
        v___x_4667_,
        v___f_4666_,
        v___x_4665_,
    );
    return v___x_4669_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_structProjCases() -> *mut LeanObject {
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    v___x_4670_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_structProjCases___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_structProjCases___closed__3_once),
        _init_l_Lean_Compiler_LCNF_structProjCases___closed__3,
    );
    return v___x_4670_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: u8 = 0;
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    v___x_4741_ = l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_;
    v___x_4742_ = 1;
    v___x_4743_ = l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_;
    v___x_4744_ = l_Lean_registerTraceClass(v___x_4741_, v___x_4742_, v___x_4743_);
    return v___x_4744_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2____boxed(
    mut v_a_4745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4746_: *mut LeanObject = core::ptr::null_mut();
    v_res_4746_ = l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_();
    return v_res_4746_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_StructProjCases(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Compiler_LCNF_structProjCases = _init_l_Lean_Compiler_LCNF_structProjCases();
    lean_mark_persistent(l_Lean_Compiler_LCNF_structProjCases);
    res = l___private_Lean_Compiler_LCNF_StructProjCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_StructProjCases_268537386____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_StructProjCases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_StructProjCases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_StructProjCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_StructProjCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_StructProjCases(builtin);
}
