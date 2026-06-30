// Lean compiler output
// Module: Lean.Compiler.InitAttr
// Imports: Lean.AddDecl Lean.Elab.InfoTree.Main Init.Data.Range.Polymorphic.Stream Lean.Compiler.NameMangling Lean.Compiler.ModPkgExt
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_expr_eqv, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_run_init, lean_run_mod_init_core,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Stream::{
    initialize_Init_Data_Range_Polymorphic_Stream,
    runtime_initialize_Init_Data_Range_Polymorphic_Stream,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_mkAtom, l_Lean_replaceRef};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Lean::AddDecl::{
    initialize_Lean_AddDecl, l_Lean_addAndCompile, runtime_initialize_Lean_AddDecl,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_Attribute_Builtin_getIdent_x3f, l_Lean_ParametricAttribute_getParam_x3f___redArg,
    l_Lean_ParametricAttribute_setParam___redArg, l_Lean_registerParametricAttribute___redArg,
};
use crate::r#gen::Lean::Compiler::MetaAttr::{l_Lean_getIRPhases, l_Lean_isMarkedMeta};
use crate::r#gen::Lean::Compiler::ModPkgExt::{
    initialize_Lean_Compiler_ModPkgExt, l_Lean_Environment_getModulePackageByIdx_x3f,
    runtime_initialize_Lean_Compiler_ModPkgExt,
};
use crate::r#gen::Lean::Compiler::NameMangling::{
    initialize_Lean_Compiler_NameMangling, l_Lean_mkModuleInitializationFunctionName,
    runtime_initialize_Lean_Compiler_NameMangling,
};
use crate::r#gen::Lean::CoreM::{l_Lean_DeclNameGenerator_mkUniqueName, l_Lean_Elab_inServer};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    initialize_Lean_Elab_InfoTree_Main, l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo,
    runtime_initialize_Lean_Elab_InfoTree_Main,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1,
    l_Lean_Environment_contains, l_Lean_Environment_evalConst___redArg,
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_app___override, l_Lean_mkConst};
use crate::r#gen::Lean::ImportingFlag::l_Lean_isInitializerExecutionEnabled;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Setup::l_Lean_instBEqIRPhases_beq;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [73, 79, 0],
};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType___closed__0_value:
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
    m_data: [85, 110, 105, 116, 0],
};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_interpretedModInits: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_registerInitAttrUnsafe___lam__0___closed__0_value:
    leanh::LeanStringObject<49> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 102, 117, 110, 99,
        116, 105, 111, 110, 32, 109, 117, 115, 116, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101,
        32, 96, 73, 79, 32, 85, 110, 105, 116, 96, 0,
    ],
};
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_registerInitAttrUnsafe___lam__0___closed__2_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 102, 117, 110, 99,
        116, 105, 111, 110, 32, 96, 0,
    ],
};
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_registerInitAttrUnsafe___lam__0___closed__4_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        96, 32, 109, 117, 115, 116, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101, 32, 111, 102,
        32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 73, 79, 32, 60, 116, 121, 112, 101, 62,
        96, 0,
    ],
};
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_registerInitAttrUnsafe___lam__0___closed__6_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        96, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 0,
    ],
};
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_registerInitAttrUnsafe___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_registerInitAttrUnsafe___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_registerInitAttrUnsafe___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttrUnsafe___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_registerInitAttrUnsafe___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_registerInitAttrUnsafe___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttrUnsafe___closed__2_value: leanh::LeanStringObject<47> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 47,
        m_capacity: 47,
        m_length: 46,
        m_data: [
            105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 112, 114, 111,
            99, 101, 100, 117, 114, 101, 32, 102, 111, 114, 32, 103, 108, 111, 98, 97, 108, 32,
            114, 101, 102, 101, 114, 101, 110, 99, 101, 115, 0,
        ],
    };
static mut l_Lean_registerInitAttrUnsafe___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__3_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_registerInitAttr___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_registerInitAttr___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__6_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_registerInitAttr___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_registerInitAttr___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__8_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__10_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [101, 120, 97, 99, 116, 0],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_registerInitAttr___auto__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__11_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__11_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_registerInitAttr___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__11_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_registerInitAttr___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_registerInitAttr___auto__1___closed__14_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__15_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__15_value)
        as *mut leanh::LeanObject;
static l_Lean_registerInitAttr___auto__1___closed__16_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__16_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__16_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__16_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__16_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_registerInitAttr___auto__1___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__16_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__15_value)
                as *mut leanh::LeanObject,
            7677164612348466033 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__17_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 101, 99, 108, 95, 110, 97, 109, 101, 37, 0],
};
static mut l_Lean_registerInitAttr___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_registerInitAttr___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerInitAttr___auto__1___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_registerInitAttr___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 105, 116, 0]};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15209775132330820936 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [114, 101, 103, 117, 108, 97, 114, 73, 110, 105, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12053862841313483068 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_regularInitAttr: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1___closed__0_value: leanh::LeanStringObject<677> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 677, m_capacity: 677, m_length: 676, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 115, 32, 97, 110, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 46, 32, 73, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 115, 32, 97, 114, 101, 32, 114, 117, 110, 32, 105, 110, 32, 102, 105, 108, 101, 115, 32, 116, 104, 97, 116, 32, 105, 109, 112, 111, 114, 116, 32, 116, 104, 101, 10, 102, 105, 108, 101, 32, 116, 104, 101, 121, 32, 97, 114, 101, 32, 100, 101, 102, 105, 110, 101, 100, 32, 105, 110, 46, 10, 10, 84, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 99, 111, 109, 101, 115, 32, 105, 110, 32, 116, 119, 111, 32, 107, 105, 110, 100, 115, 58, 32, 87, 105, 116, 104, 111, 117, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 44, 32, 116, 104, 101, 32, 116, 97, 103, 103, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 115, 104, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101, 10, 96, 73, 79, 32, 85, 110, 105, 116, 96, 32, 97, 110, 100, 32, 97, 114, 101, 32, 115, 105, 109, 112, 108, 121, 32, 114, 117, 110, 32, 100, 117, 114, 105, 110, 103, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 46, 32, 87, 105, 116, 104, 32, 97, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 97, 115, 32, 97, 32, 97, 114, 103, 117, 109, 101, 110, 116, 44, 32, 116, 104, 101, 10, 116, 97, 103, 103, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 97, 110, 32, 111, 112, 97, 113, 117, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 97, 110, 100, 32, 116, 104, 101, 32, 112, 114, 111, 118, 105, 100, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 97, 110, 32, 97, 99, 116, 105, 111, 110, 32, 105, 110, 32, 96, 73, 79, 96, 10, 116, 104, 97, 116, 32, 114, 101, 116, 117, 114, 110, 115, 32, 97, 32, 118, 97, 108, 117, 101, 32, 111, 102, 32, 116, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 116, 97, 103, 103, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 46, 32, 83, 117, 99, 104, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 115, 32, 115, 116, 111, 114, 101, 10, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 118, 97, 108, 117, 101, 32, 97, 110, 100, 32, 109, 97, 107, 101, 32, 105, 116, 32, 97, 99, 99, 101, 115, 115, 105, 98, 108, 101, 32, 116, 104, 114, 111, 117, 103, 104, 32, 116, 104, 101, 32, 116, 97, 103, 103, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 46, 10, 10, 84, 104, 101, 32, 96, 105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 96, 32, 99, 111, 109, 109, 97, 110, 100, 32, 115, 104, 111, 117, 108, 100, 32, 117, 115, 117, 97, 108, 108, 121, 32, 98, 101, 32, 112, 114, 101, 102, 101, 114, 114, 101, 100, 32, 111, 118, 101, 114, 32, 117, 115, 105, 110, 103, 32, 116, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 100, 105, 114, 101, 99, 116, 108, 121, 46, 10, 0]};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 88 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 101 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 91 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 91 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 101 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 101 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 105, 110, 105, 116, 0]};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4634360312921132838 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [98, 117, 105, 108, 116, 105, 110, 73, 110, 105, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2829956051969401032 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_builtinInitAttr: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1___closed__0_value: leanh::LeanStringObject<178> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 178, m_capacity: 178, m_length: 177, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 115, 32, 97, 32, 98, 117, 105, 108, 116, 105, 110, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 46, 10, 10, 84, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 105, 115, 32, 117, 115, 101, 100, 32, 105, 110, 116, 101, 114, 110, 97, 108, 108, 121, 32, 116, 111, 32, 100, 101, 102, 105, 110, 101, 32, 98, 117, 105, 108, 116, 105, 110, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 115, 32, 102, 111, 114, 32, 98, 111, 111, 116, 115, 116, 114, 97, 112, 112, 105, 110, 103, 32, 97, 110, 100, 10, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 32, 117, 115, 101, 100, 32, 111, 116, 104, 101, 114, 119, 105, 115, 101, 46, 10, 0]};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 103 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 110 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 100 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 100 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 110 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 110 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_declareBuiltin___lam__0___closed__0_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(
                l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___closed__0_value
            ) as *mut leanh::LeanObject,
            4390522573605260290 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_declareBuiltin___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltin___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_declareBuiltin___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_declareBuiltin___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_declareBuiltin___lam__0___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(
                l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType___closed__0_value
            ) as *mut leanh::LeanObject,
            9833841078580172006 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_declareBuiltin___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltin___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_declareBuiltin___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_declareBuiltin___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_declareBuiltin___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_declareBuiltin___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_declareBuiltin___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [95, 114, 101, 103, 66, 117, 105, 108, 116, 105, 110, 0],
    };
static mut l_Lean_declareBuiltin___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltin___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_declareBuiltin___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_declareBuiltin___closed__0_value)
                as *mut leanh::LeanObject,
            12748856906745825949 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_declareBuiltin___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltin___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__1_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__0_value:
    leanh::LeanStringObject<92> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 92,
    m_capacity: 92,
    m_length: 91,
    m_data: [
        96, 101, 110, 97, 98, 108, 101, 73, 110, 105, 116, 105, 97, 108, 105, 122, 101, 114, 115,
        69, 120, 101, 99, 117, 116, 105, 111, 110, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32,
        114, 117, 110, 32, 98, 101, 102, 111, 114, 101, 32, 99, 97, 108, 108, 105, 110, 103, 32,
        96, 105, 109, 112, 111, 114, 116, 77, 111, 100, 117, 108, 101, 115, 32, 40, 108, 111, 97,
        100, 69, 120, 116, 115, 32, 58, 61, 32, 116, 114, 117, 101, 41, 96, 0,
    ],
};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__0_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__2_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(
    mut v_x_1531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1531_) == 5 {
        let mut v_fn_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_fn_1532_ = leanh::lean_ctor_get(v_x_1531_, 0);
        if leanh::lean_obj_tag(v_fn_1532_) == 4 {
            let mut v_declName_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_declName_1533_ = leanh::lean_ctor_get(v_fn_1532_, 0);
            if leanh::lean_obj_tag(v_declName_1533_) == 1 {
                let mut v_pre_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_1534_ = leanh::lean_ctor_get(v_declName_1533_, 0);
                if leanh::lean_obj_tag(v_pre_1534_) == 0 {
                    let mut v_arg_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_str_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1538_: u8 = 0;
                    v_arg_1535_ = leanh::lean_ctor_get(v_x_1531_, 1);
                    v_str_1536_ = leanh::lean_ctor_get(v_declName_1533_, 1);
                    v___x_1537_ =
                        l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___closed__0;
                    v___x_1538_ = lean_string_dec_eq(v_str_1536_, v___x_1537_);
                    if v___x_1538_ == 0 {
                        let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_1539_ = leanh::lean_box(0);
                        return v___x_1539_;
                    } else {
                        let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_inc_ref(v_arg_1535_);
                        v___x_1540_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1540_, 0, v_arg_1535_);
                        return v___x_1540_;
                    }
                } else {
                    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1541_ = leanh::lean_box(0);
                    return v___x_1541_;
                }
            } else {
                let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1542_ = leanh::lean_box(0);
                return v___x_1542_;
            }
        } else {
            let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1543_ = leanh::lean_box(0);
            return v___x_1543_;
        }
    } else {
        let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1544_ = leanh::lean_box(0);
        return v___x_1544_;
    }
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___boxed(
    mut v_x_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1546_ = l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(v_x_1545_);
    leanh::lean_dec_ref(v_x_1545_);
    return v_res_1546_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType(
    mut v_x_1548_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1548_) == 4 {
        let mut v_declName_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_declName_1549_ = leanh::lean_ctor_get(v_x_1548_, 0);
        if leanh::lean_obj_tag(v_declName_1549_) == 1 {
            let mut v_pre_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_1550_ = leanh::lean_ctor_get(v_declName_1549_, 0);
            if leanh::lean_obj_tag(v_pre_1550_) == 0 {
                let mut v_str_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1553_: u8 = 0;
                v_str_1551_ = leanh::lean_ctor_get(v_declName_1549_, 1);
                v___x_1552_ = l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType___closed__0;
                v___x_1553_ = lean_string_dec_eq(v_str_1551_, v___x_1552_);
                return v___x_1553_;
            } else {
                let mut v___x_1554_: u8 = 0;
                v___x_1554_ = 0;
                return v___x_1554_;
            }
        } else {
            let mut v___x_1555_: u8 = 0;
            v___x_1555_ = 0;
            return v___x_1555_;
        }
    } else {
        let mut v___x_1556_: u8 = 0;
        v___x_1556_ = 0;
        return v___x_1556_;
    }
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType___boxed(
    mut v_x_1557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1558_: u8 = 0;
    let mut v_r_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1558_ = l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType(v_x_1557_);
    leanh::lean_dec_ref(v_x_1557_);
    v_r_1559_ = leanh::lean_box((v_res_1558_) as usize);
    return v_r_1559_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit(
    mut v_type_1560_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1561_ = l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(v_type_1560_);
    if leanh::lean_obj_tag(v___x_1561_) == 1 {
        let mut v_val_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1563_: u8 = 0;
        v_val_1562_ = leanh::lean_ctor_get(v___x_1561_, 0);
        leanh::lean_inc(v_val_1562_);
        leanh::lean_dec_ref_known(v___x_1561_, 1);
        v___x_1563_ = l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType(v_val_1562_);
        leanh::lean_dec(v_val_1562_);
        return v___x_1563_;
    } else {
        let mut v___x_1564_: u8 = 0;
        leanh::lean_dec(v___x_1561_);
        v___x_1564_ = 0;
        return v___x_1564_;
    }
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit___boxed(
    mut v_type_1565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1566_: u8 = 0;
    let mut v_r_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1566_ = l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit(v_type_1565_);
    leanh::lean_dec_ref(v_type_1565_);
    v_r_1567_ = leanh::lean_box((v_res_1566_) as usize);
    return v_r_1567_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_runModInitCore___boxed(
    mut v_sym_1570_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1572_ = lean_run_mod_init_core(v_sym_1570_);
    leanh::lean_dec_ref(v_sym_1570_);
    return v_res_1572_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_runModInit(
    mut v_mod_1573_: *mut leanh::LeanObject,
    mut v_pkg_x3f_1574_: *mut leanh::LeanObject,
    mut v_phases_1575_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1577_ =
        l_Lean_mkModuleInitializationFunctionName(v_mod_1573_, v_pkg_x3f_1574_, v_phases_1575_);
    v___x_1578_ = lean_run_mod_init_core(v___x_1577_);
    leanh::lean_dec_ref(v___x_1577_);
    return v___x_1578_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_runModInit___boxed(
    mut v_mod_1579_: *mut leanh::LeanObject,
    mut v_pkg_x3f_1580_: *mut leanh::LeanObject,
    mut v_phases_1581_: *mut leanh::LeanObject,
    mut v_a_1582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phases_boxed_1583_: u8 = 0;
    let mut v_res_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phases_boxed_1583_ = (leanh::lean_unbox(v_phases_1581_) as u8);
    v_res_1584_ = l___private_Lean_Compiler_InitAttr_0__Lean_runModInit(
        v_mod_1579_,
        v_pkg_x3f_1580_,
        v_phases_boxed_1583_,
    );
    leanh::lean_dec(v_pkg_x3f_1580_);
    return v_res_1584_;
}
pub unsafe fn l_Lean_runInit___boxed(
    mut v_env_1590_: *mut leanh::LeanObject,
    mut v_opts_1591_: *mut leanh::LeanObject,
    mut v_decl_1592_: *mut leanh::LeanObject,
    mut v_initDecl_1593_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1595_ = lean_run_init(v_env_1590_, v_opts_1591_, v_decl_1592_, v_initDecl_1593_);
    leanh::lean_dec(v_initDecl_1593_);
    leanh::lean_dec(v_decl_1592_);
    leanh::lean_dec_ref(v_opts_1591_);
    leanh::lean_dec_ref(v_env_1590_);
    return v_res_1595_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3590725331____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Lean_NameSet_empty;
    v___x_1598_ = lean_st_mk_ref(v___x_1597_);
    v___x_1599_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1599_, 0, v___x_1598_);
    return v___x_1599_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3590725331____hygCtx___hyg_2____boxed(
    mut v_a_1600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1601_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3590725331____hygCtx___hyg_2_();
    return v_res_1601_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1602_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1602_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__0);
    v___x_1604_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1604_, 0, v___x_1603_);
    return v___x_1604_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1605_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1);
    v___x_1606_ = leanh::lean_unsigned_to_nat(0);
    v___x_1607_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1607_, 0, v___x_1606_);
    leanh::lean_ctor_set(v___x_1607_, 1, v___x_1606_);
    leanh::lean_ctor_set(v___x_1607_, 2, v___x_1606_);
    leanh::lean_ctor_set(v___x_1607_, 3, v___x_1606_);
    leanh::lean_ctor_set(v___x_1607_, 4, v___x_1605_);
    leanh::lean_ctor_set(v___x_1607_, 5, v___x_1605_);
    leanh::lean_ctor_set(v___x_1607_, 6, v___x_1605_);
    leanh::lean_ctor_set(v___x_1607_, 7, v___x_1605_);
    leanh::lean_ctor_set(v___x_1607_, 8, v___x_1605_);
    leanh::lean_ctor_set(v___x_1607_, 9, v___x_1605_);
    return v___x_1607_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1608_ = leanh::lean_unsigned_to_nat(32);
    v___x_1609_ = lean_mk_empty_array_with_capacity(v___x_1608_);
    v___x_1610_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1610_, 0, v___x_1609_);
    return v___x_1610_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1611_: usize = 0;
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1611_ = 5usize;
    v___x_1612_ = leanh::lean_unsigned_to_nat(0);
    v___x_1613_ = leanh::lean_unsigned_to_nat(32);
    v___x_1614_ = lean_mk_empty_array_with_capacity(v___x_1613_);
    v___x_1615_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__3);
    v___x_1616_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1616_, 0, v___x_1615_);
    leanh::lean_ctor_set(v___x_1616_, 1, v___x_1614_);
    leanh::lean_ctor_set(v___x_1616_, 2, v___x_1612_);
    leanh::lean_ctor_set(v___x_1616_, 3, v___x_1612_);
    leanh::lean_ctor_set_usize(v___x_1616_, 4, v___x_1611_);
    return v___x_1616_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = leanh::lean_box(1);
    v___x_1618_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__4);
    v___x_1619_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1);
    v___x_1620_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1620_, 0, v___x_1619_);
    leanh::lean_ctor_set(v___x_1620_, 1, v___x_1618_);
    leanh::lean_ctor_set(v___x_1620_, 2, v___x_1617_);
    return v___x_1620_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2(
    mut v_msgData_1621_: *mut leanh::LeanObject,
    mut v___y_1622_: *mut leanh::LeanObject,
    mut v___y_1623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = lean_st_ref_get(v___y_1623_);
    v_env_1626_ = leanh::lean_ctor_get(v___x_1625_, 0);
    leanh::lean_inc_ref(v_env_1626_);
    leanh::lean_dec(v___x_1625_);
    v_options_1627_ = leanh::lean_ctor_get(v___y_1622_, 2);
    v___x_1628_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2);
    v___x_1629_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5);
    leanh::lean_inc_ref(v_options_1627_);
    v___x_1630_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1630_, 0, v_env_1626_);
    leanh::lean_ctor_set(v___x_1630_, 1, v___x_1628_);
    leanh::lean_ctor_set(v___x_1630_, 2, v___x_1629_);
    leanh::lean_ctor_set(v___x_1630_, 3, v_options_1627_);
    v___x_1631_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1631_, 0, v___x_1630_);
    leanh::lean_ctor_set(v___x_1631_, 1, v_msgData_1621_);
    v___x_1632_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1632_, 0, v___x_1631_);
    return v___x_1632_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___boxed(
    mut v_msgData_1633_: *mut leanh::LeanObject,
    mut v___y_1634_: *mut leanh::LeanObject,
    mut v___y_1635_: *mut leanh::LeanObject,
    mut v___y_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1637_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2(v_msgData_1633_, v___y_1634_, v___y_1635_);
    leanh::lean_dec(v___y_1635_);
    leanh::lean_dec_ref(v___y_1634_);
    return v_res_1637_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
    mut v_msg_1638_: *mut leanh::LeanObject,
    mut v___y_1639_: *mut leanh::LeanObject,
    mut v___y_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1642_ = leanh::lean_ctor_get(v___y_1639_, 5);
                v___x_1643_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2(v_msg_1638_, v___y_1639_, v___y_1640_);
                v_a_1644_ = leanh::lean_ctor_get(v___x_1643_, 0);
                v_isSharedCheck_1652_ = (!leanh::lean_is_exclusive(v___x_1643_)) as u8;
                if v_isSharedCheck_1652_ == 0 {
                    v___x_1646_ = v___x_1643_;
                    v_isShared_1647_ = v_isSharedCheck_1652_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1644_);
                    leanh::lean_dec(v___x_1643_);
                    v___x_1646_ = leanh::lean_box(0);
                    v_isShared_1647_ = v_isSharedCheck_1652_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1642_);
                v___x_1648_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1648_, 0, v_ref_1642_);
                leanh::lean_ctor_set(v___x_1648_, 1, v_a_1644_);
                if v_isShared_1647_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1646_, 1);
                    leanh::lean_ctor_set(v___x_1646_, 0, v___x_1648_);
                    v___x_1650_ = v___x_1646_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1651_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
                    v___x_1650_ = v_reuseFailAlloc_1651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg___boxed(
    mut v_msg_1653_: *mut leanh::LeanObject,
    mut v___y_1654_: *mut leanh::LeanObject,
    mut v___y_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1657_ = l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
        v_msg_1653_,
        v___y_1654_,
        v___y_1655_,
    );
    leanh::lean_dec(v___y_1655_);
    leanh::lean_dec_ref(v___y_1654_);
    return v_res_1657_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8___redArg(
    mut v_ref_1658_: *mut leanh::LeanObject,
    mut v_msg_1659_: *mut leanh::LeanObject,
    mut v___y_1660_: *mut leanh::LeanObject,
    mut v___y_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1675_: u8 = 0;
    let mut v_cancelTk_x3f_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1677_: u8 = 0;
    let mut v_inheritedTraceOptions_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1663_ = leanh::lean_ctor_get(v___y_1660_, 0);
    v_fileMap_1664_ = leanh::lean_ctor_get(v___y_1660_, 1);
    v_options_1665_ = leanh::lean_ctor_get(v___y_1660_, 2);
    v_currRecDepth_1666_ = leanh::lean_ctor_get(v___y_1660_, 3);
    v_maxRecDepth_1667_ = leanh::lean_ctor_get(v___y_1660_, 4);
    v_ref_1668_ = leanh::lean_ctor_get(v___y_1660_, 5);
    v_currNamespace_1669_ = leanh::lean_ctor_get(v___y_1660_, 6);
    v_openDecls_1670_ = leanh::lean_ctor_get(v___y_1660_, 7);
    v_initHeartbeats_1671_ = leanh::lean_ctor_get(v___y_1660_, 8);
    v_maxHeartbeats_1672_ = leanh::lean_ctor_get(v___y_1660_, 9);
    v_quotContext_1673_ = leanh::lean_ctor_get(v___y_1660_, 10);
    v_currMacroScope_1674_ = leanh::lean_ctor_get(v___y_1660_, 11);
    v_diag_1675_ = leanh::lean_ctor_get_uint8(
        v___y_1660_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1676_ = leanh::lean_ctor_get(v___y_1660_, 12);
    v_suppressElabErrors_1677_ = leanh::lean_ctor_get_uint8(
        v___y_1660_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1678_ = leanh::lean_ctor_get(v___y_1660_, 13);
    v_ref_1679_ = l_Lean_replaceRef(v_ref_1658_, v_ref_1668_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_1678_);
    leanh::lean_inc(v_cancelTk_x3f_1676_);
    leanh::lean_inc(v_currMacroScope_1674_);
    leanh::lean_inc(v_quotContext_1673_);
    leanh::lean_inc(v_maxHeartbeats_1672_);
    leanh::lean_inc(v_initHeartbeats_1671_);
    leanh::lean_inc(v_openDecls_1670_);
    leanh::lean_inc(v_currNamespace_1669_);
    leanh::lean_inc(v_maxRecDepth_1667_);
    leanh::lean_inc(v_currRecDepth_1666_);
    leanh::lean_inc_ref(v_options_1665_);
    leanh::lean_inc_ref(v_fileMap_1664_);
    leanh::lean_inc_ref(v_fileName_1663_);
    v___x_1680_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1680_, 0, v_fileName_1663_);
    leanh::lean_ctor_set(v___x_1680_, 1, v_fileMap_1664_);
    leanh::lean_ctor_set(v___x_1680_, 2, v_options_1665_);
    leanh::lean_ctor_set(v___x_1680_, 3, v_currRecDepth_1666_);
    leanh::lean_ctor_set(v___x_1680_, 4, v_maxRecDepth_1667_);
    leanh::lean_ctor_set(v___x_1680_, 5, v_ref_1679_);
    leanh::lean_ctor_set(v___x_1680_, 6, v_currNamespace_1669_);
    leanh::lean_ctor_set(v___x_1680_, 7, v_openDecls_1670_);
    leanh::lean_ctor_set(v___x_1680_, 8, v_initHeartbeats_1671_);
    leanh::lean_ctor_set(v___x_1680_, 9, v_maxHeartbeats_1672_);
    leanh::lean_ctor_set(v___x_1680_, 10, v_quotContext_1673_);
    leanh::lean_ctor_set(v___x_1680_, 11, v_currMacroScope_1674_);
    leanh::lean_ctor_set(v___x_1680_, 12, v_cancelTk_x3f_1676_);
    leanh::lean_ctor_set(v___x_1680_, 13, v_inheritedTraceOptions_1678_);
    leanh::lean_ctor_set_uint8(
        v___x_1680_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_1675_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1680_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1677_,
    );
    v___x_1681_ = l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
        v_msg_1659_,
        v___x_1680_,
        v___y_1661_,
    );
    leanh::lean_dec_ref_known(v___x_1680_, 14);
    return v___x_1681_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8___redArg___boxed(
    mut v_ref_1682_: *mut leanh::LeanObject,
    mut v_msg_1683_: *mut leanh::LeanObject,
    mut v___y_1684_: *mut leanh::LeanObject,
    mut v___y_1685_: *mut leanh::LeanObject,
    mut v___y_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1687_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8___redArg(v_ref_1682_, v_msg_1683_, v___y_1684_, v___y_1685_);
    leanh::lean_dec(v___y_1685_);
    leanh::lean_dec_ref(v___y_1684_);
    leanh::lean_dec(v_ref_1682_);
    return v_res_1687_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1689_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__0;
    v___x_1690_ = l_Lean_stringToMessageData(v___x_1689_);
    return v___x_1690_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1692_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__2;
    v___x_1693_ = l_Lean_stringToMessageData(v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1695_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__4;
    v___x_1696_ = l_Lean_stringToMessageData(v___x_1695_);
    return v___x_1696_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__6;
    v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
    return v___x_1699_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1701_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__8;
    v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
    return v___x_1702_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1704_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__10;
    v___x_1705_ = l_Lean_stringToMessageData(v___x_1704_);
    return v___x_1705_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1707_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__12;
    v___x_1708_ = l_Lean_stringToMessageData(v___x_1707_);
    return v___x_1708_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg(
    mut v_msg_1709_: *mut leanh::LeanObject,
    mut v_declHint_1710_: *mut leanh::LeanObject,
    mut v___y_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v_isExporting_1716_: u8 = 0;
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: u8 = 0;
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1738_: u8 = 0;
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: u8 = 0;
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1713_ = lean_st_ref_get(v___y_1711_);
                v_env_1714_ = leanh::lean_ctor_get(v___x_1713_, 0);
                leanh::lean_inc_ref(v_env_1714_);
                leanh::lean_dec(v___x_1713_);
                v___x_1715_ = l_Lean_Name_isAnonymous(v_declHint_1710_);
                if v___x_1715_ == 0 {
                    v_isExporting_1716_ = leanh::lean_ctor_get_uint8(
                        v_env_1714_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1716_ == 0 {
                        leanh::lean_dec_ref(v_env_1714_);
                        leanh::lean_dec(v_declHint_1710_);
                        v___x_1717_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1717_, 0, v_msg_1709_);
                        return v___x_1717_;
                    } else {
                        leanh::lean_inc_ref(v_env_1714_);
                        v___x_1718_ = l_Lean_Environment_setExporting(v_env_1714_, v___x_1715_);
                        leanh::lean_inc(v_declHint_1710_);
                        leanh::lean_inc_ref(v___x_1718_);
                        v___x_1719_ = l_Lean_Environment_contains(
                            v___x_1718_,
                            v_declHint_1710_,
                            v_isExporting_1716_,
                        );
                        if v___x_1719_ == 0 {
                            leanh::lean_dec_ref(v___x_1718_);
                            leanh::lean_dec_ref(v_env_1714_);
                            leanh::lean_dec(v_declHint_1710_);
                            v___x_1720_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1720_, 0, v_msg_1709_);
                            return v___x_1720_;
                        } else {
                            v___x_1721_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2);
                            v___x_1722_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5);
                            v___x_1723_ = l_Lean_Options_empty;
                            v___x_1724_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1724_, 0, v___x_1718_);
                            leanh::lean_ctor_set(v___x_1724_, 1, v___x_1721_);
                            leanh::lean_ctor_set(v___x_1724_, 2, v___x_1722_);
                            leanh::lean_ctor_set(v___x_1724_, 3, v___x_1723_);
                            leanh::lean_inc(v_declHint_1710_);
                            v___x_1725_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1710_, v___x_1715_);
                            v_c_1726_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_1726_, 0, v___x_1724_);
                            leanh::lean_ctor_set(v_c_1726_, 1, v___x_1725_);
                            v___x_1727_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1714_,
                                v_declHint_1710_,
                            );
                            if leanh::lean_obj_tag(v___x_1727_) == 0 {
                                leanh::lean_dec_ref(v_env_1714_);
                                leanh::lean_dec(v_declHint_1710_);
                                v___x_1728_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1);
                                v___x_1729_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1729_, 0, v___x_1728_);
                                leanh::lean_ctor_set(v___x_1729_, 1, v_c_1726_);
                                v___x_1730_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__3);
                                v___x_1731_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1731_, 0, v___x_1729_);
                                leanh::lean_ctor_set(v___x_1731_, 1, v___x_1730_);
                                v___x_1732_ = l_Lean_MessageData_note(v___x_1731_);
                                v___x_1733_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1733_, 0, v_msg_1709_);
                                leanh::lean_ctor_set(v___x_1733_, 1, v___x_1732_);
                                v___x_1734_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1734_, 0, v___x_1733_);
                                return v___x_1734_;
                            } else {
                                v_val_1735_ = leanh::lean_ctor_get(v___x_1727_, 0);
                                v_isSharedCheck_1770_ =
                                    (!leanh::lean_is_exclusive(v___x_1727_)) as u8;
                                if v_isSharedCheck_1770_ == 0 {
                                    v___x_1737_ = v___x_1727_;
                                    v_isShared_1738_ = v_isSharedCheck_1770_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1735_);
                                    leanh::lean_dec(v___x_1727_);
                                    v___x_1737_ = leanh::lean_box(0);
                                    v_isShared_1738_ = v_isSharedCheck_1770_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1714_);
                    leanh::lean_dec(v_declHint_1710_);
                    v___x_1771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1771_, 0, v_msg_1709_);
                    return v___x_1771_;
                }
            }
            1 => {
                v___x_1739_ = leanh::lean_box(0);
                v___x_1740_ = l_Lean_Environment_header(v_env_1714_);
                leanh::lean_dec_ref(v_env_1714_);
                v___x_1741_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1740_);
                v_mod_1742_ = lean_array_get(v___x_1739_, v___x_1741_, v_val_1735_);
                leanh::lean_dec(v_val_1735_);
                leanh::lean_dec_ref(v___x_1741_);
                v___x_1743_ = l_Lean_isPrivateName(v_declHint_1710_);
                leanh::lean_dec(v_declHint_1710_);
                if v___x_1743_ == 0 {
                    v___x_1744_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__5);
                    v___x_1745_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1745_, 0, v___x_1744_);
                    leanh::lean_ctor_set(v___x_1745_, 1, v_c_1726_);
                    v___x_1746_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__7);
                    v___x_1747_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1747_, 0, v___x_1745_);
                    leanh::lean_ctor_set(v___x_1747_, 1, v___x_1746_);
                    v___x_1748_ = l_Lean_MessageData_ofName(v_mod_1742_);
                    v___x_1749_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1749_, 0, v___x_1747_);
                    leanh::lean_ctor_set(v___x_1749_, 1, v___x_1748_);
                    v___x_1750_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__9);
                    v___x_1751_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1751_, 0, v___x_1749_);
                    leanh::lean_ctor_set(v___x_1751_, 1, v___x_1750_);
                    v___x_1752_ = l_Lean_MessageData_note(v___x_1751_);
                    v___x_1753_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1753_, 0, v_msg_1709_);
                    leanh::lean_ctor_set(v___x_1753_, 1, v___x_1752_);
                    if v_isShared_1738_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1737_, 0);
                        leanh::lean_ctor_set(v___x_1737_, 0, v___x_1753_);
                        v___x_1755_ = v___x_1737_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1756_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
                        v___x_1755_ = v_reuseFailAlloc_1756_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1757_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1);
                    v___x_1758_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1758_, 0, v___x_1757_);
                    leanh::lean_ctor_set(v___x_1758_, 1, v_c_1726_);
                    v___x_1759_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__11);
                    v___x_1760_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1760_, 0, v___x_1758_);
                    leanh::lean_ctor_set(v___x_1760_, 1, v___x_1759_);
                    v___x_1761_ = l_Lean_MessageData_ofName(v_mod_1742_);
                    v___x_1762_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_1760_);
                    leanh::lean_ctor_set(v___x_1762_, 1, v___x_1761_);
                    v___x_1763_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__13);
                    v___x_1764_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1764_, 0, v___x_1762_);
                    leanh::lean_ctor_set(v___x_1764_, 1, v___x_1763_);
                    v___x_1765_ = l_Lean_MessageData_note(v___x_1764_);
                    v___x_1766_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1766_, 0, v_msg_1709_);
                    leanh::lean_ctor_set(v___x_1766_, 1, v___x_1765_);
                    if v_isShared_1738_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1737_, 0);
                        leanh::lean_ctor_set(v___x_1737_, 0, v___x_1766_);
                        v___x_1768_ = v___x_1737_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1769_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
                        v___x_1768_ = v_reuseFailAlloc_1769_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1755_;
            }
            3 => {
                return v___x_1768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___boxed(
    mut v_msg_1772_: *mut leanh::LeanObject,
    mut v_declHint_1773_: *mut leanh::LeanObject,
    mut v___y_1774_: *mut leanh::LeanObject,
    mut v___y_1775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1776_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg(v_msg_1772_, v_declHint_1773_, v___y_1774_);
    leanh::lean_dec(v___y_1774_);
    return v_res_1776_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7(
    mut v_msg_1777_: *mut leanh::LeanObject,
    mut v_declHint_1778_: *mut leanh::LeanObject,
    mut v___y_1779_: *mut leanh::LeanObject,
    mut v___y_1780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1786_: u8 = 0;
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1782_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg(v_msg_1777_, v_declHint_1778_, v___y_1780_);
                v_a_1783_ = leanh::lean_ctor_get(v___x_1782_, 0);
                v_isSharedCheck_1792_ = (!leanh::lean_is_exclusive(v___x_1782_)) as u8;
                if v_isSharedCheck_1792_ == 0 {
                    v___x_1785_ = v___x_1782_;
                    v_isShared_1786_ = v_isSharedCheck_1792_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1783_);
                    leanh::lean_dec(v___x_1782_);
                    v___x_1785_ = leanh::lean_box(0);
                    v_isShared_1786_ = v_isSharedCheck_1792_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1787_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1788_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1788_, 0, v___x_1787_);
                leanh::lean_ctor_set(v___x_1788_, 1, v_a_1783_);
                if v_isShared_1786_ == 0 {
                    leanh::lean_ctor_set(v___x_1785_, 0, v___x_1788_);
                    v___x_1790_ = v___x_1785_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
                    v___x_1790_ = v_reuseFailAlloc_1791_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7___boxed(
    mut v_msg_1793_: *mut leanh::LeanObject,
    mut v_declHint_1794_: *mut leanh::LeanObject,
    mut v___y_1795_: *mut leanh::LeanObject,
    mut v___y_1796_: *mut leanh::LeanObject,
    mut v___y_1797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7(v_msg_1793_, v_declHint_1794_, v___y_1795_, v___y_1796_);
    leanh::lean_dec(v___y_1796_);
    leanh::lean_dec_ref(v___y_1795_);
    return v_res_1798_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6___redArg(
    mut v_ref_1799_: *mut leanh::LeanObject,
    mut v_msg_1800_: *mut leanh::LeanObject,
    mut v_declHint_1801_: *mut leanh::LeanObject,
    mut v___y_1802_: *mut leanh::LeanObject,
    mut v___y_1803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1805_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7(v_msg_1800_, v_declHint_1801_, v___y_1802_, v___y_1803_);
    v_a_1806_ = leanh::lean_ctor_get(v___x_1805_, 0);
    leanh::lean_inc(v_a_1806_);
    leanh::lean_dec_ref(v___x_1805_);
    v___x_1807_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8___redArg(v_ref_1799_, v_a_1806_, v___y_1802_, v___y_1803_);
    return v___x_1807_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6___redArg___boxed(
    mut v_ref_1808_: *mut leanh::LeanObject,
    mut v_msg_1809_: *mut leanh::LeanObject,
    mut v_declHint_1810_: *mut leanh::LeanObject,
    mut v___y_1811_: *mut leanh::LeanObject,
    mut v___y_1812_: *mut leanh::LeanObject,
    mut v___y_1813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1814_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1808_, v_msg_1809_, v_declHint_1810_, v___y_1811_, v___y_1812_);
    leanh::lean_dec(v___y_1812_);
    leanh::lean_dec_ref(v___y_1811_);
    leanh::lean_dec(v_ref_1808_);
    return v_res_1814_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1816_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1817_ = l_Lean_stringToMessageData(v___x_1816_);
    return v___x_1817_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1819_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1820_ = l_Lean_stringToMessageData(v___x_1819_);
    return v___x_1820_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1821_: *mut leanh::LeanObject,
    mut v_constName_1822_: *mut leanh::LeanObject,
    mut v___y_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: u8 = 0;
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1826_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1827_ = 0;
    leanh::lean_inc(v_constName_1822_);
    v___x_1828_ = l_Lean_MessageData_ofConstName(v_constName_1822_, v___x_1827_);
    v___x_1829_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1829_, 0, v___x_1826_);
    leanh::lean_ctor_set(v___x_1829_, 1, v___x_1828_);
    v___x_1830_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1831_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1831_, 0, v___x_1829_);
    leanh::lean_ctor_set(v___x_1831_, 1, v___x_1830_);
    v___x_1832_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1821_, v___x_1831_, v_constName_1822_, v___y_1823_, v___y_1824_);
    return v___x_1832_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1833_: *mut leanh::LeanObject,
    mut v_constName_1834_: *mut leanh::LeanObject,
    mut v___y_1835_: *mut leanh::LeanObject,
    mut v___y_1836_: *mut leanh::LeanObject,
    mut v___y_1837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1838_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg(v_ref_1833_, v_constName_1834_, v___y_1835_, v___y_1836_);
    leanh::lean_dec(v___y_1836_);
    leanh::lean_dec_ref(v___y_1835_);
    leanh::lean_dec(v_ref_1833_);
    return v_res_1838_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0___redArg(
    mut v_constName_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1843_ = leanh::lean_ctor_get(v___y_1840_, 5);
    v___x_1844_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg(v_ref_1843_, v_constName_1839_, v___y_1840_, v___y_1841_);
    return v___x_1844_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0___redArg___boxed(
    mut v_constName_1845_: *mut leanh::LeanObject,
    mut v___y_1846_: *mut leanh::LeanObject,
    mut v___y_1847_: *mut leanh::LeanObject,
    mut v___y_1848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1849_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0___redArg(v_constName_1845_, v___y_1846_, v___y_1847_);
    leanh::lean_dec(v___y_1847_);
    leanh::lean_dec_ref(v___y_1846_);
    return v_res_1849_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0(
    mut v_constName_1850_: *mut leanh::LeanObject,
    mut v___y_1851_: *mut leanh::LeanObject,
    mut v___y_1852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1854_ = lean_st_ref_get(v___y_1852_);
                v_env_1855_ = leanh::lean_ctor_get(v___x_1854_, 0);
                leanh::lean_inc_ref(v_env_1855_);
                leanh::lean_dec(v___x_1854_);
                v___x_1856_ = 0;
                leanh::lean_inc(v_constName_1850_);
                v___x_1857_ =
                    l_Lean_Environment_find_x3f(v_env_1855_, v_constName_1850_, v___x_1856_);
                if leanh::lean_obj_tag(v___x_1857_) == 0 {
                    v___x_1858_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0___redArg(v_constName_1850_, v___y_1851_, v___y_1852_);
                    return v___x_1858_;
                } else {
                    leanh::lean_dec(v_constName_1850_);
                    v_val_1859_ = leanh::lean_ctor_get(v___x_1857_, 0);
                    v_isSharedCheck_1866_ = (!leanh::lean_is_exclusive(v___x_1857_)) as u8;
                    if v_isSharedCheck_1866_ == 0 {
                        v___x_1861_ = v___x_1857_;
                        v_isShared_1862_ = v_isSharedCheck_1866_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1859_);
                        leanh::lean_dec(v___x_1857_);
                        v___x_1861_ = leanh::lean_box(0);
                        v_isShared_1862_ = v_isSharedCheck_1866_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1862_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1861_, 0);
                    v___x_1864_ = v___x_1861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1865_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_val_1859_);
                    v___x_1864_ = v_reuseFailAlloc_1865_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1864_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0___boxed(
    mut v_constName_1867_: *mut leanh::LeanObject,
    mut v___y_1868_: *mut leanh::LeanObject,
    mut v___y_1869_: *mut leanh::LeanObject,
    mut v___y_1870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1871_ = l_Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0(
        v_constName_1867_,
        v___y_1868_,
        v___y_1869_,
    );
    leanh::lean_dec(v___y_1869_);
    leanh::lean_dec_ref(v___y_1868_);
    return v_res_1871_;
}
pub unsafe fn _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1873_ = l_Lean_registerInitAttrUnsafe___lam__0___closed__0;
    v___x_1874_ = l_Lean_stringToMessageData(v___x_1873_);
    return v___x_1874_;
}
pub unsafe fn _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1876_ = l_Lean_registerInitAttrUnsafe___lam__0___closed__2;
    v___x_1877_ = l_Lean_stringToMessageData(v___x_1876_);
    return v___x_1877_;
}
pub unsafe fn _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1879_ = l_Lean_registerInitAttrUnsafe___lam__0___closed__4;
    v___x_1880_ = l_Lean_stringToMessageData(v___x_1879_);
    return v___x_1880_;
}
pub unsafe fn _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1882_ = l_Lean_registerInitAttrUnsafe___lam__0___closed__6;
    v___x_1883_ = l_Lean_stringToMessageData(v___x_1882_);
    return v___x_1883_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__0(
    mut v_declName_1884_: *mut leanh::LeanObject,
    mut v_stx_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
    mut v___y_1887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1933_: u8 = 0;
    let mut v_a_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1941_: u8 = 0;
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut v_a_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1946_: u8 = 0;
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1950_: u8 = 0;
    let mut v_a_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1954_: u8 = 0;
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1958_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1889_ = l_Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0(
                    v_declName_1884_,
                    v___y_1886_,
                    v___y_1887_,
                );
                if leanh::lean_obj_tag(v___x_1889_) == 0 {
                    v_a_1890_ = leanh::lean_ctor_get(v___x_1889_, 0);
                    leanh::lean_inc(v_a_1890_);
                    leanh::lean_dec_ref_known(v___x_1889_, 1);
                    v___x_1891_ = l_Lean_Attribute_Builtin_getIdent_x3f(
                        v_stx_1885_,
                        v___y_1886_,
                        v___y_1887_,
                    );
                    if leanh::lean_obj_tag(v___x_1891_) == 0 {
                        v_a_1892_ = leanh::lean_ctor_get(v___x_1891_, 0);
                        v_isSharedCheck_1942_ =
                            (!leanh::lean_is_exclusive(v___x_1891_)) as u8;
                        if v_isSharedCheck_1942_ == 0 {
                            v___x_1894_ = v___x_1891_;
                            v_isShared_1895_ = v_isSharedCheck_1942_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1892_);
                            leanh::lean_dec(v___x_1891_);
                            v___x_1894_ = leanh::lean_box(0);
                            v_isShared_1895_ = v_isSharedCheck_1942_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1890_);
                        v_a_1943_ = leanh::lean_ctor_get(v___x_1891_, 0);
                        v_isSharedCheck_1950_ =
                            (!leanh::lean_is_exclusive(v___x_1891_)) as u8;
                        if v_isSharedCheck_1950_ == 0 {
                            v___x_1945_ = v___x_1891_;
                            v_isShared_1946_ = v_isSharedCheck_1950_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1943_);
                            leanh::lean_dec(v___x_1891_);
                            v___x_1945_ = leanh::lean_box(0);
                            v_isShared_1946_ = v_isSharedCheck_1950_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_stx_1885_);
                    v_a_1951_ = leanh::lean_ctor_get(v___x_1889_, 0);
                    v_isSharedCheck_1958_ = (!leanh::lean_is_exclusive(v___x_1889_)) as u8;
                    if v_isSharedCheck_1958_ == 0 {
                        v___x_1953_ = v___x_1889_;
                        v_isShared_1954_ = v_isSharedCheck_1958_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1951_);
                        leanh::lean_dec(v___x_1889_);
                        v___x_1953_ = leanh::lean_box(0);
                        v_isShared_1954_ = v_isSharedCheck_1958_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1892_) == 0 {
                    v___x_1896_ = l_Lean_ConstantInfo_type(v_a_1890_);
                    leanh::lean_dec(v_a_1890_);
                    v___x_1897_ = l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit(v___x_1896_);
                    leanh::lean_dec_ref(v___x_1896_);
                    if v___x_1897_ == 0 {
                        leanh::lean_del_object(v___x_1894_);
                        v___x_1898_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_registerInitAttrUnsafe___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_registerInitAttrUnsafe___lam__0___closed__1_once
                            ),
                            _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__1,
                        );
                        v___x_1899_ =
                            l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
                                v___x_1898_,
                                v___y_1886_,
                                v___y_1887_,
                            );
                        return v___x_1899_;
                    } else {
                        v___x_1900_ = leanh::lean_box(0);
                        if v_isShared_1895_ == 0 {
                            leanh::lean_ctor_set(v___x_1894_, 0, v___x_1900_);
                            v___x_1902_ = v___x_1894_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1903_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
                            v___x_1902_ = v_reuseFailAlloc_1903_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1894_);
                    v_val_1904_ = leanh::lean_ctor_get(v_a_1892_, 0);
                    leanh::lean_inc(v_val_1904_);
                    leanh::lean_dec_ref_known(v_a_1892_, 1);
                    v___x_1905_ = leanh::lean_box(0);
                    v___x_1906_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                        v_val_1904_,
                        v___x_1905_,
                        v___y_1886_,
                        v___y_1887_,
                    );
                    if leanh::lean_obj_tag(v___x_1906_) == 0 {
                        v_a_1907_ = leanh::lean_ctor_get(v___x_1906_, 0);
                        leanh::lean_inc_n(v_a_1907_, 2);
                        leanh::lean_dec_ref_known(v___x_1906_, 1);
                        v___x_1908_ =
                            l_Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0(
                                v_a_1907_,
                                v___y_1886_,
                                v___y_1887_,
                            );
                        if leanh::lean_obj_tag(v___x_1908_) == 0 {
                            v_a_1909_ = leanh::lean_ctor_get(v___x_1908_, 0);
                            v_isSharedCheck_1933_ =
                                (!leanh::lean_is_exclusive(v___x_1908_)) as u8;
                            if v_isSharedCheck_1933_ == 0 {
                                v___x_1911_ = v___x_1908_;
                                v_isShared_1912_ = v_isSharedCheck_1933_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1909_);
                                leanh::lean_dec(v___x_1908_);
                                v___x_1911_ = leanh::lean_box(0);
                                v_isShared_1912_ = v_isSharedCheck_1933_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1907_);
                            leanh::lean_dec(v_a_1890_);
                            v_a_1934_ = leanh::lean_ctor_get(v___x_1908_, 0);
                            v_isSharedCheck_1941_ =
                                (!leanh::lean_is_exclusive(v___x_1908_)) as u8;
                            if v_isSharedCheck_1941_ == 0 {
                                v___x_1936_ = v___x_1908_;
                                v_isShared_1937_ = v_isSharedCheck_1941_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1934_);
                                leanh::lean_dec(v___x_1908_);
                                v___x_1936_ = leanh::lean_box(0);
                                v_isShared_1937_ = v_isSharedCheck_1941_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1890_);
                        return v___x_1906_;
                    }
                }
            }
            2 => {
                return v___x_1902_;
            }
            3 => {
                v___x_1913_ = l_Lean_ConstantInfo_type(v_a_1909_);
                leanh::lean_dec(v_a_1909_);
                v___x_1914_ = l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(v___x_1913_);
                leanh::lean_dec_ref(v___x_1913_);
                if leanh::lean_obj_tag(v___x_1914_) == 0 {
                    leanh::lean_del_object(v___x_1911_);
                    leanh::lean_dec(v_a_1890_);
                    v___x_1915_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_registerInitAttrUnsafe___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_registerInitAttrUnsafe___lam__0___closed__3_once
                        ),
                        _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__3,
                    );
                    v___x_1916_ = l_Lean_MessageData_ofName(v_a_1907_);
                    v___x_1917_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1917_, 0, v___x_1915_);
                    leanh::lean_ctor_set(v___x_1917_, 1, v___x_1916_);
                    v___x_1918_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_registerInitAttrUnsafe___lam__0___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_registerInitAttrUnsafe___lam__0___closed__5_once
                        ),
                        _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__5,
                    );
                    v___x_1919_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1919_, 0, v___x_1917_);
                    leanh::lean_ctor_set(v___x_1919_, 1, v___x_1918_);
                    v___x_1920_ =
                        l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
                            v___x_1919_,
                            v___y_1886_,
                            v___y_1887_,
                        );
                    return v___x_1920_;
                } else {
                    v_val_1921_ = leanh::lean_ctor_get(v___x_1914_, 0);
                    leanh::lean_inc(v_val_1921_);
                    leanh::lean_dec_ref_known(v___x_1914_, 1);
                    v___x_1922_ = l_Lean_ConstantInfo_type(v_a_1890_);
                    leanh::lean_dec(v_a_1890_);
                    v___x_1923_ = lean_expr_eqv(v___x_1922_, v_val_1921_);
                    leanh::lean_dec(v_val_1921_);
                    leanh::lean_dec_ref(v___x_1922_);
                    if v___x_1923_ == 0 {
                        leanh::lean_del_object(v___x_1911_);
                        v___x_1924_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_registerInitAttrUnsafe___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_registerInitAttrUnsafe___lam__0___closed__3_once
                            ),
                            _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__3,
                        );
                        v___x_1925_ = l_Lean_MessageData_ofName(v_a_1907_);
                        v___x_1926_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1926_, 0, v___x_1924_);
                        leanh::lean_ctor_set(v___x_1926_, 1, v___x_1925_);
                        v___x_1927_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_registerInitAttrUnsafe___lam__0___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_registerInitAttrUnsafe___lam__0___closed__7_once
                            ),
                            _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__7,
                        );
                        v___x_1928_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1928_, 0, v___x_1926_);
                        leanh::lean_ctor_set(v___x_1928_, 1, v___x_1927_);
                        v___x_1929_ =
                            l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
                                v___x_1928_,
                                v___y_1886_,
                                v___y_1887_,
                            );
                        return v___x_1929_;
                    } else {
                        if v_isShared_1912_ == 0 {
                            leanh::lean_ctor_set(v___x_1911_, 0, v_a_1907_);
                            v___x_1931_ = v___x_1911_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1932_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1907_);
                            v___x_1931_ = v_reuseFailAlloc_1932_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_1931_;
            }
            5 => {
                if v_isShared_1937_ == 0 {
                    v___x_1939_ = v___x_1936_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1940_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
                    v___x_1939_ = v_reuseFailAlloc_1940_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1939_;
            }
            7 => {
                if v_isShared_1946_ == 0 {
                    v___x_1948_ = v___x_1945_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1949_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
                    v___x_1948_ = v_reuseFailAlloc_1949_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1948_;
            }
            9 => {
                if v_isShared_1954_ == 0 {
                    v___x_1956_ = v___x_1953_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1957_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
                    v___x_1956_ = v_reuseFailAlloc_1957_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1956_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__0___boxed(
    mut v_declName_1959_: *mut leanh::LeanObject,
    mut v_stx_1960_: *mut leanh::LeanObject,
    mut v___y_1961_: *mut leanh::LeanObject,
    mut v___y_1962_: *mut leanh::LeanObject,
    mut v___y_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1964_ = l_Lean_registerInitAttrUnsafe___lam__0(
        v_declName_1959_,
        v_stx_1960_,
        v___y_1961_,
        v___y_1962_,
    );
    leanh::lean_dec(v___y_1962_);
    leanh::lean_dec_ref(v___y_1961_);
    return v_res_1964_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___lam__0(
    mut v___y_1965_: *mut leanh::LeanObject,
    mut v_isExporting_1966_: u8,
    mut v___x_1967_: *mut leanh::LeanObject,
    mut v_a_x3f_1968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut v_unused_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1970_ = lean_st_ref_take(v___y_1965_);
                v_env_1971_ = leanh::lean_ctor_get(v___x_1970_, 0);
                v_nextMacroScope_1972_ = leanh::lean_ctor_get(v___x_1970_, 1);
                v_ngen_1973_ = leanh::lean_ctor_get(v___x_1970_, 2);
                v_auxDeclNGen_1974_ = leanh::lean_ctor_get(v___x_1970_, 3);
                v_traceState_1975_ = leanh::lean_ctor_get(v___x_1970_, 4);
                v_messages_1976_ = leanh::lean_ctor_get(v___x_1970_, 6);
                v_infoState_1977_ = leanh::lean_ctor_get(v___x_1970_, 7);
                v_snapshotTasks_1978_ = leanh::lean_ctor_get(v___x_1970_, 8);
                v_isSharedCheck_1989_ = (!leanh::lean_is_exclusive(v___x_1970_)) as u8;
                if v_isSharedCheck_1989_ == 0 {
                    v_unused_1990_ = leanh::lean_ctor_get(v___x_1970_, 5);
                    leanh::lean_dec(v_unused_1990_);
                    v___x_1980_ = v___x_1970_;
                    v_isShared_1981_ = v_isSharedCheck_1989_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1978_);
                    leanh::lean_inc(v_infoState_1977_);
                    leanh::lean_inc(v_messages_1976_);
                    leanh::lean_inc(v_traceState_1975_);
                    leanh::lean_inc(v_auxDeclNGen_1974_);
                    leanh::lean_inc(v_ngen_1973_);
                    leanh::lean_inc(v_nextMacroScope_1972_);
                    leanh::lean_inc(v_env_1971_);
                    leanh::lean_dec(v___x_1970_);
                    v___x_1980_ = leanh::lean_box(0);
                    v_isShared_1981_ = v_isSharedCheck_1989_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1982_ = l_Lean_Environment_setExporting(v_env_1971_, v_isExporting_1966_);
                if v_isShared_1981_ == 0 {
                    leanh::lean_ctor_set(v___x_1980_, 5, v___x_1967_);
                    leanh::lean_ctor_set(v___x_1980_, 0, v___x_1982_);
                    v___x_1984_ = v___x_1980_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1988_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1982_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_nextMacroScope_1972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_ngen_1973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 3, v_auxDeclNGen_1974_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 4, v_traceState_1975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 5, v___x_1967_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 6, v_messages_1976_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 7, v_infoState_1977_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 8, v_snapshotTasks_1978_);
                    v___x_1984_ = v_reuseFailAlloc_1988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1985_ = lean_st_ref_set(v___y_1965_, v___x_1984_);
                v___x_1986_ = leanh::lean_box(0);
                v___x_1987_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1987_, 0, v___x_1986_);
                return v___x_1987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___lam__0___boxed(
    mut v___y_1991_: *mut leanh::LeanObject,
    mut v_isExporting_1992_: *mut leanh::LeanObject,
    mut v___x_1993_: *mut leanh::LeanObject,
    mut v_a_x3f_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_1996_: u8 = 0;
    let mut v_res_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_1996_ = (leanh::lean_unbox(v_isExporting_1992_) as u8);
    v_res_1997_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___lam__0(v___y_1991_, v_isExporting_boxed_1996_, v___x_1993_, v_a_x3f_1994_);
    leanh::lean_dec(v_a_x3f_1994_);
    leanh::lean_dec(v___y_1991_);
    return v_res_1997_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1998_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1998_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1999_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__0);
    v___x_2000_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2000_, 0, v___x_1999_);
    return v___x_2000_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__1);
    v___x_2002_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2002_, 0, v___x_2001_);
    leanh::lean_ctor_set(v___x_2002_, 1, v___x_2001_);
    return v___x_2002_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg(
    mut v_x_2003_: *mut leanh::LeanObject,
    mut v_isExporting_2004_: u8,
    mut v___y_2005_: *mut leanh::LeanObject,
    mut v___y_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2010_: u8 = 0;
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2022_: u8 = 0;
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2042_: u8 = 0;
    let mut v_unused_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut v_a_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut v_unused_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_unused_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2008_ = lean_st_ref_get(v___y_2006_);
                v_env_2009_ = leanh::lean_ctor_get(v___x_2008_, 0);
                leanh::lean_inc_ref(v_env_2009_);
                leanh::lean_dec(v___x_2008_);
                v_isExporting_2010_ = leanh::lean_ctor_get_uint8(
                    v_env_2009_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_2009_);
                v___x_2011_ = lean_st_ref_take(v___y_2006_);
                v_env_2012_ = leanh::lean_ctor_get(v___x_2011_, 0);
                v_nextMacroScope_2013_ = leanh::lean_ctor_get(v___x_2011_, 1);
                v_ngen_2014_ = leanh::lean_ctor_get(v___x_2011_, 2);
                v_auxDeclNGen_2015_ = leanh::lean_ctor_get(v___x_2011_, 3);
                v_traceState_2016_ = leanh::lean_ctor_get(v___x_2011_, 4);
                v_messages_2017_ = leanh::lean_ctor_get(v___x_2011_, 6);
                v_infoState_2018_ = leanh::lean_ctor_get(v___x_2011_, 7);
                v_snapshotTasks_2019_ = leanh::lean_ctor_get(v___x_2011_, 8);
                v_isSharedCheck_2058_ = (!leanh::lean_is_exclusive(v___x_2011_)) as u8;
                if v_isSharedCheck_2058_ == 0 {
                    v_unused_2059_ = leanh::lean_ctor_get(v___x_2011_, 5);
                    leanh::lean_dec(v_unused_2059_);
                    v___x_2021_ = v___x_2011_;
                    v_isShared_2022_ = v_isSharedCheck_2058_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2019_);
                    leanh::lean_inc(v_infoState_2018_);
                    leanh::lean_inc(v_messages_2017_);
                    leanh::lean_inc(v_traceState_2016_);
                    leanh::lean_inc(v_auxDeclNGen_2015_);
                    leanh::lean_inc(v_ngen_2014_);
                    leanh::lean_inc(v_nextMacroScope_2013_);
                    leanh::lean_inc(v_env_2012_);
                    leanh::lean_dec(v___x_2011_);
                    v___x_2021_ = leanh::lean_box(0);
                    v_isShared_2022_ = v_isSharedCheck_2058_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2023_ = l_Lean_Environment_setExporting(v_env_2012_, v_isExporting_2004_);
                v___x_2024_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2);
                if v_isShared_2022_ == 0 {
                    leanh::lean_ctor_set(v___x_2021_, 5, v___x_2024_);
                    leanh::lean_ctor_set(v___x_2021_, 0, v___x_2023_);
                    v___x_2026_ = v___x_2021_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2023_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_nextMacroScope_2013_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_ngen_2014_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 3, v_auxDeclNGen_2015_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 4, v_traceState_2016_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 5, v___x_2024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 6, v_messages_2017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 7, v_infoState_2018_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 8, v_snapshotTasks_2019_);
                    v___x_2026_ = v_reuseFailAlloc_2057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2027_ = lean_st_ref_set(v___y_2006_, v___x_2026_);
                leanh::lean_inc(v___y_2006_);
                leanh::lean_inc_ref(v___y_2005_);
                v_r_2028_ = leanh::lean_apply_3(
                    v_x_2003_,
                    v___y_2005_,
                    v___y_2006_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_2028_) == 0 {
                    v_a_2029_ = leanh::lean_ctor_get(v_r_2028_, 0);
                    v_isSharedCheck_2045_ = (!leanh::lean_is_exclusive(v_r_2028_)) as u8;
                    if v_isSharedCheck_2045_ == 0 {
                        v___x_2031_ = v_r_2028_;
                        v_isShared_2032_ = v_isSharedCheck_2045_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2029_);
                        leanh::lean_dec(v_r_2028_);
                        v___x_2031_ = leanh::lean_box(0);
                        v_isShared_2032_ = v_isSharedCheck_2045_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2046_ = leanh::lean_ctor_get(v_r_2028_, 0);
                    leanh::lean_inc(v_a_2046_);
                    leanh::lean_dec_ref_known(v_r_2028_, 1);
                    v___x_2047_ = leanh::lean_box(0);
                    v___x_2048_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___lam__0(v___y_2006_, v_isExporting_2010_, v___x_2024_, v___x_2047_);
                    v_isSharedCheck_2055_ = (!leanh::lean_is_exclusive(v___x_2048_)) as u8;
                    if v_isSharedCheck_2055_ == 0 {
                        v_unused_2056_ = leanh::lean_ctor_get(v___x_2048_, 0);
                        leanh::lean_dec(v_unused_2056_);
                        v___x_2050_ = v___x_2048_;
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2048_);
                        v___x_2050_ = leanh::lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_a_2029_);
                if v_isShared_2032_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2031_, 1);
                    v___x_2034_ = v___x_2031_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2029_);
                    v___x_2034_ = v_reuseFailAlloc_2044_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2035_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___lam__0(v___y_2006_, v_isExporting_2010_, v___x_2024_, v___x_2034_);
                leanh::lean_dec_ref(v___x_2034_);
                v_isSharedCheck_2042_ = (!leanh::lean_is_exclusive(v___x_2035_)) as u8;
                if v_isSharedCheck_2042_ == 0 {
                    v_unused_2043_ = leanh::lean_ctor_get(v___x_2035_, 0);
                    leanh::lean_dec(v_unused_2043_);
                    v___x_2037_ = v___x_2035_;
                    v_isShared_2038_ = v_isSharedCheck_2042_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2035_);
                    v___x_2037_ = leanh::lean_box(0);
                    v_isShared_2038_ = v_isSharedCheck_2042_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2038_ == 0 {
                    leanh::lean_ctor_set(v___x_2037_, 0, v_a_2029_);
                    v___x_2040_ = v___x_2037_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2041_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2029_);
                    v___x_2040_ = v_reuseFailAlloc_2041_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2040_;
            }
            7 => {
                if v_isShared_2051_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2050_, 1);
                    leanh::lean_ctor_set(v___x_2050_, 0, v_a_2046_);
                    v___x_2053_ = v___x_2050_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2046_);
                    v___x_2053_ = v_reuseFailAlloc_2054_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___boxed(
    mut v_x_2060_: *mut leanh::LeanObject,
    mut v_isExporting_2061_: *mut leanh::LeanObject,
    mut v___y_2062_: *mut leanh::LeanObject,
    mut v___y_2063_: *mut leanh::LeanObject,
    mut v___y_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_2065_: u8 = 0;
    let mut v_res_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2065_ = (leanh::lean_unbox(v_isExporting_2061_) as u8);
    v_res_2066_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg(v_x_2060_, v_isExporting_boxed_2065_, v___y_2062_, v___y_2063_);
    leanh::lean_dec(v___y_2063_);
    leanh::lean_dec_ref(v___y_2062_);
    return v_res_2066_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2___redArg(
    mut v_x_2067_: *mut leanh::LeanObject,
    mut v_when_2068_: u8,
    mut v___y_2069_: *mut leanh::LeanObject,
    mut v___y_2070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_when_2068_ == 0 {
        let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v___y_2070_);
        leanh::lean_inc_ref(v___y_2069_);
        v___x_2072_ = leanh::lean_apply_3(
            v_x_2067_,
            v___y_2069_,
            v___y_2070_,
            leanh::lean_box(0),
        );
        return v___x_2072_;
    } else {
        let mut v___x_2073_: u8 = 0;
        let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2073_ = 0;
        v___x_2074_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg(v_x_2067_, v___x_2073_, v___y_2069_, v___y_2070_);
        return v___x_2074_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2___redArg___boxed(
    mut v_x_2075_: *mut leanh::LeanObject,
    mut v_when_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_2080_: u8 = 0;
    let mut v_res_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_2080_ = (leanh::lean_unbox(v_when_2076_) as u8);
    v_res_2081_ = l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2___redArg(
        v_x_2075_,
        v_when_boxed_2080_,
        v___y_2077_,
        v___y_2078_,
    );
    leanh::lean_dec(v___y_2078_);
    leanh::lean_dec_ref(v___y_2077_);
    return v_res_2081_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__1(
    mut v_declName_2082_: *mut leanh::LeanObject,
    mut v_stx_2083_: *mut leanh::LeanObject,
    mut v___y_2084_: *mut leanh::LeanObject,
    mut v___y_2085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: u8 = 0;
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2087_ = leanh::lean_alloc_closure(
        l_Lean_registerInitAttrUnsafe___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2087_, 0, v_declName_2082_);
    leanh::lean_closure_set(v___f_2087_, 1, v_stx_2083_);
    v___x_2088_ = 1;
    v___x_2089_ = l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2___redArg(
        v___f_2087_,
        v___x_2088_,
        v___y_2084_,
        v___y_2085_,
    );
    return v___x_2089_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__1___boxed(
    mut v_declName_2090_: *mut leanh::LeanObject,
    mut v_stx_2091_: *mut leanh::LeanObject,
    mut v___y_2092_: *mut leanh::LeanObject,
    mut v___y_2093_: *mut leanh::LeanObject,
    mut v___y_2094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2095_ = l_Lean_registerInitAttrUnsafe___lam__1(
        v_declName_2090_,
        v_stx_2091_,
        v___y_2092_,
        v___y_2093_,
    );
    leanh::lean_dec(v___y_2093_);
    leanh::lean_dec_ref(v___y_2092_);
    return v_res_2095_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__2(
    mut v_x_2096_: *mut leanh::LeanObject,
    mut v_x_2097_: *mut leanh::LeanObject,
    mut v_x_2098_: *mut leanh::LeanObject,
    mut v___y_2099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ = leanh::lean_box(0);
    v___x_2102_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2102_, 0, v___x_2101_);
    return v___x_2102_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__2___boxed(
    mut v_x_2103_: *mut leanh::LeanObject,
    mut v_x_2104_: *mut leanh::LeanObject,
    mut v_x_2105_: *mut leanh::LeanObject,
    mut v___y_2106_: *mut leanh::LeanObject,
    mut v___y_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2108_ =
        l_Lean_registerInitAttrUnsafe___lam__2(v_x_2103_, v_x_2104_, v_x_2105_, v___y_2106_);
    leanh::lean_dec(v___y_2106_);
    leanh::lean_dec_ref(v_x_2105_);
    leanh::lean_dec(v_x_2104_);
    leanh::lean_dec(v_x_2103_);
    return v_res_2108_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__3(
    mut v_runAfterImport_2109_: u8,
    mut v___x_2110_: u8,
    mut v_env_2111_: *mut leanh::LeanObject,
    mut v_declName_2112_: *mut leanh::LeanObject,
    mut v_x_2113_: *mut leanh::LeanObject,
) -> u8 {
    if v_runAfterImport_2109_ == 0 {
        leanh::lean_dec(v_declName_2112_);
        leanh::lean_dec_ref(v_env_2111_);
        return v___x_2110_;
    } else {
        let mut v___x_2114_: u8 = 0;
        v___x_2114_ = l_Lean_isMarkedMeta(v_env_2111_, v_declName_2112_);
        return v___x_2114_;
    }
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__3___boxed(
    mut v_runAfterImport_2115_: *mut leanh::LeanObject,
    mut v___x_2116_: *mut leanh::LeanObject,
    mut v_env_2117_: *mut leanh::LeanObject,
    mut v_declName_2118_: *mut leanh::LeanObject,
    mut v_x_2119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_runAfterImport_boxed_2120_: u8 = 0;
    let mut v___x_5418__boxed_2121_: u8 = 0;
    let mut v_res_2122_: u8 = 0;
    let mut v_r_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_runAfterImport_boxed_2120_ = (leanh::lean_unbox(v_runAfterImport_2115_) as u8);
    v___x_5418__boxed_2121_ = (leanh::lean_unbox(v___x_2116_) as u8);
    v_res_2122_ = l_Lean_registerInitAttrUnsafe___lam__3(
        v_runAfterImport_boxed_2120_,
        v___x_5418__boxed_2121_,
        v_env_2117_,
        v_declName_2118_,
        v_x_2119_,
    );
    leanh::lean_dec(v_x_2119_);
    v_r_2123_ = leanh::lean_box((v_res_2122_) as usize);
    return v_r_2123_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe(
    mut v_attrName_2127_: *mut leanh::LeanObject,
    mut v_runAfterImport_2128_: u8,
    mut v_ref_2129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: u8 = 0;
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2131_ = l_Lean_registerInitAttrUnsafe___closed__0;
    v___f_2132_ = l_Lean_registerInitAttrUnsafe___closed__1;
    v___x_2133_ = l_Lean_registerInitAttrUnsafe___closed__2;
    v___x_2134_ = 0;
    v___x_2135_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_2135_, 0, v_ref_2129_);
    leanh::lean_ctor_set(v___x_2135_, 1, v_attrName_2127_);
    leanh::lean_ctor_set(v___x_2135_, 2, v___x_2133_);
    leanh::lean_ctor_set_uint8(
        v___x_2135_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_2134_,
    );
    v___x_2136_ = 1;
    v___x_2137_ = leanh::lean_box((v_runAfterImport_2128_) as usize);
    v___x_2138_ = leanh::lean_box((v___x_2136_) as usize);
    v___f_2139_ = leanh::lean_alloc_closure(
        l_Lean_registerInitAttrUnsafe___lam__3___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2139_, 0, v___x_2137_);
    leanh::lean_closure_set(v___f_2139_, 1, v___x_2138_);
    v___x_2140_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
    leanh::lean_ctor_set(v___x_2140_, 0, v___x_2135_);
    leanh::lean_ctor_set(v___x_2140_, 1, v___f_2131_);
    leanh::lean_ctor_set(v___x_2140_, 2, v___f_2132_);
    leanh::lean_ctor_set(v___x_2140_, 3, v___f_2139_);
    leanh::lean_ctor_set_uint8(
        v___x_2140_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        v___x_2136_,
    );
    v___x_2141_ = l_Lean_registerParametricAttribute___redArg(v___x_2140_);
    return v___x_2141_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___boxed(
    mut v_attrName_2142_: *mut leanh::LeanObject,
    mut v_runAfterImport_2143_: *mut leanh::LeanObject,
    mut v_ref_2144_: *mut leanh::LeanObject,
    mut v_a_2145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_runAfterImport_boxed_2146_: u8 = 0;
    let mut v_res_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_runAfterImport_boxed_2146_ = (leanh::lean_unbox(v_runAfterImport_2143_) as u8);
    v_res_2147_ =
        l_Lean_registerInitAttrUnsafe(v_attrName_2142_, v_runAfterImport_boxed_2146_, v_ref_2144_);
    return v_res_2147_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1(
    mut v_00_u03b1_2148_: *mut leanh::LeanObject,
    mut v_msg_2149_: *mut leanh::LeanObject,
    mut v___y_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
        v_msg_2149_,
        v___y_2150_,
        v___y_2151_,
    );
    return v___x_2153_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___boxed(
    mut v_00_u03b1_2154_: *mut leanh::LeanObject,
    mut v_msg_2155_: *mut leanh::LeanObject,
    mut v___y_2156_: *mut leanh::LeanObject,
    mut v___y_2157_: *mut leanh::LeanObject,
    mut v___y_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2159_ = l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1(
        v_00_u03b1_2154_,
        v_msg_2155_,
        v___y_2156_,
        v___y_2157_,
    );
    leanh::lean_dec(v___y_2157_);
    leanh::lean_dec_ref(v___y_2156_);
    return v_res_2159_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4(
    mut v_00_u03b1_2160_: *mut leanh::LeanObject,
    mut v_x_2161_: *mut leanh::LeanObject,
    mut v_isExporting_2162_: u8,
    mut v___y_2163_: *mut leanh::LeanObject,
    mut v___y_2164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2166_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg(v_x_2161_, v_isExporting_2162_, v___y_2163_, v___y_2164_);
    return v___x_2166_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___boxed(
    mut v_00_u03b1_2167_: *mut leanh::LeanObject,
    mut v_x_2168_: *mut leanh::LeanObject,
    mut v_isExporting_2169_: *mut leanh::LeanObject,
    mut v___y_2170_: *mut leanh::LeanObject,
    mut v___y_2171_: *mut leanh::LeanObject,
    mut v___y_2172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_2173_: u8 = 0;
    let mut v_res_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2173_ = (leanh::lean_unbox(v_isExporting_2169_) as u8);
    v_res_2174_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4(v_00_u03b1_2167_, v_x_2168_, v_isExporting_boxed_2173_, v___y_2170_, v___y_2171_);
    leanh::lean_dec(v___y_2171_);
    leanh::lean_dec_ref(v___y_2170_);
    return v_res_2174_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2(
    mut v_00_u03b1_2175_: *mut leanh::LeanObject,
    mut v_x_2176_: *mut leanh::LeanObject,
    mut v_when_2177_: u8,
    mut v___y_2178_: *mut leanh::LeanObject,
    mut v___y_2179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2181_ = l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2___redArg(
        v_x_2176_,
        v_when_2177_,
        v___y_2178_,
        v___y_2179_,
    );
    return v___x_2181_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2___boxed(
    mut v_00_u03b1_2182_: *mut leanh::LeanObject,
    mut v_x_2183_: *mut leanh::LeanObject,
    mut v_when_2184_: *mut leanh::LeanObject,
    mut v___y_2185_: *mut leanh::LeanObject,
    mut v___y_2186_: *mut leanh::LeanObject,
    mut v___y_2187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_2188_: u8 = 0;
    let mut v_res_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_2188_ = (leanh::lean_unbox(v_when_2184_) as u8);
    v_res_2189_ = l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2(
        v_00_u03b1_2182_,
        v_x_2183_,
        v_when_boxed_2188_,
        v___y_2185_,
        v___y_2186_,
    );
    leanh::lean_dec(v___y_2186_);
    leanh::lean_dec_ref(v___y_2185_);
    return v_res_2189_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0(
    mut v_00_u03b1_2190_: *mut leanh::LeanObject,
    mut v_constName_2191_: *mut leanh::LeanObject,
    mut v___y_2192_: *mut leanh::LeanObject,
    mut v___y_2193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2195_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0___redArg(v_constName_2191_, v___y_2192_, v___y_2193_);
    return v___x_2195_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0___boxed(
    mut v_00_u03b1_2196_: *mut leanh::LeanObject,
    mut v_constName_2197_: *mut leanh::LeanObject,
    mut v___y_2198_: *mut leanh::LeanObject,
    mut v___y_2199_: *mut leanh::LeanObject,
    mut v___y_2200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0(v_00_u03b1_2196_, v_constName_2197_, v___y_2198_, v___y_2199_);
    leanh::lean_dec(v___y_2199_);
    leanh::lean_dec_ref(v___y_2198_);
    return v_res_2201_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2202_: *mut leanh::LeanObject,
    mut v_ref_2203_: *mut leanh::LeanObject,
    mut v_constName_2204_: *mut leanh::LeanObject,
    mut v___y_2205_: *mut leanh::LeanObject,
    mut v___y_2206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2208_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg(v_ref_2203_, v_constName_2204_, v___y_2205_, v___y_2206_);
    return v___x_2208_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2209_: *mut leanh::LeanObject,
    mut v_ref_2210_: *mut leanh::LeanObject,
    mut v_constName_2211_: *mut leanh::LeanObject,
    mut v___y_2212_: *mut leanh::LeanObject,
    mut v___y_2213_: *mut leanh::LeanObject,
    mut v___y_2214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2215_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_2209_, v_ref_2210_, v_constName_2211_, v___y_2212_, v___y_2213_);
    leanh::lean_dec(v___y_2213_);
    leanh::lean_dec_ref(v___y_2212_);
    leanh::lean_dec(v_ref_2210_);
    return v_res_2215_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6(
    mut v_00_u03b1_2216_: *mut leanh::LeanObject,
    mut v_ref_2217_: *mut leanh::LeanObject,
    mut v_msg_2218_: *mut leanh::LeanObject,
    mut v_declHint_2219_: *mut leanh::LeanObject,
    mut v___y_2220_: *mut leanh::LeanObject,
    mut v___y_2221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2223_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_2217_, v_msg_2218_, v_declHint_2219_, v___y_2220_, v___y_2221_);
    return v___x_2223_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6___boxed(
    mut v_00_u03b1_2224_: *mut leanh::LeanObject,
    mut v_ref_2225_: *mut leanh::LeanObject,
    mut v_msg_2226_: *mut leanh::LeanObject,
    mut v_declHint_2227_: *mut leanh::LeanObject,
    mut v___y_2228_: *mut leanh::LeanObject,
    mut v___y_2229_: *mut leanh::LeanObject,
    mut v___y_2230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2231_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_2224_, v_ref_2225_, v_msg_2226_, v_declHint_2227_, v___y_2228_, v___y_2229_);
    leanh::lean_dec(v___y_2229_);
    leanh::lean_dec_ref(v___y_2228_);
    leanh::lean_dec(v_ref_2225_);
    return v_res_2231_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8(
    mut v_msg_2232_: *mut leanh::LeanObject,
    mut v_declHint_2233_: *mut leanh::LeanObject,
    mut v___y_2234_: *mut leanh::LeanObject,
    mut v___y_2235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2237_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg(v_msg_2232_, v_declHint_2233_, v___y_2235_);
    return v___x_2237_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___boxed(
    mut v_msg_2238_: *mut leanh::LeanObject,
    mut v_declHint_2239_: *mut leanh::LeanObject,
    mut v___y_2240_: *mut leanh::LeanObject,
    mut v___y_2241_: *mut leanh::LeanObject,
    mut v___y_2242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2243_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8(v_msg_2238_, v_declHint_2239_, v___y_2240_, v___y_2241_);
    leanh::lean_dec(v___y_2241_);
    leanh::lean_dec_ref(v___y_2240_);
    return v_res_2243_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8(
    mut v_00_u03b1_2244_: *mut leanh::LeanObject,
    mut v_ref_2245_: *mut leanh::LeanObject,
    mut v_msg_2246_: *mut leanh::LeanObject,
    mut v___y_2247_: *mut leanh::LeanObject,
    mut v___y_2248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2250_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8___redArg(v_ref_2245_, v_msg_2246_, v___y_2247_, v___y_2248_);
    return v___x_2250_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8___boxed(
    mut v_00_u03b1_2251_: *mut leanh::LeanObject,
    mut v_ref_2252_: *mut leanh::LeanObject,
    mut v_msg_2253_: *mut leanh::LeanObject,
    mut v___y_2254_: *mut leanh::LeanObject,
    mut v___y_2255_: *mut leanh::LeanObject,
    mut v___y_2256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2257_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8(v_00_u03b1_2251_, v_ref_2252_, v_msg_2253_, v___y_2254_, v___y_2255_);
    leanh::lean_dec(v___y_2255_);
    leanh::lean_dec_ref(v___y_2254_);
    leanh::lean_dec(v_ref_2252_);
    return v_res_2257_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__12() -> *mut leanh::LeanObject
{
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2284_ = l_Lean_registerInitAttr___auto__1___closed__10;
    v___x_2285_ = l_Lean_mkAtom(v___x_2284_);
    return v___x_2285_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__13() -> *mut leanh::LeanObject
{
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2286_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__12_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__12,
    );
    v___x_2287_ = l_Lean_registerInitAttr___auto__1___closed__5;
    v___x_2288_ = lean_array_push(v___x_2287_, v___x_2286_);
    return v___x_2288_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__18() -> *mut leanh::LeanObject
{
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2297_ = l_Lean_registerInitAttr___auto__1___closed__17;
    v___x_2298_ = l_Lean_mkAtom(v___x_2297_);
    return v___x_2298_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__19() -> *mut leanh::LeanObject
{
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__18_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__18,
    );
    v___x_2300_ = l_Lean_registerInitAttr___auto__1___closed__5;
    v___x_2301_ = lean_array_push(v___x_2300_, v___x_2299_);
    return v___x_2301_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__20() -> *mut leanh::LeanObject
{
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__19_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__19,
    );
    v___x_2303_ = l_Lean_registerInitAttr___auto__1___closed__16;
    v___x_2304_ = leanh::lean_box(2);
    v___x_2305_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2305_, 0, v___x_2304_);
    leanh::lean_ctor_set(v___x_2305_, 1, v___x_2303_);
    leanh::lean_ctor_set(v___x_2305_, 2, v___x_2302_);
    return v___x_2305_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__21() -> *mut leanh::LeanObject
{
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2306_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__20_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__20,
    );
    v___x_2307_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__13_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__13,
    );
    v___x_2308_ = lean_array_push(v___x_2307_, v___x_2306_);
    return v___x_2308_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__22() -> *mut leanh::LeanObject
{
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2309_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__21_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__21,
    );
    v___x_2310_ = l_Lean_registerInitAttr___auto__1___closed__11;
    v___x_2311_ = leanh::lean_box(2);
    v___x_2312_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2312_, 0, v___x_2311_);
    leanh::lean_ctor_set(v___x_2312_, 1, v___x_2310_);
    leanh::lean_ctor_set(v___x_2312_, 2, v___x_2309_);
    return v___x_2312_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__23() -> *mut leanh::LeanObject
{
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2313_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__22_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__22,
    );
    v___x_2314_ = l_Lean_registerInitAttr___auto__1___closed__5;
    v___x_2315_ = lean_array_push(v___x_2314_, v___x_2313_);
    return v___x_2315_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__24() -> *mut leanh::LeanObject
{
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2316_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__23_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__23,
    );
    v___x_2317_ = l_Lean_registerInitAttr___auto__1___closed__9;
    v___x_2318_ = leanh::lean_box(2);
    v___x_2319_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2319_, 0, v___x_2318_);
    leanh::lean_ctor_set(v___x_2319_, 1, v___x_2317_);
    leanh::lean_ctor_set(v___x_2319_, 2, v___x_2316_);
    return v___x_2319_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__25() -> *mut leanh::LeanObject
{
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2320_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__24_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__24,
    );
    v___x_2321_ = l_Lean_registerInitAttr___auto__1___closed__5;
    v___x_2322_ = lean_array_push(v___x_2321_, v___x_2320_);
    return v___x_2322_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__26() -> *mut leanh::LeanObject
{
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2323_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__25_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__25,
    );
    v___x_2324_ = l_Lean_registerInitAttr___auto__1___closed__7;
    v___x_2325_ = leanh::lean_box(2);
    v___x_2326_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2326_, 0, v___x_2325_);
    leanh::lean_ctor_set(v___x_2326_, 1, v___x_2324_);
    leanh::lean_ctor_set(v___x_2326_, 2, v___x_2323_);
    return v___x_2326_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__27() -> *mut leanh::LeanObject
{
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__26_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__26,
    );
    v___x_2328_ = l_Lean_registerInitAttr___auto__1___closed__5;
    v___x_2329_ = lean_array_push(v___x_2328_, v___x_2327_);
    return v___x_2329_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__28() -> *mut leanh::LeanObject
{
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2330_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__27_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__27,
    );
    v___x_2331_ = l_Lean_registerInitAttr___auto__1___closed__4;
    v___x_2332_ = leanh::lean_box(2);
    v___x_2333_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2333_, 0, v___x_2332_);
    leanh::lean_ctor_set(v___x_2333_, 1, v___x_2331_);
    leanh::lean_ctor_set(v___x_2333_, 2, v___x_2330_);
    return v___x_2333_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2334_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__28_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__28,
    );
    return v___x_2334_;
}
pub unsafe fn l_Lean_registerInitAttr(
    mut v_attrName_2335_: *mut leanh::LeanObject,
    mut v_runAfterImport_2336_: u8,
    mut v_ref_2337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2339_ =
        l_Lean_registerInitAttrUnsafe(v_attrName_2335_, v_runAfterImport_2336_, v_ref_2337_);
    return v___x_2339_;
}
pub unsafe fn l_Lean_registerInitAttr___boxed(
    mut v_attrName_2340_: *mut leanh::LeanObject,
    mut v_runAfterImport_2341_: *mut leanh::LeanObject,
    mut v_ref_2342_: *mut leanh::LeanObject,
    mut v_a_2343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_runAfterImport_boxed_2344_: u8 = 0;
    let mut v_res_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_runAfterImport_boxed_2344_ = (leanh::lean_unbox(v_runAfterImport_2341_) as u8);
    v_res_2345_ =
        l_Lean_registerInitAttr(v_attrName_2340_, v_runAfterImport_boxed_2344_, v_ref_2342_);
    return v_res_2345_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2354_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_;
    v___x_2355_ = 1;
    v___x_2356_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_;
    v___x_2357_ = l_Lean_registerInitAttrUnsafe(v___x_2354_, v___x_2355_, v___x_2356_);
    return v___x_2357_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2____boxed(
    mut v_a_2358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2359_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_();
    return v_res_2359_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1()
-> *mut leanh::LeanObject {
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2362_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_;
    v___x_2363_ = l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1___closed__0;
    v___x_2364_ = l_Lean_addBuiltinDocString(v___x_2362_, v___x_2363_);
    return v___x_2364_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1___boxed(
    mut v_a_2365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2366_ = l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1();
    return v_res_2366_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2393_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_;
    v___x_2394_ = l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__6;
    v___x_2395_ = l_Lean_addBuiltinDeclarationRanges(v___x_2393_, v___x_2394_);
    return v___x_2395_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___boxed(
    mut v_a_2396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2397_ = l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3();
    return v_res_2397_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: u8 = 0;
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_;
    v___x_2407_ = 0;
    v___x_2408_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_;
    v___x_2409_ = l_Lean_registerInitAttrUnsafe(v___x_2406_, v___x_2407_, v___x_2408_);
    return v___x_2409_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2____boxed(
    mut v_a_2410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2411_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_();
    return v_res_2411_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1()
-> *mut leanh::LeanObject {
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2414_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_;
    v___x_2415_ = l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1___closed__0;
    v___x_2416_ = l_Lean_addBuiltinDocString(v___x_2414_, v___x_2415_);
    return v___x_2416_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1___boxed(
    mut v_a_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2418_ = l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1();
    return v_res_2418_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2445_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_;
    v___x_2446_ = l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__6;
    v___x_2447_ = l_Lean_addBuiltinDeclarationRanges(v___x_2445_, v___x_2446_);
    return v___x_2447_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___boxed(
    mut v_a_2448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2449_ = l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3();
    return v_res_2449_;
}
pub unsafe fn l_Lean_getInitFnNameForCore_x3f(
    mut v_env_2450_: *mut leanh::LeanObject,
    mut v_attr_2451_: *mut leanh::LeanObject,
    mut v_fn_2452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2453_ = leanh::lean_box(0);
    v___x_2454_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
        v___x_2453_,
        v_attr_2451_,
        v_env_2450_,
        v_fn_2452_,
    );
    if leanh::lean_obj_tag(v___x_2454_) == 1 {
        let mut v_val_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2455_ = leanh::lean_ctor_get(v___x_2454_, 0);
        leanh::lean_inc(v_val_2455_);
        if leanh::lean_obj_tag(v_val_2455_) == 0 {
            let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_2454_, 1);
            v___x_2456_ = leanh::lean_box(0);
            return v___x_2456_;
        } else {
            leanh::lean_dec(v_val_2455_);
            return v___x_2454_;
        }
    } else {
        let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_2454_);
        v___x_2457_ = leanh::lean_box(0);
        return v___x_2457_;
    }
}
pub unsafe fn l_Lean_getInitFnNameForCore_x3f___boxed(
    mut v_env_2458_: *mut leanh::LeanObject,
    mut v_attr_2459_: *mut leanh::LeanObject,
    mut v_fn_2460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2461_ = l_Lean_getInitFnNameForCore_x3f(v_env_2458_, v_attr_2459_, v_fn_2460_);
    leanh::lean_dec_ref(v_attr_2459_);
    return v_res_2461_;
}
pub unsafe fn l_Lean_getBuiltinInitFnNameFor_x3f(
    mut v_env_2462_: *mut leanh::LeanObject,
    mut v_fn_2463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2464_ = l_Lean_builtinInitAttr;
    v___x_2465_ = l_Lean_getInitFnNameForCore_x3f(v_env_2462_, v___x_2464_, v_fn_2463_);
    return v___x_2465_;
}
pub unsafe fn lean_get_regular_init_fn_name_for(
    mut v_env_2466_: *mut leanh::LeanObject,
    mut v_fn_2467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = l_Lean_regularInitAttr;
    v___x_2469_ = l_Lean_getInitFnNameForCore_x3f(v_env_2466_, v___x_2468_, v_fn_2467_);
    return v___x_2469_;
}
pub unsafe fn lean_get_init_fn_name_for(
    mut v_env_2470_: *mut leanh::LeanObject,
    mut v_fn_2471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_fn_2471_);
    leanh::lean_inc_ref(v_env_2470_);
    v___x_2472_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_2470_, v_fn_2471_);
    if leanh::lean_obj_tag(v___x_2472_) == 0 {
        let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2473_ = lean_get_regular_init_fn_name_for(v_env_2470_, v_fn_2471_);
        return v___x_2473_;
    } else {
        leanh::lean_dec(v_fn_2471_);
        leanh::lean_dec_ref(v_env_2470_);
        return v___x_2472_;
    }
}
pub unsafe fn l_Lean_isIOUnitInitFnCore(
    mut v_env_2474_: *mut leanh::LeanObject,
    mut v_attr_2475_: *mut leanh::LeanObject,
    mut v_fn_2476_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2477_ = leanh::lean_box(0);
    v___x_2478_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
        v___x_2477_,
        v_attr_2475_,
        v_env_2474_,
        v_fn_2476_,
    );
    if leanh::lean_obj_tag(v___x_2478_) == 1 {
        let mut v_val_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2479_ = leanh::lean_ctor_get(v___x_2478_, 0);
        leanh::lean_inc(v_val_2479_);
        leanh::lean_dec_ref_known(v___x_2478_, 1);
        if leanh::lean_obj_tag(v_val_2479_) == 0 {
            let mut v___x_2480_: u8 = 0;
            v___x_2480_ = 1;
            return v___x_2480_;
        } else {
            let mut v___x_2481_: u8 = 0;
            leanh::lean_dec(v_val_2479_);
            v___x_2481_ = 0;
            return v___x_2481_;
        }
    } else {
        let mut v___x_2482_: u8 = 0;
        leanh::lean_dec(v___x_2478_);
        v___x_2482_ = 0;
        return v___x_2482_;
    }
}
pub unsafe fn l_Lean_isIOUnitInitFnCore___boxed(
    mut v_env_2483_: *mut leanh::LeanObject,
    mut v_attr_2484_: *mut leanh::LeanObject,
    mut v_fn_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2486_: u8 = 0;
    let mut v_r_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2486_ = l_Lean_isIOUnitInitFnCore(v_env_2483_, v_attr_2484_, v_fn_2485_);
    leanh::lean_dec_ref(v_attr_2484_);
    v_r_2487_ = leanh::lean_box((v_res_2486_) as usize);
    return v_r_2487_;
}
pub unsafe fn l_Lean_isIOUnitRegularInitFn(
    mut v_env_2488_: *mut leanh::LeanObject,
    mut v_fn_2489_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    v___x_2490_ = l_Lean_regularInitAttr;
    v___x_2491_ = l_Lean_isIOUnitInitFnCore(v_env_2488_, v___x_2490_, v_fn_2489_);
    return v___x_2491_;
}
pub unsafe fn l_Lean_isIOUnitRegularInitFn___boxed(
    mut v_env_2492_: *mut leanh::LeanObject,
    mut v_fn_2493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2494_: u8 = 0;
    let mut v_r_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2494_ = l_Lean_isIOUnitRegularInitFn(v_env_2492_, v_fn_2493_);
    v_r_2495_ = leanh::lean_box((v_res_2494_) as usize);
    return v_r_2495_;
}
pub unsafe fn l_Lean_isIOUnitBuiltinInitFn(
    mut v_env_2496_: *mut leanh::LeanObject,
    mut v_fn_2497_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: u8 = 0;
    v___x_2498_ = l_Lean_builtinInitAttr;
    v___x_2499_ = l_Lean_isIOUnitInitFnCore(v_env_2496_, v___x_2498_, v_fn_2497_);
    return v___x_2499_;
}
pub unsafe fn l_Lean_isIOUnitBuiltinInitFn___boxed(
    mut v_env_2500_: *mut leanh::LeanObject,
    mut v_fn_2501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2502_: u8 = 0;
    let mut v_r_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2502_ = l_Lean_isIOUnitBuiltinInitFn(v_env_2500_, v_fn_2501_);
    v_r_2503_ = leanh::lean_box((v_res_2502_) as usize);
    return v_r_2503_;
}
pub unsafe fn l_Lean_isIOUnitInitFn(
    mut v_env_2504_: *mut leanh::LeanObject,
    mut v_fn_2505_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2506_: u8 = 0;
    leanh::lean_inc(v_fn_2505_);
    leanh::lean_inc_ref(v_env_2504_);
    v___x_2506_ = l_Lean_isIOUnitBuiltinInitFn(v_env_2504_, v_fn_2505_);
    if v___x_2506_ == 0 {
        let mut v___x_2507_: u8 = 0;
        v___x_2507_ = l_Lean_isIOUnitRegularInitFn(v_env_2504_, v_fn_2505_);
        return v___x_2507_;
    } else {
        leanh::lean_dec(v_fn_2505_);
        leanh::lean_dec_ref(v_env_2504_);
        return v___x_2506_;
    }
}
pub unsafe fn l_Lean_isIOUnitInitFn___boxed(
    mut v_env_2508_: *mut leanh::LeanObject,
    mut v_fn_2509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2510_: u8 = 0;
    let mut v_r_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2510_ = l_Lean_isIOUnitInitFn(v_env_2508_, v_fn_2509_);
    v_r_2511_ = leanh::lean_box((v_res_2510_) as usize);
    return v_r_2511_;
}
pub unsafe fn l_Lean_hasInitAttr(
    mut v_env_2512_: *mut leanh::LeanObject,
    mut v_fn_2513_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2514_ = lean_get_init_fn_name_for(v_env_2512_, v_fn_2513_);
    if leanh::lean_obj_tag(v___x_2514_) == 0 {
        let mut v___x_2515_: u8 = 0;
        v___x_2515_ = 0;
        return v___x_2515_;
    } else {
        let mut v___x_2516_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_2514_, 1);
        v___x_2516_ = 1;
        return v___x_2516_;
    }
}
pub unsafe fn l_Lean_hasInitAttr___boxed(
    mut v_env_2517_: *mut leanh::LeanObject,
    mut v_fn_2518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2519_: u8 = 0;
    let mut v_r_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2519_ = l_Lean_hasInitAttr(v_env_2517_, v_fn_2518_);
    v_r_2520_ = leanh::lean_box((v_res_2519_) as usize);
    return v_r_2520_;
}
pub unsafe fn l_Lean_setBuiltinInitAttr(
    mut v_env_2521_: *mut leanh::LeanObject,
    mut v_declName_2522_: *mut leanh::LeanObject,
    mut v_initFnName_2523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2524_ = l_Lean_builtinInitAttr;
    v___x_2525_ = l_Lean_ParametricAttribute_setParam___redArg(
        v___x_2524_,
        v_env_2521_,
        v_declName_2522_,
        v_initFnName_2523_,
    );
    return v___x_2525_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0___redArg(
    mut v_kind_2526_: *mut leanh::LeanObject,
    mut v___y_2527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2547_: u8 = 0;
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2553_: u8 = 0;
    let mut v_unused_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2529_ = lean_st_ref_get(v___y_2527_);
                v_auxDeclNGen_2530_ = leanh::lean_ctor_get(v___x_2529_, 3);
                leanh::lean_inc_ref(v_auxDeclNGen_2530_);
                leanh::lean_dec(v___x_2529_);
                v___x_2531_ = lean_st_ref_get(v___y_2527_);
                v_env_2532_ = leanh::lean_ctor_get(v___x_2531_, 0);
                leanh::lean_inc_ref(v_env_2532_);
                leanh::lean_dec(v___x_2531_);
                v___x_2533_ = l_Lean_DeclNameGenerator_mkUniqueName(
                    v_env_2532_,
                    v_auxDeclNGen_2530_,
                    v_kind_2526_,
                );
                v_fst_2534_ = leanh::lean_ctor_get(v___x_2533_, 0);
                leanh::lean_inc(v_fst_2534_);
                v_snd_2535_ = leanh::lean_ctor_get(v___x_2533_, 1);
                leanh::lean_inc(v_snd_2535_);
                leanh::lean_dec_ref(v___x_2533_);
                v___x_2536_ = lean_st_ref_take(v___y_2527_);
                v_env_2537_ = leanh::lean_ctor_get(v___x_2536_, 0);
                v_nextMacroScope_2538_ = leanh::lean_ctor_get(v___x_2536_, 1);
                v_ngen_2539_ = leanh::lean_ctor_get(v___x_2536_, 2);
                v_traceState_2540_ = leanh::lean_ctor_get(v___x_2536_, 4);
                v_cache_2541_ = leanh::lean_ctor_get(v___x_2536_, 5);
                v_messages_2542_ = leanh::lean_ctor_get(v___x_2536_, 6);
                v_infoState_2543_ = leanh::lean_ctor_get(v___x_2536_, 7);
                v_snapshotTasks_2544_ = leanh::lean_ctor_get(v___x_2536_, 8);
                v_isSharedCheck_2553_ = (!leanh::lean_is_exclusive(v___x_2536_)) as u8;
                if v_isSharedCheck_2553_ == 0 {
                    v_unused_2554_ = leanh::lean_ctor_get(v___x_2536_, 3);
                    leanh::lean_dec(v_unused_2554_);
                    v___x_2546_ = v___x_2536_;
                    v_isShared_2547_ = v_isSharedCheck_2553_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2544_);
                    leanh::lean_inc(v_infoState_2543_);
                    leanh::lean_inc(v_messages_2542_);
                    leanh::lean_inc(v_cache_2541_);
                    leanh::lean_inc(v_traceState_2540_);
                    leanh::lean_inc(v_ngen_2539_);
                    leanh::lean_inc(v_nextMacroScope_2538_);
                    leanh::lean_inc(v_env_2537_);
                    leanh::lean_dec(v___x_2536_);
                    v___x_2546_ = leanh::lean_box(0);
                    v_isShared_2547_ = v_isSharedCheck_2553_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2547_ == 0 {
                    leanh::lean_ctor_set(v___x_2546_, 3, v_snd_2535_);
                    v___x_2549_ = v___x_2546_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2552_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_env_2537_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_nextMacroScope_2538_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_ngen_2539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_snd_2535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 4, v_traceState_2540_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 5, v_cache_2541_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 6, v_messages_2542_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 7, v_infoState_2543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 8, v_snapshotTasks_2544_);
                    v___x_2549_ = v_reuseFailAlloc_2552_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2550_ = lean_st_ref_set(v___y_2527_, v___x_2549_);
                v___x_2551_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2551_, 0, v_fst_2534_);
                return v___x_2551_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0___redArg___boxed(
    mut v_kind_2555_: *mut leanh::LeanObject,
    mut v___y_2556_: *mut leanh::LeanObject,
    mut v___y_2557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2558_ = l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0___redArg(
        v_kind_2555_,
        v___y_2556_,
    );
    leanh::lean_dec(v___y_2556_);
    return v_res_2558_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0(
    mut v_kind_2559_: *mut leanh::LeanObject,
    mut v___y_2560_: *mut leanh::LeanObject,
    mut v___y_2561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2563_ = l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0___redArg(
        v_kind_2559_,
        v___y_2561_,
    );
    return v___x_2563_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0___boxed(
    mut v_kind_2564_: *mut leanh::LeanObject,
    mut v___y_2565_: *mut leanh::LeanObject,
    mut v___y_2566_: *mut leanh::LeanObject,
    mut v___y_2567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0(
        v_kind_2564_,
        v___y_2565_,
        v___y_2566_,
    );
    leanh::lean_dec(v___y_2566_);
    leanh::lean_dec_ref(v___y_2565_);
    return v_res_2568_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1___redArg(
    mut v_e_2569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2574_: u8 = 0;
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_a_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2583_: u8 = 0;
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_2569_) == 0 {
                    v_a_2571_ = leanh::lean_ctor_get(v_e_2569_, 0);
                    v_isSharedCheck_2579_ = (!leanh::lean_is_exclusive(v_e_2569_)) as u8;
                    if v_isSharedCheck_2579_ == 0 {
                        v___x_2573_ = v_e_2569_;
                        v_isShared_2574_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2571_);
                        leanh::lean_dec(v_e_2569_);
                        v___x_2573_ = leanh::lean_box(0);
                        v_isShared_2574_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2580_ = leanh::lean_ctor_get(v_e_2569_, 0);
                    v_isSharedCheck_2587_ = (!leanh::lean_is_exclusive(v_e_2569_)) as u8;
                    if v_isSharedCheck_2587_ == 0 {
                        v___x_2582_ = v_e_2569_;
                        v_isShared_2583_ = v_isSharedCheck_2587_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2580_);
                        leanh::lean_dec(v_e_2569_);
                        v___x_2582_ = leanh::lean_box(0);
                        v_isShared_2583_ = v_isSharedCheck_2587_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2575_ = lean_mk_io_user_error(v_a_2571_);
                if v_isShared_2574_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2573_, 1);
                    leanh::lean_ctor_set(v___x_2573_, 0, v___x_2575_);
                    v___x_2577_ = v___x_2573_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2578_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
                    v___x_2577_ = v_reuseFailAlloc_2578_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2577_;
            }
            3 => {
                if v_isShared_2583_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2582_, 0);
                    v___x_2585_ = v___x_2582_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
                    v___x_2585_ = v_reuseFailAlloc_2586_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1___redArg___boxed(
    mut v_e_2588_: *mut leanh::LeanObject,
    mut v_a_2589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2590_ = l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1___redArg(v_e_2588_);
    return v_res_2590_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1(
    mut v_00_u03b1_2591_: *mut leanh::LeanObject,
    mut v_e_2592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2594_ = l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1___redArg(v_e_2592_);
    return v___x_2594_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1___boxed(
    mut v_00_u03b1_2595_: *mut leanh::LeanObject,
    mut v_e_2596_: *mut leanh::LeanObject,
    mut v_a_2597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2598_ = l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1(v_00_u03b1_2595_, v_e_2596_);
    return v_res_2598_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2___redArg(
    mut v_env_2599_: *mut leanh::LeanObject,
    mut v___y_2600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2620_: u8 = 0;
    let mut v_unused_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2602_ = lean_st_ref_take(v___y_2600_);
                v_nextMacroScope_2603_ = leanh::lean_ctor_get(v___x_2602_, 1);
                v_ngen_2604_ = leanh::lean_ctor_get(v___x_2602_, 2);
                v_auxDeclNGen_2605_ = leanh::lean_ctor_get(v___x_2602_, 3);
                v_traceState_2606_ = leanh::lean_ctor_get(v___x_2602_, 4);
                v_messages_2607_ = leanh::lean_ctor_get(v___x_2602_, 6);
                v_infoState_2608_ = leanh::lean_ctor_get(v___x_2602_, 7);
                v_snapshotTasks_2609_ = leanh::lean_ctor_get(v___x_2602_, 8);
                v_isSharedCheck_2620_ = (!leanh::lean_is_exclusive(v___x_2602_)) as u8;
                if v_isSharedCheck_2620_ == 0 {
                    v_unused_2621_ = leanh::lean_ctor_get(v___x_2602_, 5);
                    leanh::lean_dec(v_unused_2621_);
                    v_unused_2622_ = leanh::lean_ctor_get(v___x_2602_, 0);
                    leanh::lean_dec(v_unused_2622_);
                    v___x_2611_ = v___x_2602_;
                    v_isShared_2612_ = v_isSharedCheck_2620_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2609_);
                    leanh::lean_inc(v_infoState_2608_);
                    leanh::lean_inc(v_messages_2607_);
                    leanh::lean_inc(v_traceState_2606_);
                    leanh::lean_inc(v_auxDeclNGen_2605_);
                    leanh::lean_inc(v_ngen_2604_);
                    leanh::lean_inc(v_nextMacroScope_2603_);
                    leanh::lean_dec(v___x_2602_);
                    v___x_2611_ = leanh::lean_box(0);
                    v_isShared_2612_ = v_isSharedCheck_2620_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2613_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2);
                if v_isShared_2612_ == 0 {
                    leanh::lean_ctor_set(v___x_2611_, 5, v___x_2613_);
                    leanh::lean_ctor_set(v___x_2611_, 0, v_env_2599_);
                    v___x_2615_ = v___x_2611_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2619_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_env_2599_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_nextMacroScope_2603_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_ngen_2604_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 3, v_auxDeclNGen_2605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 4, v_traceState_2606_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 5, v___x_2613_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 6, v_messages_2607_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 7, v_infoState_2608_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 8, v_snapshotTasks_2609_);
                    v___x_2615_ = v_reuseFailAlloc_2619_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2616_ = lean_st_ref_set(v___y_2600_, v___x_2615_);
                v___x_2617_ = leanh::lean_box(0);
                v___x_2618_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2618_, 0, v___x_2617_);
                return v___x_2618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2___redArg___boxed(
    mut v_env_2623_: *mut leanh::LeanObject,
    mut v___y_2624_: *mut leanh::LeanObject,
    mut v___y_2625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2626_ =
        l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2___redArg(v_env_2623_, v___y_2624_);
    leanh::lean_dec(v___y_2624_);
    return v_res_2626_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2(
    mut v_env_2627_: *mut leanh::LeanObject,
    mut v___y_2628_: *mut leanh::LeanObject,
    mut v___y_2629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2631_ =
        l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2___redArg(v_env_2627_, v___y_2629_);
    return v___x_2631_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2___boxed(
    mut v_env_2632_: *mut leanh::LeanObject,
    mut v___y_2633_: *mut leanh::LeanObject,
    mut v___y_2634_: *mut leanh::LeanObject,
    mut v___y_2635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2636_ =
        l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2(v_env_2632_, v___y_2633_, v___y_2634_);
    leanh::lean_dec(v___y_2634_);
    leanh::lean_dec_ref(v___y_2633_);
    return v_res_2636_;
}
pub unsafe fn _init_l_Lean_declareBuiltin___lam__0___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2639_ = leanh::lean_box(0);
    v___x_2640_ = l_Lean_declareBuiltin___lam__0___closed__0;
    v___x_2641_ = l_Lean_mkConst(v___x_2640_, v___x_2639_);
    return v___x_2641_;
}
pub unsafe fn _init_l_Lean_declareBuiltin___lam__0___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2644_ = leanh::lean_box(0);
    v___x_2645_ = l_Lean_declareBuiltin___lam__0___closed__2;
    v___x_2646_ = l_Lean_mkConst(v___x_2645_, v___x_2644_);
    return v___x_2646_;
}
pub unsafe fn _init_l_Lean_declareBuiltin___lam__0___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2647_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_declareBuiltin___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_declareBuiltin___lam__0___closed__3_once),
        _init_l_Lean_declareBuiltin___lam__0___closed__3,
    );
    v___x_2648_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_declareBuiltin___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_declareBuiltin___lam__0___closed__1_once),
        _init_l_Lean_declareBuiltin___lam__0___closed__1,
    );
    v___x_2649_ = l_Lean_Expr_app___override(v___x_2648_, v___x_2647_);
    return v___x_2649_;
}
pub unsafe fn l_Lean_declareBuiltin___lam__0(
    mut v___x_2650_: *mut leanh::LeanObject,
    mut v_value_2651_: *mut leanh::LeanObject,
    mut v___y_2652_: *mut leanh::LeanObject,
    mut v___y_2653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2659_: u8 = 0;
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: u8 = 0;
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: u8 = 0;
    let mut v___x_2670_: u8 = 0;
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2685_: u8 = 0;
    let mut v_ref_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut v_unused_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2655_ = l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0___redArg(
                    v___x_2650_,
                    v___y_2653_,
                );
                v_a_2656_ = leanh::lean_ctor_get(v___x_2655_, 0);
                v_isSharedCheck_2700_ = (!leanh::lean_is_exclusive(v___x_2655_)) as u8;
                if v_isSharedCheck_2700_ == 0 {
                    v___x_2658_ = v___x_2655_;
                    v_isShared_2659_ = v_isSharedCheck_2700_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2656_);
                    leanh::lean_dec(v___x_2655_);
                    v___x_2658_ = leanh::lean_box(0);
                    v_isShared_2659_ = v_isSharedCheck_2700_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2660_ = leanh::lean_box(0);
                v___x_2661_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_declareBuiltin___lam__0___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_declareBuiltin___lam__0___closed__4_once),
                    _init_l_Lean_declareBuiltin___lam__0___closed__4,
                );
                leanh::lean_inc_n(v_a_2656_, 2);
                v___x_2662_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2662_, 0, v_a_2656_);
                leanh::lean_ctor_set(v___x_2662_, 1, v___x_2660_);
                leanh::lean_ctor_set(v___x_2662_, 2, v___x_2661_);
                v___x_2663_ = leanh::lean_box(0);
                v___x_2664_ = 1;
                v___x_2665_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2665_, 0, v_a_2656_);
                leanh::lean_ctor_set(v___x_2665_, 1, v___x_2660_);
                v___x_2666_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_2666_, 0, v___x_2662_);
                leanh::lean_ctor_set(v___x_2666_, 1, v_value_2651_);
                leanh::lean_ctor_set(v___x_2666_, 2, v___x_2663_);
                leanh::lean_ctor_set(v___x_2666_, 3, v___x_2665_);
                leanh::lean_ctor_set_uint8(
                    v___x_2666_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_2664_,
                );
                if v_isShared_2659_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2658_, 1);
                    leanh::lean_ctor_set(v___x_2658_, 0, v___x_2666_);
                    v___x_2668_ = v___x_2658_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2699_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2666_);
                    v___x_2668_ = v_reuseFailAlloc_2699_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2669_ = 1;
                v___x_2670_ = 0;
                v___x_2671_ = l_Lean_addAndCompile(
                    v___x_2668_,
                    v___x_2669_,
                    v___x_2670_,
                    v___y_2652_,
                    v___y_2653_,
                );
                if leanh::lean_obj_tag(v___x_2671_) == 0 {
                    v_isSharedCheck_2697_ = (!leanh::lean_is_exclusive(v___x_2671_)) as u8;
                    if v_isSharedCheck_2697_ == 0 {
                        v_unused_2698_ = leanh::lean_ctor_get(v___x_2671_, 0);
                        leanh::lean_dec(v_unused_2698_);
                        v___x_2673_ = v___x_2671_;
                        v_isShared_2674_ = v_isSharedCheck_2697_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2671_);
                        v___x_2673_ = leanh::lean_box(0);
                        v_isShared_2674_ = v_isSharedCheck_2697_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2656_);
                    return v___x_2671_;
                }
            }
            3 => {
                v___x_2675_ = lean_st_ref_get(v___y_2653_);
                v_env_2676_ = leanh::lean_ctor_get(v___x_2675_, 0);
                leanh::lean_inc_ref(v_env_2676_);
                leanh::lean_dec(v___x_2675_);
                v___x_2677_ = leanh::lean_box(0);
                v___x_2678_ = l_Lean_setBuiltinInitAttr(v_env_2676_, v_a_2656_, v___x_2677_);
                v___x_2679_ =
                    l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1___redArg(v___x_2678_);
                if leanh::lean_obj_tag(v___x_2679_) == 0 {
                    leanh::lean_del_object(v___x_2673_);
                    v_a_2680_ = leanh::lean_ctor_get(v___x_2679_, 0);
                    leanh::lean_inc(v_a_2680_);
                    leanh::lean_dec_ref_known(v___x_2679_, 1);
                    v___x_2681_ = l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2___redArg(
                        v_a_2680_,
                        v___y_2653_,
                    );
                    return v___x_2681_;
                } else {
                    v_a_2682_ = leanh::lean_ctor_get(v___x_2679_, 0);
                    v_isSharedCheck_2696_ = (!leanh::lean_is_exclusive(v___x_2679_)) as u8;
                    if v_isSharedCheck_2696_ == 0 {
                        v___x_2684_ = v___x_2679_;
                        v_isShared_2685_ = v_isSharedCheck_2696_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2682_);
                        leanh::lean_dec(v___x_2679_);
                        v___x_2684_ = leanh::lean_box(0);
                        v_isShared_2685_ = v_isSharedCheck_2696_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v_ref_2686_ = leanh::lean_ctor_get(v___y_2652_, 5);
                v___x_2687_ = lean_io_error_to_string(v_a_2682_);
                if v_isShared_2674_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2673_, 3);
                    leanh::lean_ctor_set(v___x_2673_, 0, v___x_2687_);
                    v___x_2689_ = v___x_2673_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2695_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2687_);
                    v___x_2689_ = v_reuseFailAlloc_2695_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2690_ = l_Lean_MessageData_ofFormat(v___x_2689_);
                leanh::lean_inc(v_ref_2686_);
                v___x_2691_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2691_, 0, v_ref_2686_);
                leanh::lean_ctor_set(v___x_2691_, 1, v___x_2690_);
                if v_isShared_2685_ == 0 {
                    leanh::lean_ctor_set(v___x_2684_, 0, v___x_2691_);
                    v___x_2693_ = v___x_2684_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2694_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
                    v___x_2693_ = v_reuseFailAlloc_2694_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_declareBuiltin___lam__0___boxed(
    mut v___x_2701_: *mut leanh::LeanObject,
    mut v_value_2702_: *mut leanh::LeanObject,
    mut v___y_2703_: *mut leanh::LeanObject,
    mut v___y_2704_: *mut leanh::LeanObject,
    mut v___y_2705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2706_ =
        l_Lean_declareBuiltin___lam__0(v___x_2701_, v_value_2702_, v___y_2703_, v___y_2704_);
    leanh::lean_dec(v___y_2704_);
    leanh::lean_dec_ref(v___y_2703_);
    return v_res_2706_;
}
pub unsafe fn l_Lean_declareBuiltin(
    mut v_forDecl_2710_: *mut leanh::LeanObject,
    mut v_value_2711_: *mut leanh::LeanObject,
    mut v_a_2712_: *mut leanh::LeanObject,
    mut v_a_2713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: u8 = 0;
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2715_ = l_Lean_declareBuiltin___closed__1;
    v___x_2716_ = l_Lean_Name_append(v___x_2715_, v_forDecl_2710_);
    v___f_2717_ = leanh::lean_alloc_closure(
        l_Lean_declareBuiltin___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2717_, 0, v___x_2716_);
    leanh::lean_closure_set(v___f_2717_, 1, v_value_2711_);
    v___x_2718_ = 1;
    v___x_2719_ = l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2___redArg(
        v___f_2717_,
        v___x_2718_,
        v_a_2712_,
        v_a_2713_,
    );
    return v___x_2719_;
}
pub unsafe fn l_Lean_declareBuiltin___boxed(
    mut v_forDecl_2720_: *mut leanh::LeanObject,
    mut v_value_2721_: *mut leanh::LeanObject,
    mut v_a_2722_: *mut leanh::LeanObject,
    mut v_a_2723_: *mut leanh::LeanObject,
    mut v_a_2724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2725_ = l_Lean_declareBuiltin(v_forDecl_2720_, v_value_2721_, v_a_2722_, v_a_2723_);
    leanh::lean_dec(v_a_2723_);
    leanh::lean_dec_ref(v_a_2722_);
    return v_res_2725_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__3(
    mut v_opts_2726_: *mut leanh::LeanObject,
    mut v_opt_2727_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2728_ = leanh::lean_ctor_get(v_opt_2727_, 0);
    v_defValue_2729_ = leanh::lean_ctor_get(v_opt_2727_, 1);
    v_map_2730_ = leanh::lean_ctor_get(v_opts_2726_, 0);
    v___x_2731_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2730_,
            v_name_2728_,
        );
    if leanh::lean_obj_tag(v___x_2731_) == 0 {
        let mut v___x_2732_: u8 = 0;
        v___x_2732_ = (leanh::lean_unbox(v_defValue_2729_) as u8);
        return v___x_2732_;
    } else {
        let mut v_val_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2733_ = leanh::lean_ctor_get(v___x_2731_, 0);
        leanh::lean_inc(v_val_2733_);
        leanh::lean_dec_ref_known(v___x_2731_, 1);
        if leanh::lean_obj_tag(v_val_2733_) == 1 {
            let mut v_v_2734_: u8 = 0;
            v_v_2734_ = leanh::lean_ctor_get_uint8(v_val_2733_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2733_, 0);
            return v_v_2734_;
        } else {
            let mut v___x_2735_: u8 = 0;
            leanh::lean_dec(v_val_2733_);
            v___x_2735_ = (leanh::lean_unbox(v_defValue_2729_) as u8);
            return v___x_2735_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__3___boxed(
    mut v_opts_2736_: *mut leanh::LeanObject,
    mut v_opt_2737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2738_: u8 = 0;
    let mut v_r_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2738_ =
        l_Lean_Option_get___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__3(
            v_opts_2736_,
            v_opt_2737_,
        );
    leanh::lean_dec_ref(v_opt_2737_);
    leanh::lean_dec_ref(v_opts_2736_);
    v_r_2739_ = leanh::lean_box((v_res_2738_) as usize);
    return v_r_2739_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0_spec__0(
    mut v_a_2740_: *mut leanh::LeanObject,
    mut v_as_2741_: *mut leanh::LeanObject,
    mut v_i_2742_: usize,
    mut v_stop_2743_: usize,
) -> u8 {
    let mut v___x_2744_: u8 = 0;
    let mut v_fst_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: u8 = 0;
    let mut v___y_2752_: u8 = 0;
    let mut v___x_2753_: usize = 0;
    let mut v___x_2754_: usize = 0;
    let mut v___x_2756_: u8 = 0;
    let mut v___x_2757_: u8 = 0;
    let mut v___x_2758_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2744_ = lean_usize_dec_eq(v_i_2742_, v_stop_2743_);
                if v___x_2744_ == 0 {
                    v_fst_2745_ = leanh::lean_ctor_get(v_a_2740_, 0);
                    v_snd_2746_ = leanh::lean_ctor_get(v_a_2740_, 1);
                    v___x_2747_ = lean_array_uget_borrowed(v_as_2741_, v_i_2742_);
                    v_fst_2748_ = leanh::lean_ctor_get(v___x_2747_, 0);
                    v_snd_2749_ = leanh::lean_ctor_get(v___x_2747_, 1);
                    v___x_2750_ = 1;
                    v___x_2756_ = lean_name_eq(v_fst_2745_, v_fst_2748_);
                    if v___x_2756_ == 0 {
                        v___y_2752_ = v___x_2756_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2757_ = lean_name_eq(v_snd_2746_, v_snd_2749_);
                        v___y_2752_ = v___x_2757_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2758_ = 0;
                    return v___x_2758_;
                }
            }
            1 => {
                if v___y_2752_ == 0 {
                    v___x_2753_ = 1usize;
                    v___x_2754_ = lean_usize_add(v_i_2742_, v___x_2753_);
                    v_i_2742_ = v___x_2754_;
                    state = 0;
                    continue;
                } else {
                    return v___x_2750_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0_spec__0___boxed(
    mut v_a_2759_: *mut leanh::LeanObject,
    mut v_as_2760_: *mut leanh::LeanObject,
    mut v_i_2761_: *mut leanh::LeanObject,
    mut v_stop_2762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2763_: usize = 0;
    let mut v_stop_boxed_2764_: usize = 0;
    let mut v_res_2765_: u8 = 0;
    let mut v_r_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2763_ = leanh::lean_unbox_usize(v_i_2761_);
    leanh::lean_dec(v_i_2761_);
    v_stop_boxed_2764_ = leanh::lean_unbox_usize(v_stop_2762_);
    leanh::lean_dec(v_stop_2762_);
    v_res_2765_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0_spec__0(v_a_2759_, v_as_2760_, v_i_boxed_2763_, v_stop_boxed_2764_);
    leanh::lean_dec_ref(v_as_2760_);
    leanh::lean_dec_ref(v_a_2759_);
    v_r_2766_ = leanh::lean_box((v_res_2765_) as usize);
    return v_r_2766_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0(
    mut v_as_2767_: *mut leanh::LeanObject,
    mut v_a_2768_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u8 = 0;
    v___x_2769_ = leanh::lean_unsigned_to_nat(0);
    v___x_2770_ = lean_array_get_size(v_as_2767_);
    v___x_2771_ = lean_nat_dec_lt(v___x_2769_, v___x_2770_);
    if v___x_2771_ == 0 {
        return v___x_2771_;
    } else {
        if v___x_2771_ == 0 {
            return v___x_2771_;
        } else {
            let mut v___x_2772_: usize = 0;
            let mut v___x_2773_: usize = 0;
            let mut v___x_2774_: u8 = 0;
            v___x_2772_ = 0usize;
            v___x_2773_ = lean_usize_of_nat(v___x_2770_);
            v___x_2774_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0_spec__0(v_a_2768_, v_as_2767_, v___x_2772_, v___x_2773_);
            return v___x_2774_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0___boxed(
    mut v_as_2775_: *mut leanh::LeanObject,
    mut v_a_2776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2777_: u8 = 0;
    let mut v_r_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2777_ =
        l_Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0(
            v_as_2775_, v_a_2776_,
        );
    leanh::lean_dec_ref(v_a_2776_);
    leanh::lean_dec_ref(v_as_2775_);
    v_r_2778_ = leanh::lean_box((v_res_2777_) as usize);
    return v_r_2778_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__2(
    mut v___x_2779_: *mut leanh::LeanObject,
    mut v_as_2780_: *mut leanh::LeanObject,
    mut v_i_2781_: usize,
    mut v_stop_2782_: usize,
    mut v_b_2783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: usize = 0;
    let mut v___x_2787_: usize = 0;
    let mut v___x_2789_: u8 = 0;
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: u8 = 0;
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2789_ = lean_usize_dec_eq(v_i_2781_, v_stop_2782_);
                if v___x_2789_ == 0 {
                    v___x_2790_ = lean_array_uget_borrowed(v_as_2780_, v_i_2781_);
                    v___x_2791_ = l_Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0(v___x_2779_, v___x_2790_);
                    if v___x_2791_ == 0 {
                        leanh::lean_inc(v___x_2790_);
                        v___x_2792_ = lean_array_push(v_b_2783_, v___x_2790_);
                        v___y_2785_ = v___x_2792_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2785_ = v_b_2783_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2783_;
                }
            }
            1 => {
                v___x_2786_ = 1usize;
                v___x_2787_ = lean_usize_add(v_i_2781_, v___x_2786_);
                v_i_2781_ = v___x_2787_;
                v_b_2783_ = v___y_2785_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__2___boxed(
    mut v___x_2793_: *mut leanh::LeanObject,
    mut v_as_2794_: *mut leanh::LeanObject,
    mut v_i_2795_: *mut leanh::LeanObject,
    mut v_stop_2796_: *mut leanh::LeanObject,
    mut v_b_2797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2798_: usize = 0;
    let mut v_stop_boxed_2799_: usize = 0;
    let mut v_res_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2798_ = leanh::lean_unbox_usize(v_i_2795_);
    leanh::lean_dec(v_i_2795_);
    v_stop_boxed_2799_ = leanh::lean_unbox_usize(v_stop_2796_);
    leanh::lean_dec(v_stop_2796_);
    v_res_2800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__2(v___x_2793_, v_as_2794_, v_i_boxed_2798_, v_stop_boxed_2799_, v_b_2797_);
    leanh::lean_dec_ref(v_as_2794_);
    leanh::lean_dec_ref(v___x_2793_);
    return v_res_2800_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__1(
    mut v_env_2801_: *mut leanh::LeanObject,
    mut v_opts_2802_: *mut leanh::LeanObject,
    mut v___y_2803_: u8,
    mut v___x_2804_: u8,
    mut v_as_2805_: *mut leanh::LeanObject,
    mut v_sz_2806_: usize,
    mut v_i_2807_: usize,
    mut v_b_2808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: usize = 0;
    let mut v___x_2813_: usize = 0;
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: u8 = 0;
    let mut v___x_2823_: u8 = 0;
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2832_: u8 = 0;
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut v___x_2838_: u8 = 0;
    let mut v___x_2839_: u8 = 0;
    let mut v___x_2840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2815_ = lean_usize_dec_lt(v_i_2807_, v_sz_2806_);
                if v___x_2815_ == 0 {
                    leanh::lean_dec_ref(v_env_2801_);
                    v___x_2816_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2816_, 0, v_b_2808_);
                    return v___x_2816_;
                } else {
                    v_a_2817_ = lean_array_uget_borrowed(v_as_2805_, v_i_2807_);
                    v_fst_2818_ = leanh::lean_ctor_get(v_a_2817_, 0);
                    v_snd_2819_ = leanh::lean_ctor_get(v_a_2817_, 1);
                    v___x_2820_ = leanh::lean_box(0);
                    if v___y_2803_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        if v___x_2804_ == 0 {
                            v___y_2822_ = v___x_2804_;
                            state = 2;
                            continue;
                        } else {
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2812_ = 1usize;
                v___x_2813_ = lean_usize_add(v_i_2807_, v___x_2812_);
                v_i_2807_ = v___x_2813_;
                v_b_2808_ = v_a_2811_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2823_ = l_Lean_Name_isAnonymous(v_snd_2819_);
                if v___x_2823_ == 0 {
                    v___x_2824_ =
                        lean_run_init(v_env_2801_, v_opts_2802_, v_fst_2818_, v_snd_2819_);
                    if leanh::lean_obj_tag(v___x_2824_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2824_, 1);
                        v_a_2811_ = v___x_2820_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_env_2801_);
                        return v___x_2824_;
                    }
                } else {
                    v___x_2825_ = l_Lean_Environment_evalConst___redArg(
                        v_env_2801_,
                        v_opts_2802_,
                        v_fst_2818_,
                        v___y_2822_,
                    );
                    v___x_2826_ =
                        l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1___redArg(v___x_2825_);
                    if leanh::lean_obj_tag(v___x_2826_) == 0 {
                        v_a_2827_ = leanh::lean_ctor_get(v___x_2826_, 0);
                        leanh::lean_inc(v_a_2827_);
                        leanh::lean_dec_ref_known(v___x_2826_, 1);
                        v___x_2828_ =
                            leanh::lean_apply_1(v_a_2827_, leanh::lean_box(0));
                        if leanh::lean_obj_tag(v___x_2828_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2828_, 1);
                            v_a_2811_ = v___x_2820_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_env_2801_);
                            return v___x_2828_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_env_2801_);
                        v_a_2829_ = leanh::lean_ctor_get(v___x_2826_, 0);
                        v_isSharedCheck_2836_ =
                            (!leanh::lean_is_exclusive(v___x_2826_)) as u8;
                        if v_isSharedCheck_2836_ == 0 {
                            v___x_2831_ = v___x_2826_;
                            v_isShared_2832_ = v_isSharedCheck_2836_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2829_);
                            leanh::lean_dec(v___x_2826_);
                            v___x_2831_ = leanh::lean_box(0);
                            v_isShared_2832_ = v_isSharedCheck_2836_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_2832_ == 0 {
                    v___x_2834_ = v___x_2831_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
                    v___x_2834_ = v_reuseFailAlloc_2835_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2834_;
            }
            5 => {
                leanh::lean_inc(v_fst_2818_);
                leanh::lean_inc_ref(v_env_2801_);
                v___x_2838_ = l_Lean_getIRPhases(v_env_2801_, v_fst_2818_);
                v___x_2839_ = 0;
                v___x_2840_ = l_Lean_instBEqIRPhases_beq(v___x_2838_, v___x_2839_);
                if v___x_2840_ == 0 {
                    v___y_2822_ = v___x_2840_;
                    state = 2;
                    continue;
                } else {
                    v_a_2811_ = v___x_2820_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__1___boxed(
    mut v_env_2841_: *mut leanh::LeanObject,
    mut v_opts_2842_: *mut leanh::LeanObject,
    mut v___y_2843_: *mut leanh::LeanObject,
    mut v___x_2844_: *mut leanh::LeanObject,
    mut v_as_2845_: *mut leanh::LeanObject,
    mut v_sz_2846_: *mut leanh::LeanObject,
    mut v_i_2847_: *mut leanh::LeanObject,
    mut v_b_2848_: *mut leanh::LeanObject,
    mut v___y_2849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6088__boxed_2850_: u8 = 0;
    let mut v___x_6089__boxed_2851_: u8 = 0;
    let mut v_sz_boxed_2852_: usize = 0;
    let mut v_i_boxed_2853_: usize = 0;
    let mut v_res_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_6088__boxed_2850_ = (leanh::lean_unbox(v___y_2843_) as u8);
    v___x_6089__boxed_2851_ = (leanh::lean_unbox(v___x_2844_) as u8);
    v_sz_boxed_2852_ = leanh::lean_unbox_usize(v_sz_2846_);
    leanh::lean_dec(v_sz_2846_);
    v_i_boxed_2853_ = leanh::lean_unbox_usize(v_i_2847_);
    leanh::lean_dec(v_i_2847_);
    v_res_2854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__1(v_env_2841_, v_opts_2842_, v___y_6088__boxed_2850_, v___x_6089__boxed_2851_, v_as_2845_, v_sz_boxed_2852_, v_i_boxed_2853_, v_b_2848_);
    leanh::lean_dec_ref(v_as_2845_);
    leanh::lean_dec_ref(v_opts_2842_);
    return v_res_2854_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4(
    mut v_env_2860_: *mut leanh::LeanObject,
    mut v_opts_2861_: *mut leanh::LeanObject,
    mut v___x_2862_: *mut leanh::LeanObject,
    mut v_a_2863_: u8,
    mut v_as_2864_: *mut leanh::LeanObject,
    mut v_sz_2865_: usize,
    mut v_i_2866_: usize,
    mut v_b_2867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: usize = 0;
    let mut v___x_2872_: usize = 0;
    let mut v___x_2874_: u8 = 0;
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2880_: u8 = 0;
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2888_: u8 = 0;
    let mut v___y_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2890_: u8 = 0;
    let mut v___y_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2894_: usize = 0;
    let mut v___x_2895_: usize = 0;
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2900_: u8 = 0;
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2904_: u8 = 0;
    let mut v___y_2906_: u8 = 0;
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: u8 = 0;
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: u8 = 0;
    let mut v___x_2925_: usize = 0;
    let mut v___x_2926_: usize = 0;
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: usize = 0;
    let mut v___x_2929_: usize = 0;
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2932_: u8 = 0;
    let mut v___y_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2934_: u8 = 0;
    let mut v_toImport_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: u8 = 0;
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: u8 = 0;
    let mut v_a_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2945_: u8 = 0;
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2949_: u8 = 0;
    let mut v___y_2951_: u8 = 0;
    let mut v_isModule_2952_: u8 = 0;
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: u8 = 0;
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: u8 = 0;
    let mut v_a_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2964_: u8 = 0;
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_toImport_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: u8 = 0;
    let mut v_a_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2983_: u8 = 0;
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: u8 = 0;
    let mut v_irPhases_2986_: u8 = 0;
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: u8 = 0;
    let mut v_reuseFailAlloc_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2874_ = lean_usize_dec_lt(v_i_2866_, v_sz_2865_);
                if v___x_2874_ == 0 {
                    leanh::lean_dec_ref(v_env_2860_);
                    v___x_2875_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2875_, 0, v_b_2867_);
                    return v___x_2875_;
                } else {
                    if leanh::lean_obj_tag(v_b_2867_) == 0 {
                        leanh::lean_dec_ref(v_env_2860_);
                        v___x_2876_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2876_, 0, v_b_2867_);
                        return v___x_2876_;
                    } else {
                        v_val_2877_ = leanh::lean_ctor_get(v_b_2867_, 0);
                        v_isSharedCheck_2990_ = (!leanh::lean_is_exclusive(v_b_2867_)) as u8;
                        if v_isSharedCheck_2990_ == 0 {
                            v___x_2879_ = v_b_2867_;
                            v_isShared_2880_ = v_isSharedCheck_2990_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2877_);
                            leanh::lean_dec(v_b_2867_);
                            v___x_2879_ = leanh::lean_box(0);
                            v_isShared_2880_ = v_isSharedCheck_2990_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2871_ = 1usize;
                v___x_2872_ = lean_usize_add(v_i_2866_, v___x_2871_);
                v_i_2866_ = v___x_2872_;
                v_b_2867_ = v_a_2870_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2881_ = leanh::lean_unsigned_to_nat(0);
                v_a_2882_ = lean_array_uget_borrowed(v_as_2864_, v_i_2866_);
                v___x_2883_ = leanh::lean_unsigned_to_nat(1);
                v___x_2884_ = lean_nat_add(v_val_2877_, v___x_2883_);
                if v_isShared_2880_ == 0 {
                    leanh::lean_ctor_set(v___x_2879_, 0, v___x_2884_);
                    v___x_2886_ = v___x_2879_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2989_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2884_);
                    v___x_2886_ = v_reuseFailAlloc_2989_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2984_ = l_Lean_Elab_inServer;
                v___x_2985_ = l_Lean_Option_get___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__3(v_opts_2861_, v___x_2984_);
                if v___x_2985_ == 0 {
                    v_irPhases_2986_ = leanh::lean_ctor_get_uint8(
                        v_a_2882_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_2987_ = 0;
                    v___x_2988_ = l_Lean_instBEqIRPhases_beq(v_irPhases_2986_, v___x_2987_);
                    if v___x_2988_ == 0 {
                        v___y_2951_ = v_a_2863_;
                        state = 11;
                        continue;
                    } else {
                        v___y_2951_ = v___x_2985_;
                        state = 11;
                        continue;
                    }
                } else {
                    v___y_2951_ = v___x_2985_;
                    state = 11;
                    continue;
                }
            }
            4 => {
                v___x_2892_ = l_Array_append___redArg(v___y_2889_, v___y_2891_);
                leanh::lean_dec_ref(v___y_2891_);
                v___x_2893_ = leanh::lean_box(0);
                v_sz_2894_ = lean_array_size(v___x_2892_);
                v___x_2895_ = 0usize;
                leanh::lean_inc_ref(v_env_2860_);
                v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__1(v_env_2860_, v_opts_2861_, v___y_2888_, v___y_2890_, v___x_2892_, v_sz_2894_, v___x_2895_, v___x_2893_);
                leanh::lean_dec_ref(v___x_2892_);
                if leanh::lean_obj_tag(v___x_2896_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2896_, 1);
                    v_a_2870_ = v___x_2886_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___x_2886_);
                    leanh::lean_dec_ref(v_env_2860_);
                    v_a_2897_ = leanh::lean_ctor_get(v___x_2896_, 0);
                    v_isSharedCheck_2904_ = (!leanh::lean_is_exclusive(v___x_2896_)) as u8;
                    if v_isSharedCheck_2904_ == 0 {
                        v___x_2899_ = v___x_2896_;
                        v_isShared_2900_ = v_isSharedCheck_2904_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2897_);
                        leanh::lean_dec(v___x_2896_);
                        v___x_2899_ = leanh::lean_box(0);
                        v_isShared_2900_ = v_isSharedCheck_2904_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_2900_ == 0 {
                    v___x_2902_ = v___x_2899_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2903_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
                    v___x_2902_ = v_reuseFailAlloc_2903_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2902_;
            }
            7 => {
                v___x_2907_ = l_Lean_interpretedModInits;
                v___x_2908_ = lean_st_ref_get(v___x_2907_);
                v_toImport_2909_ = leanh::lean_ctor_get(v_a_2882_, 0);
                v_module_2910_ = leanh::lean_ctor_get(v_toImport_2909_, 0);
                v___x_2911_ = l_Lean_NameSet_contains(v___x_2908_, v_module_2910_);
                leanh::lean_dec(v___x_2908_);
                if v___x_2911_ == 0 {
                    v___x_2912_ = lean_st_ref_take(v___x_2907_);
                    leanh::lean_inc(v_module_2910_);
                    v___x_2913_ = l_Lean_NameSet_insert(v___x_2912_, v_module_2910_);
                    v___x_2914_ = lean_st_ref_set(v___x_2907_, v___x_2913_);
                    v___x_2915_ = l_Lean_regularInitAttr;
                    v_ext_2916_ = leanh::lean_ctor_get(v___x_2915_, 1);
                    v___x_2917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__0;
                    v___x_2918_ = 0;
                    v___x_2919_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                        v___x_2917_,
                        v_ext_2916_,
                        v_env_2860_,
                        v_val_2877_,
                        v___x_2918_,
                    );
                    v___x_2920_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_2917_, v_ext_2916_, v_env_2860_, v_val_2877_);
                    leanh::lean_dec(v_val_2877_);
                    v___x_2921_ = lean_array_get_size(v___x_2920_);
                    v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__1;
                    v___x_2923_ = lean_nat_dec_lt(v___x_2881_, v___x_2921_);
                    if v___x_2923_ == 0 {
                        leanh::lean_dec_ref(v___x_2920_);
                        v___y_2888_ = v___y_2906_;
                        v___y_2889_ = v___x_2919_;
                        v___y_2890_ = v___x_2911_;
                        v___y_2891_ = v___x_2922_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2924_ = lean_nat_dec_le(v___x_2921_, v___x_2921_);
                        if v___x_2924_ == 0 {
                            if v___x_2923_ == 0 {
                                leanh::lean_dec_ref(v___x_2920_);
                                v___y_2888_ = v___y_2906_;
                                v___y_2889_ = v___x_2919_;
                                v___y_2890_ = v___x_2911_;
                                v___y_2891_ = v___x_2922_;
                                state = 4;
                                continue;
                            } else {
                                v___x_2925_ = 0usize;
                                v___x_2926_ = lean_usize_of_nat(v___x_2921_);
                                v___x_2927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__2(v___x_2919_, v___x_2920_, v___x_2925_, v___x_2926_, v___x_2922_);
                                leanh::lean_dec_ref(v___x_2920_);
                                v___y_2888_ = v___y_2906_;
                                v___y_2889_ = v___x_2919_;
                                v___y_2890_ = v___x_2911_;
                                v___y_2891_ = v___x_2927_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v___x_2928_ = 0usize;
                            v___x_2929_ = lean_usize_of_nat(v___x_2921_);
                            v___x_2930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__2(v___x_2919_, v___x_2920_, v___x_2928_, v___x_2929_, v___x_2922_);
                            leanh::lean_dec_ref(v___x_2920_);
                            v___y_2888_ = v___y_2906_;
                            v___y_2889_ = v___x_2919_;
                            v___y_2890_ = v___x_2911_;
                            v___y_2891_ = v___x_2930_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_val_2877_);
                    v_a_2870_ = v___x_2886_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                v_toImport_2935_ = leanh::lean_ctor_get(v_a_2882_, 0);
                v_module_2936_ = leanh::lean_ctor_get(v_toImport_2935_, 0);
                v___x_2937_ = 1;
                leanh::lean_inc(v_module_2936_);
                v___x_2938_ = l_Lean_mkModuleInitializationFunctionName(
                    v_module_2936_,
                    v___y_2933_,
                    v___x_2937_,
                );
                leanh::lean_dec(v___y_2933_);
                v___x_2939_ = lean_run_mod_init_core(v___x_2938_);
                leanh::lean_dec_ref(v___x_2938_);
                if leanh::lean_obj_tag(v___x_2939_) == 0 {
                    if v_a_2934_ == 0 {
                        v_a_2940_ = leanh::lean_ctor_get(v___x_2939_, 0);
                        leanh::lean_inc(v_a_2940_);
                        leanh::lean_dec_ref_known(v___x_2939_, 1);
                        v___x_2941_ = (leanh::lean_unbox(v_a_2940_) as u8);
                        leanh::lean_dec(v_a_2940_);
                        if v___x_2941_ == 0 {
                            v___y_2906_ = v___y_2932_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_dec(v_val_2877_);
                            v_a_2870_ = v___x_2886_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_2939_, 1);
                        leanh::lean_dec(v_val_2877_);
                        v_a_2870_ = v___x_2886_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2886_);
                    leanh::lean_dec(v_val_2877_);
                    leanh::lean_dec_ref(v_env_2860_);
                    v_a_2942_ = leanh::lean_ctor_get(v___x_2939_, 0);
                    v_isSharedCheck_2949_ = (!leanh::lean_is_exclusive(v___x_2939_)) as u8;
                    if v_isSharedCheck_2949_ == 0 {
                        v___x_2944_ = v___x_2939_;
                        v_isShared_2945_ = v_isSharedCheck_2949_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2942_);
                        leanh::lean_dec(v___x_2939_);
                        v___x_2944_ = leanh::lean_box(0);
                        v_isShared_2945_ = v_isSharedCheck_2949_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2945_ == 0 {
                    v___x_2947_ = v___x_2944_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2948_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
                    v___x_2947_ = v_reuseFailAlloc_2948_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2947_;
            }
            11 => {
                v_isModule_2952_ = leanh::lean_ctor_get_uint8(
                    v___x_2862_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                );
                v___x_2953_ =
                    l_Lean_Environment_getModulePackageByIdx_x3f(v_env_2860_, v_val_2877_);
                if v_isModule_2952_ == 0 {
                    v_toImport_2954_ = leanh::lean_ctor_get(v_a_2882_, 0);
                    v_module_2955_ = leanh::lean_ctor_get(v_toImport_2954_, 0);
                    v___x_2956_ = 2;
                    leanh::lean_inc(v_module_2955_);
                    v___x_2957_ = l_Lean_mkModuleInitializationFunctionName(
                        v_module_2955_,
                        v___x_2953_,
                        v___x_2956_,
                    );
                    leanh::lean_dec(v___x_2953_);
                    v___x_2958_ = lean_run_mod_init_core(v___x_2957_);
                    leanh::lean_dec_ref(v___x_2957_);
                    if leanh::lean_obj_tag(v___x_2958_) == 0 {
                        v_a_2959_ = leanh::lean_ctor_get(v___x_2958_, 0);
                        leanh::lean_inc(v_a_2959_);
                        leanh::lean_dec_ref_known(v___x_2958_, 1);
                        v___x_2960_ = (leanh::lean_unbox(v_a_2959_) as u8);
                        leanh::lean_dec(v_a_2959_);
                        if v___x_2960_ == 0 {
                            v___y_2906_ = v___y_2951_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_dec(v_val_2877_);
                            v_a_2870_ = v___x_2886_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2886_);
                        leanh::lean_dec(v_val_2877_);
                        leanh::lean_dec_ref(v_env_2860_);
                        v_a_2961_ = leanh::lean_ctor_get(v___x_2958_, 0);
                        v_isSharedCheck_2968_ =
                            (!leanh::lean_is_exclusive(v___x_2958_)) as u8;
                        if v_isSharedCheck_2968_ == 0 {
                            v___x_2963_ = v___x_2958_;
                            v_isShared_2964_ = v_isSharedCheck_2968_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2961_);
                            leanh::lean_dec(v___x_2958_);
                            v___x_2963_ = leanh::lean_box(0);
                            v_isShared_2964_ = v_isSharedCheck_2968_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    if v___y_2951_ == 0 {
                        v___y_2932_ = v___y_2951_;
                        v___y_2933_ = v___x_2953_;
                        v_a_2934_ = v___y_2951_;
                        state = 8;
                        continue;
                    } else {
                        v_toImport_2969_ = leanh::lean_ctor_get(v_a_2882_, 0);
                        v_module_2970_ = leanh::lean_ctor_get(v_toImport_2969_, 0);
                        v___x_2971_ = 0;
                        leanh::lean_inc(v_module_2970_);
                        v___x_2972_ = l_Lean_mkModuleInitializationFunctionName(
                            v_module_2970_,
                            v___x_2953_,
                            v___x_2971_,
                        );
                        v___x_2973_ = lean_run_mod_init_core(v___x_2972_);
                        leanh::lean_dec_ref(v___x_2972_);
                        if leanh::lean_obj_tag(v___x_2973_) == 0 {
                            v_a_2974_ = leanh::lean_ctor_get(v___x_2973_, 0);
                            leanh::lean_inc(v_a_2974_);
                            leanh::lean_dec_ref_known(v___x_2973_, 1);
                            v___x_2975_ = (leanh::lean_unbox(v_a_2974_) as u8);
                            leanh::lean_dec(v_a_2974_);
                            v___y_2932_ = v___y_2951_;
                            v___y_2933_ = v___x_2953_;
                            v_a_2934_ = v___x_2975_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2953_);
                            leanh::lean_dec_ref(v___x_2886_);
                            leanh::lean_dec(v_val_2877_);
                            leanh::lean_dec_ref(v_env_2860_);
                            v_a_2976_ = leanh::lean_ctor_get(v___x_2973_, 0);
                            v_isSharedCheck_2983_ =
                                (!leanh::lean_is_exclusive(v___x_2973_)) as u8;
                            if v_isSharedCheck_2983_ == 0 {
                                v___x_2978_ = v___x_2973_;
                                v_isShared_2979_ = v_isSharedCheck_2983_;
                                state = 14;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2976_);
                                leanh::lean_dec(v___x_2973_);
                                v___x_2978_ = leanh::lean_box(0);
                                v_isShared_2979_ = v_isSharedCheck_2983_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                }
            }
            12 => {
                if v_isShared_2964_ == 0 {
                    v___x_2966_ = v___x_2963_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2967_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
                    v___x_2966_ = v_reuseFailAlloc_2967_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2966_;
            }
            14 => {
                if v_isShared_2979_ == 0 {
                    v___x_2981_ = v___x_2978_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2982_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
                    v___x_2981_ = v_reuseFailAlloc_2982_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___boxed(
    mut v_env_2991_: *mut leanh::LeanObject,
    mut v_opts_2992_: *mut leanh::LeanObject,
    mut v___x_2993_: *mut leanh::LeanObject,
    mut v_a_2994_: *mut leanh::LeanObject,
    mut v_as_2995_: *mut leanh::LeanObject,
    mut v_sz_2996_: *mut leanh::LeanObject,
    mut v_i_2997_: *mut leanh::LeanObject,
    mut v_b_2998_: *mut leanh::LeanObject,
    mut v___y_2999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6172__boxed_3000_: u8 = 0;
    let mut v_sz_boxed_3001_: usize = 0;
    let mut v_i_boxed_3002_: usize = 0;
    let mut v_res_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_6172__boxed_3000_ = (leanh::lean_unbox(v_a_2994_) as u8);
    v_sz_boxed_3001_ = leanh::lean_unbox_usize(v_sz_2996_);
    leanh::lean_dec(v_sz_2996_);
    v_i_boxed_3002_ = leanh::lean_unbox_usize(v_i_2997_);
    leanh::lean_dec(v_i_2997_);
    v_res_3003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4(v_env_2991_, v_opts_2992_, v___x_2993_, v_a_6172__boxed_3000_, v_as_2995_, v_sz_boxed_3001_, v_i_boxed_3002_, v_b_2998_);
    leanh::lean_dec_ref(v_as_2995_);
    leanh::lean_dec_ref(v___x_2993_);
    leanh::lean_dec_ref(v_opts_2992_);
    return v_res_3003_;
}
pub unsafe fn _init_l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3005_ = l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__0;
    v___x_3006_ = lean_mk_io_user_error(v___x_3005_);
    return v___x_3006_;
}
pub unsafe fn lean_run_init_attrs(
    mut v_env_3009_: *mut leanh::LeanObject,
    mut v_opts_3010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v___x_3017_: u8 = 0;
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3025_: usize = 0;
    let mut v___x_3026_: usize = 0;
    let mut v___x_3027_: u8 = 0;
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3031_: u8 = 0;
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3036_: u8 = 0;
    let mut v_unused_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3041_: u8 = 0;
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut v_isSharedCheck_3046_: u8 = 0;
    let mut v_a_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3050_: u8 = 0;
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3012_ = l_Lean_isInitializerExecutionEnabled();
                if leanh::lean_obj_tag(v___x_3012_) == 0 {
                    v_a_3013_ = leanh::lean_ctor_get(v___x_3012_, 0);
                    v_isSharedCheck_3046_ = (!leanh::lean_is_exclusive(v___x_3012_)) as u8;
                    if v_isSharedCheck_3046_ == 0 {
                        v___x_3015_ = v___x_3012_;
                        v_isShared_3016_ = v_isSharedCheck_3046_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3013_);
                        leanh::lean_dec(v___x_3012_);
                        v___x_3015_ = leanh::lean_box(0);
                        v_isShared_3016_ = v_isSharedCheck_3046_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_opts_3010_);
                    leanh::lean_dec_ref(v_env_3009_);
                    v_a_3047_ = leanh::lean_ctor_get(v___x_3012_, 0);
                    v_isSharedCheck_3054_ = (!leanh::lean_is_exclusive(v___x_3012_)) as u8;
                    if v_isSharedCheck_3054_ == 0 {
                        v___x_3049_ = v___x_3012_;
                        v_isShared_3050_ = v_isSharedCheck_3054_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3047_);
                        leanh::lean_dec(v___x_3012_);
                        v___x_3049_ = leanh::lean_box(0);
                        v_isShared_3050_ = v_isSharedCheck_3054_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3017_ = (leanh::lean_unbox(v_a_3013_) as u8);
                if v___x_3017_ == 0 {
                    leanh::lean_dec(v_a_3013_);
                    leanh::lean_dec_ref(v_opts_3010_);
                    leanh::lean_dec_ref(v_env_3009_);
                    v___x_3018_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__1_once), _init_l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__1);
                    if v_isShared_3016_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3015_, 1);
                        leanh::lean_ctor_set(v___x_3015_, 0, v___x_3018_);
                        v___x_3020_ = v___x_3015_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3021_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
                        v___x_3020_ = v_reuseFailAlloc_3021_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3015_);
                    v___x_3022_ = l_Lean_Environment_header(v_env_3009_);
                    v_modules_3023_ = leanh::lean_ctor_get(v___x_3022_, 3);
                    leanh::lean_inc_ref(v_modules_3023_);
                    v___x_3024_ =
                        l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__2;
                    v_sz_3025_ = lean_array_size(v_modules_3023_);
                    v___x_3026_ = 0usize;
                    v___x_3027_ = (leanh::lean_unbox(v_a_3013_) as u8);
                    leanh::lean_dec(v_a_3013_);
                    v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4(v_env_3009_, v_opts_3010_, v___x_3022_, v___x_3027_, v_modules_3023_, v_sz_3025_, v___x_3026_, v___x_3024_);
                    leanh::lean_dec_ref(v_modules_3023_);
                    leanh::lean_dec_ref(v___x_3022_);
                    leanh::lean_dec_ref(v_opts_3010_);
                    if leanh::lean_obj_tag(v___x_3028_) == 0 {
                        v_isSharedCheck_3036_ =
                            (!leanh::lean_is_exclusive(v___x_3028_)) as u8;
                        if v_isSharedCheck_3036_ == 0 {
                            v_unused_3037_ = leanh::lean_ctor_get(v___x_3028_, 0);
                            leanh::lean_dec(v_unused_3037_);
                            v___x_3030_ = v___x_3028_;
                            v_isShared_3031_ = v_isSharedCheck_3036_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3028_);
                            v___x_3030_ = leanh::lean_box(0);
                            v_isShared_3031_ = v_isSharedCheck_3036_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3038_ = leanh::lean_ctor_get(v___x_3028_, 0);
                        v_isSharedCheck_3045_ =
                            (!leanh::lean_is_exclusive(v___x_3028_)) as u8;
                        if v_isSharedCheck_3045_ == 0 {
                            v___x_3040_ = v___x_3028_;
                            v_isShared_3041_ = v_isSharedCheck_3045_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3038_);
                            leanh::lean_dec(v___x_3028_);
                            v___x_3040_ = leanh::lean_box(0);
                            v_isShared_3041_ = v_isSharedCheck_3045_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3020_;
            }
            3 => {
                v___x_3032_ = leanh::lean_box(0);
                if v_isShared_3031_ == 0 {
                    leanh::lean_ctor_set(v___x_3030_, 0, v___x_3032_);
                    v___x_3034_ = v___x_3030_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
                    v___x_3034_ = v_reuseFailAlloc_3035_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3034_;
            }
            5 => {
                if v_isShared_3041_ == 0 {
                    v___x_3043_ = v___x_3040_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3044_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
                    v___x_3043_ = v_reuseFailAlloc_3044_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3043_;
            }
            7 => {
                if v_isShared_3050_ == 0 {
                    v___x_3052_ = v___x_3049_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3053_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
                    v___x_3052_ = v_reuseFailAlloc_3053_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___boxed(
    mut v_env_3055_: *mut leanh::LeanObject,
    mut v_opts_3056_: *mut leanh::LeanObject,
    mut v_a_3057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3058_ = lean_run_init_attrs(v_env_3055_, v_opts_3056_);
    return v_res_3058_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_InitAttr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Stream(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_NameMangling(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3590725331____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_interpretedModInits = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_interpretedModInits);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_regularInitAttr = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_regularInitAttr);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_builtinInitAttr = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_builtinInitAttr);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_InitAttr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_registerInitAttr___auto__1 = _init_l_Lean_registerInitAttr___auto__1();
    leanh::lean_mark_persistent(l_Lean_registerInitAttr___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_InitAttr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_InfoTree_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Stream(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_NameMangling(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_ModPkgExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_InitAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_InitAttr(builtin);
}