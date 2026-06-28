// Lean compiler output
// Module: Lean.Compiler.InitAttr
// Imports: Lean.AddDecl Lean.Elab.InfoTree.Main Init.Data.Range.Polymorphic.Stream Lean.Compiler.NameMangling Lean.Compiler.ModPkgExt
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Stream::{
    initialize_Init_Data_Range_Polymorphic_Stream,
    runtime_initialize_Init_Data_Range_Polymorphic_Stream,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_mkAtom,
    l_Lean_replaceRef,
};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_string_dec_eq,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___closed__0_value:
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
    m_data: [73, 79, 0],
};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_registerInitAttrUnsafe___lam__0___closed__0_value: LeanStringObject<49> =
    LeanStringObject {
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
            105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 102, 117, 110,
            99, 116, 105, 111, 110, 32, 109, 117, 115, 116, 32, 104, 97, 118, 101, 32, 116, 121,
            112, 101, 32, 96, 73, 79, 32, 85, 110, 105, 116, 96, 0,
        ],
    };
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_registerInitAttrUnsafe___lam__0___closed__2_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 102, 117, 110,
            99, 116, 105, 111, 110, 32, 96, 0,
        ],
    };
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_registerInitAttrUnsafe___lam__0___closed__4_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            96, 32, 109, 117, 115, 116, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101, 32, 111,
            102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 73, 79, 32, 60, 116, 121, 112,
            101, 62, 96, 0,
        ],
    };
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___lam__0___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_registerInitAttrUnsafe___lam__0___closed__6_value: LeanStringObject<16> =
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
            96, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 0,
        ],
    };
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___lam__0___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttrUnsafe___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_registerInitAttrUnsafe___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_registerInitAttrUnsafe___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_registerInitAttrUnsafe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___closed__0_value) as *mut LeanObject;
pub static l_Lean_registerInitAttrUnsafe___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_registerInitAttrUnsafe___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_registerInitAttrUnsafe___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___closed__1_value) as *mut LeanObject;
pub static l_Lean_registerInitAttrUnsafe___closed__2_value: LeanStringObject<47> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_registerInitAttrUnsafe___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttrUnsafe___closed__2_value) as *mut LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__3_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__3_value) as *mut LeanObject;
static l_Lean_registerInitAttr___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_registerInitAttr___auto__1___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__5_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__6_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__6_value) as *mut LeanObject;
static l_Lean_registerInitAttr___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_registerInitAttr___auto__1___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__8_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__8_value) as *mut LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__9_value) as *mut LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__10_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__10_value) as *mut LeanObject;
static l_Lean_registerInitAttr___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_registerInitAttr___auto__1___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__11_value) as *mut LeanObject;
static mut l_Lean_registerInitAttr___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_registerInitAttr___auto__1___closed__14_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__14_value) as *mut LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__15_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__15_value) as *mut LeanObject;
static l_Lean_registerInitAttr___auto__1___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__16_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__16_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_registerInitAttr___auto__1___closed__16_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__16_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__14_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_registerInitAttr___auto__1___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__16_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__15_value)
                as *mut LeanObject,
            7677164612348466033 as *mut LeanObject,
        ],
    };
static mut l_Lean_registerInitAttr___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__16_value) as *mut LeanObject;
pub static l_Lean_registerInitAttr___auto__1___closed__17_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_registerInitAttr___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__17_value) as *mut LeanObject;
static mut l_Lean_registerInitAttr___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__26: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__27: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_registerInitAttr___auto__1___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_registerInitAttr___auto__1___closed__28: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_registerInitAttr___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 105, 116, 0]};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value) as *mut LeanObject,15209775132330820936 as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [114, 101, 103, 117, 108, 97, 114, 73, 110, 105, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value) as *mut LeanObject,12053862841313483068 as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1___closed__0_value: LeanStringObject<677> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 677, m_capacity: 677, m_length: 676, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 115, 32, 97, 110, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 46, 32, 73, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 115, 32, 97, 114, 101, 32, 114, 117, 110, 32, 105, 110, 32, 102, 105, 108, 101, 115, 32, 116, 104, 97, 116, 32, 105, 109, 112, 111, 114, 116, 32, 116, 104, 101, 10, 102, 105, 108, 101, 32, 116, 104, 101, 121, 32, 97, 114, 101, 32, 100, 101, 102, 105, 110, 101, 100, 32, 105, 110, 46, 10, 10, 84, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 99, 111, 109, 101, 115, 32, 105, 110, 32, 116, 119, 111, 32, 107, 105, 110, 100, 115, 58, 32, 87, 105, 116, 104, 111, 117, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 44, 32, 116, 104, 101, 32, 116, 97, 103, 103, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 115, 104, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101, 10, 96, 73, 79, 32, 85, 110, 105, 116, 96, 32, 97, 110, 100, 32, 97, 114, 101, 32, 115, 105, 109, 112, 108, 121, 32, 114, 117, 110, 32, 100, 117, 114, 105, 110, 103, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 46, 32, 87, 105, 116, 104, 32, 97, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 97, 115, 32, 97, 32, 97, 114, 103, 117, 109, 101, 110, 116, 44, 32, 116, 104, 101, 10, 116, 97, 103, 103, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 97, 110, 32, 111, 112, 97, 113, 117, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 97, 110, 100, 32, 116, 104, 101, 32, 112, 114, 111, 118, 105, 100, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 97, 110, 32, 97, 99, 116, 105, 111, 110, 32, 105, 110, 32, 96, 73, 79, 96, 10, 116, 104, 97, 116, 32, 114, 101, 116, 117, 114, 110, 115, 32, 97, 32, 118, 97, 108, 117, 101, 32, 111, 102, 32, 116, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 116, 97, 103, 103, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 46, 32, 83, 117, 99, 104, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 115, 32, 115, 116, 111, 114, 101, 10, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 118, 97, 108, 117, 101, 32, 97, 110, 100, 32, 109, 97, 107, 101, 32, 105, 116, 32, 97, 99, 99, 101, 115, 115, 105, 98, 108, 101, 32, 116, 104, 114, 111, 117, 103, 104, 32, 116, 104, 101, 32, 116, 97, 103, 103, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 46, 10, 10, 84, 104, 101, 32, 96, 105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 96, 32, 99, 111, 109, 109, 97, 110, 100, 32, 115, 104, 111, 117, 108, 100, 32, 117, 115, 117, 97, 108, 108, 121, 32, 98, 101, 32, 112, 114, 101, 102, 101, 114, 114, 101, 100, 32, 111, 118, 101, 114, 32, 117, 115, 105, 110, 103, 32, 116, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 100, 105, 114, 101, 99, 116, 108, 121, 46, 10, 0]};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 88 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 101 as usize) << 1) | 1) as *mut LeanObject,((( 91 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__1_value) as *mut LeanObject,((( 91 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 101 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 101 as usize) << 1) | 1) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__3_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__4_value) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 105, 110, 105, 116, 0]};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value) as *mut LeanObject,4634360312921132838 as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [98, 117, 105, 108, 116, 105, 110, 73, 110, 105, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_registerInitAttr___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value) as *mut LeanObject,2829956051969401032 as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1___closed__0_value: LeanStringObject<178> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 178, m_capacity: 178, m_length: 177, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 115, 32, 97, 32, 98, 117, 105, 108, 116, 105, 110, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 46, 10, 10, 84, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 105, 115, 32, 117, 115, 101, 100, 32, 105, 110, 116, 101, 114, 110, 97, 108, 108, 121, 32, 116, 111, 32, 100, 101, 102, 105, 110, 101, 32, 98, 117, 105, 108, 116, 105, 110, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 115, 32, 102, 111, 114, 32, 98, 111, 111, 116, 115, 116, 114, 97, 112, 112, 105, 110, 103, 32, 97, 110, 100, 10, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 32, 117, 115, 101, 100, 32, 111, 116, 104, 101, 114, 119, 105, 115, 101, 46, 10, 0]};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 103 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 110 as usize) << 1) | 1) as *mut LeanObject,((( 100 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__1_value) as *mut LeanObject,((( 100 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 110 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 110 as usize) << 1) | 1) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__3_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__4_value) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_declareBuiltin___lam__0___closed__0_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___closed__0_value
        ) as *mut LeanObject,
        4390522573605260290 as *mut LeanObject,
    ],
};
static mut l_Lean_declareBuiltin___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltin___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_declareBuiltin___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_declareBuiltin___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_declareBuiltin___lam__0___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType___closed__0_value)
            as *mut LeanObject,
        9833841078580172006 as *mut LeanObject,
    ],
};
static mut l_Lean_declareBuiltin___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltin___lam__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_declareBuiltin___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_declareBuiltin___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_declareBuiltin___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_declareBuiltin___lam__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_declareBuiltin___closed__0_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_declareBuiltin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltin___closed__0_value) as *mut LeanObject;
pub static l_Lean_declareBuiltin___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_declareBuiltin___closed__0_value) as *mut LeanObject,
        12748856906745825949 as *mut LeanObject,
    ],
};
static mut l_Lean_declareBuiltin___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltin___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__0_value:
    LeanStringObject<92> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__0_value)
        as *mut LeanObject;
static mut l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__2_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__2_value)
        as *mut LeanObject;
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(
    mut v_x_1531_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1531_) == 5 {
        let mut v_fn_1532_: *mut LeanObject = core::ptr::null_mut();
        v_fn_1532_ = lean_ctor_get(v_x_1531_, 0);
        if lean_obj_tag(v_fn_1532_) == 4 {
            let mut v_declName_1533_: *mut LeanObject = core::ptr::null_mut();
            v_declName_1533_ = lean_ctor_get(v_fn_1532_, 0);
            if lean_obj_tag(v_declName_1533_) == 1 {
                let mut v_pre_1534_: *mut LeanObject = core::ptr::null_mut();
                v_pre_1534_ = lean_ctor_get(v_declName_1533_, 0);
                if lean_obj_tag(v_pre_1534_) == 0 {
                    let mut v_arg_1535_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_str_1536_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1538_: u8 = 0;
                    v_arg_1535_ = lean_ctor_get(v_x_1531_, 1);
                    v_str_1536_ = lean_ctor_get(v_declName_1533_, 1);
                    v___x_1537_ =
                        l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___closed__0;
                    v___x_1538_ = lean_string_dec_eq(v_str_1536_, v___x_1537_);
                    if v___x_1538_ == 0 {
                        let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
                        v___x_1539_ = lean_box(0);
                        return v___x_1539_;
                    } else {
                        let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
                        lean_inc_ref(v_arg_1535_);
                        v___x_1540_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1540_, 0, v_arg_1535_);
                        return v___x_1540_;
                    }
                } else {
                    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
                    v___x_1541_ = lean_box(0);
                    return v___x_1541_;
                }
            } else {
                let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
                v___x_1542_ = lean_box(0);
                return v___x_1542_;
            }
        } else {
            let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
            v___x_1543_ = lean_box(0);
            return v___x_1543_;
        }
    } else {
        let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
        v___x_1544_ = lean_box(0);
        return v___x_1544_;
    }
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___boxed(
    mut v_x_1545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1546_: *mut LeanObject = core::ptr::null_mut();
    v_res_1546_ = l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(v_x_1545_);
    lean_dec_ref(v_x_1545_);
    return v_res_1546_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType(
    mut v_x_1548_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1548_) == 4 {
        let mut v_declName_1549_: *mut LeanObject = core::ptr::null_mut();
        v_declName_1549_ = lean_ctor_get(v_x_1548_, 0);
        if lean_obj_tag(v_declName_1549_) == 1 {
            let mut v_pre_1550_: *mut LeanObject = core::ptr::null_mut();
            v_pre_1550_ = lean_ctor_get(v_declName_1549_, 0);
            if lean_obj_tag(v_pre_1550_) == 0 {
                let mut v_str_1551_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1553_: u8 = 0;
                v_str_1551_ = lean_ctor_get(v_declName_1549_, 1);
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
    mut v_x_1557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1558_: u8 = 0;
    let mut v_r_1559_: *mut LeanObject = core::ptr::null_mut();
    v_res_1558_ = l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType(v_x_1557_);
    lean_dec_ref(v_x_1557_);
    v_r_1559_ = lean_box((v_res_1558_) as usize);
    return v_r_1559_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit(
    mut v_type_1560_: *mut LeanObject,
) -> u8 {
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    v___x_1561_ = l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(v_type_1560_);
    if lean_obj_tag(v___x_1561_) == 1 {
        let mut v_val_1562_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1563_: u8 = 0;
        v_val_1562_ = lean_ctor_get(v___x_1561_, 0);
        lean_inc(v_val_1562_);
        lean_dec_ref_known(v___x_1561_, 1);
        v___x_1563_ = l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType(v_val_1562_);
        lean_dec(v_val_1562_);
        return v___x_1563_;
    } else {
        let mut v___x_1564_: u8 = 0;
        lean_dec(v___x_1561_);
        v___x_1564_ = 0;
        return v___x_1564_;
    }
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit___boxed(
    mut v_type_1565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1566_: u8 = 0;
    let mut v_r_1567_: *mut LeanObject = core::ptr::null_mut();
    v_res_1566_ = l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit(v_type_1565_);
    lean_dec_ref(v_type_1565_);
    v_r_1567_ = lean_box((v_res_1566_) as usize);
    return v_r_1567_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_runModInitCore___boxed(
    mut v_sym_1570_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1572_: *mut LeanObject = core::ptr::null_mut();
    v_res_1572_ = lean_run_mod_init_core(v_sym_1570_);
    lean_dec_ref(v_sym_1570_);
    return v_res_1572_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_runModInit(
    mut v_mod_1573_: *mut LeanObject,
    mut v_pkg_x3f_1574_: *mut LeanObject,
    mut v_phases_1575_: u8,
) -> *mut LeanObject {
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    v___x_1577_ =
        l_Lean_mkModuleInitializationFunctionName(v_mod_1573_, v_pkg_x3f_1574_, v_phases_1575_);
    v___x_1578_ = lean_run_mod_init_core(v___x_1577_);
    lean_dec_ref(v___x_1577_);
    return v___x_1578_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_runModInit___boxed(
    mut v_mod_1579_: *mut LeanObject,
    mut v_pkg_x3f_1580_: *mut LeanObject,
    mut v_phases_1581_: *mut LeanObject,
    mut v_a_1582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phases_boxed_1583_: u8 = 0;
    let mut v_res_1584_: *mut LeanObject = core::ptr::null_mut();
    v_phases_boxed_1583_ = (lean_unbox(v_phases_1581_) as u8);
    v_res_1584_ = l___private_Lean_Compiler_InitAttr_0__Lean_runModInit(
        v_mod_1579_,
        v_pkg_x3f_1580_,
        v_phases_boxed_1583_,
    );
    lean_dec(v_pkg_x3f_1580_);
    return v_res_1584_;
}
pub unsafe fn l_Lean_runInit___boxed(
    mut v_env_1590_: *mut LeanObject,
    mut v_opts_1591_: *mut LeanObject,
    mut v_decl_1592_: *mut LeanObject,
    mut v_initDecl_1593_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1595_: *mut LeanObject = core::ptr::null_mut();
    v_res_1595_ = lean_run_init(v_env_1590_, v_opts_1591_, v_decl_1592_, v_initDecl_1593_);
    lean_dec(v_initDecl_1593_);
    lean_dec(v_decl_1592_);
    lean_dec_ref(v_opts_1591_);
    lean_dec_ref(v_env_1590_);
    return v_res_1595_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3590725331____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Lean_NameSet_empty;
    v___x_1598_ = lean_st_mk_ref(v___x_1597_);
    v___x_1599_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1599_, 0, v___x_1598_);
    return v___x_1599_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3590725331____hygCtx___hyg_2____boxed(
    mut v_a_1600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1601_: *mut LeanObject = core::ptr::null_mut();
    v_res_1601_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3590725331____hygCtx___hyg_2_();
    return v_res_1601_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    v___x_1602_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1602_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    v___x_1603_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__0);
    v___x_1604_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1604_, 0, v___x_1603_);
    return v___x_1604_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2()
-> *mut LeanObject {
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    v___x_1605_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1);
    v___x_1606_ = lean_unsigned_to_nat(0);
    v___x_1607_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1607_, 0, v___x_1606_);
    lean_ctor_set(v___x_1607_, 1, v___x_1606_);
    lean_ctor_set(v___x_1607_, 2, v___x_1606_);
    lean_ctor_set(v___x_1607_, 3, v___x_1606_);
    lean_ctor_set(v___x_1607_, 4, v___x_1605_);
    lean_ctor_set(v___x_1607_, 5, v___x_1605_);
    lean_ctor_set(v___x_1607_, 6, v___x_1605_);
    lean_ctor_set(v___x_1607_, 7, v___x_1605_);
    lean_ctor_set(v___x_1607_, 8, v___x_1605_);
    lean_ctor_set(v___x_1607_, 9, v___x_1605_);
    return v___x_1607_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    v___x_1608_ = lean_unsigned_to_nat(32);
    v___x_1609_ = lean_mk_empty_array_with_capacity(v___x_1608_);
    v___x_1610_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1610_, 0, v___x_1609_);
    return v___x_1610_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__4()
-> *mut LeanObject {
    let mut v___x_1611_: usize = 0;
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    v___x_1611_ = 5usize;
    v___x_1612_ = lean_unsigned_to_nat(0);
    v___x_1613_ = lean_unsigned_to_nat(32);
    v___x_1614_ = lean_mk_empty_array_with_capacity(v___x_1613_);
    v___x_1615_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__3);
    v___x_1616_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1616_, 0, v___x_1615_);
    lean_ctor_set(v___x_1616_, 1, v___x_1614_);
    lean_ctor_set(v___x_1616_, 2, v___x_1612_);
    lean_ctor_set(v___x_1616_, 3, v___x_1612_);
    lean_ctor_set_usize(v___x_1616_, 4, v___x_1611_);
    return v___x_1616_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5()
-> *mut LeanObject {
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    v___x_1617_ = lean_box(1);
    v___x_1618_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__4);
    v___x_1619_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__1);
    v___x_1620_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1620_, 0, v___x_1619_);
    lean_ctor_set(v___x_1620_, 1, v___x_1618_);
    lean_ctor_set(v___x_1620_, 2, v___x_1617_);
    return v___x_1620_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2(
    mut v_msgData_1621_: *mut LeanObject,
    mut v___y_1622_: *mut LeanObject,
    mut v___y_1623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    v___x_1625_ = lean_st_ref_get(v___y_1623_);
    v_env_1626_ = lean_ctor_get(v___x_1625_, 0);
    lean_inc_ref(v_env_1626_);
    lean_dec(v___x_1625_);
    v_options_1627_ = lean_ctor_get(v___y_1622_, 2);
    v___x_1628_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2);
    v___x_1629_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5);
    lean_inc_ref(v_options_1627_);
    v___x_1630_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1630_, 0, v_env_1626_);
    lean_ctor_set(v___x_1630_, 1, v___x_1628_);
    lean_ctor_set(v___x_1630_, 2, v___x_1629_);
    lean_ctor_set(v___x_1630_, 3, v_options_1627_);
    v___x_1631_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1631_, 0, v___x_1630_);
    lean_ctor_set(v___x_1631_, 1, v_msgData_1621_);
    v___x_1632_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1632_, 0, v___x_1631_);
    return v___x_1632_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___boxed(
    mut v_msgData_1633_: *mut LeanObject,
    mut v___y_1634_: *mut LeanObject,
    mut v___y_1635_: *mut LeanObject,
    mut v___y_1636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1637_: *mut LeanObject = core::ptr::null_mut();
    v_res_1637_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2(v_msgData_1633_, v___y_1634_, v___y_1635_);
    lean_dec(v___y_1635_);
    lean_dec_ref(v___y_1634_);
    return v_res_1637_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
    mut v_msg_1638_: *mut LeanObject,
    mut v___y_1639_: *mut LeanObject,
    mut v___y_1640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1642_ = lean_ctor_get(v___y_1639_, 5);
                v___x_1643_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2(v_msg_1638_, v___y_1639_, v___y_1640_);
                v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
                v_isSharedCheck_1652_ = (!lean_is_exclusive(v___x_1643_)) as u8;
                if v_isSharedCheck_1652_ == 0 {
                    v___x_1646_ = v___x_1643_;
                    v_isShared_1647_ = v_isSharedCheck_1652_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1644_);
                    lean_dec(v___x_1643_);
                    v___x_1646_ = lean_box(0);
                    v_isShared_1647_ = v_isSharedCheck_1652_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1642_);
                v___x_1648_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1648_, 0, v_ref_1642_);
                lean_ctor_set(v___x_1648_, 1, v_a_1644_);
                if v_isShared_1647_ == 0 {
                    lean_ctor_set_tag(v___x_1646_, 1);
                    lean_ctor_set(v___x_1646_, 0, v___x_1648_);
                    v___x_1650_ = v___x_1646_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
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
    mut v_msg_1653_: *mut LeanObject,
    mut v___y_1654_: *mut LeanObject,
    mut v___y_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1657_: *mut LeanObject = core::ptr::null_mut();
    v_res_1657_ = l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
        v_msg_1653_,
        v___y_1654_,
        v___y_1655_,
    );
    lean_dec(v___y_1655_);
    lean_dec_ref(v___y_1654_);
    return v_res_1657_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8___redArg(
    mut v_ref_1658_: *mut LeanObject,
    mut v_msg_1659_: *mut LeanObject,
    mut v___y_1660_: *mut LeanObject,
    mut v___y_1661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1675_: u8 = 0;
    let mut v_cancelTk_x3f_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1677_: u8 = 0;
    let mut v_inheritedTraceOptions_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1663_ = lean_ctor_get(v___y_1660_, 0);
    v_fileMap_1664_ = lean_ctor_get(v___y_1660_, 1);
    v_options_1665_ = lean_ctor_get(v___y_1660_, 2);
    v_currRecDepth_1666_ = lean_ctor_get(v___y_1660_, 3);
    v_maxRecDepth_1667_ = lean_ctor_get(v___y_1660_, 4);
    v_ref_1668_ = lean_ctor_get(v___y_1660_, 5);
    v_currNamespace_1669_ = lean_ctor_get(v___y_1660_, 6);
    v_openDecls_1670_ = lean_ctor_get(v___y_1660_, 7);
    v_initHeartbeats_1671_ = lean_ctor_get(v___y_1660_, 8);
    v_maxHeartbeats_1672_ = lean_ctor_get(v___y_1660_, 9);
    v_quotContext_1673_ = lean_ctor_get(v___y_1660_, 10);
    v_currMacroScope_1674_ = lean_ctor_get(v___y_1660_, 11);
    v_diag_1675_ = lean_ctor_get_uint8(
        v___y_1660_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1676_ = lean_ctor_get(v___y_1660_, 12);
    v_suppressElabErrors_1677_ = lean_ctor_get_uint8(
        v___y_1660_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1678_ = lean_ctor_get(v___y_1660_, 13);
    v_ref_1679_ = l_Lean_replaceRef(v_ref_1658_, v_ref_1668_);
    lean_inc_ref(v_inheritedTraceOptions_1678_);
    lean_inc(v_cancelTk_x3f_1676_);
    lean_inc(v_currMacroScope_1674_);
    lean_inc(v_quotContext_1673_);
    lean_inc(v_maxHeartbeats_1672_);
    lean_inc(v_initHeartbeats_1671_);
    lean_inc(v_openDecls_1670_);
    lean_inc(v_currNamespace_1669_);
    lean_inc(v_maxRecDepth_1667_);
    lean_inc(v_currRecDepth_1666_);
    lean_inc_ref(v_options_1665_);
    lean_inc_ref(v_fileMap_1664_);
    lean_inc_ref(v_fileName_1663_);
    v___x_1680_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1680_, 0, v_fileName_1663_);
    lean_ctor_set(v___x_1680_, 1, v_fileMap_1664_);
    lean_ctor_set(v___x_1680_, 2, v_options_1665_);
    lean_ctor_set(v___x_1680_, 3, v_currRecDepth_1666_);
    lean_ctor_set(v___x_1680_, 4, v_maxRecDepth_1667_);
    lean_ctor_set(v___x_1680_, 5, v_ref_1679_);
    lean_ctor_set(v___x_1680_, 6, v_currNamespace_1669_);
    lean_ctor_set(v___x_1680_, 7, v_openDecls_1670_);
    lean_ctor_set(v___x_1680_, 8, v_initHeartbeats_1671_);
    lean_ctor_set(v___x_1680_, 9, v_maxHeartbeats_1672_);
    lean_ctor_set(v___x_1680_, 10, v_quotContext_1673_);
    lean_ctor_set(v___x_1680_, 11, v_currMacroScope_1674_);
    lean_ctor_set(v___x_1680_, 12, v_cancelTk_x3f_1676_);
    lean_ctor_set(v___x_1680_, 13, v_inheritedTraceOptions_1678_);
    lean_ctor_set_uint8(
        v___x_1680_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1675_,
    );
    lean_ctor_set_uint8(
        v___x_1680_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1677_,
    );
    v___x_1681_ = l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
        v_msg_1659_,
        v___x_1680_,
        v___y_1661_,
    );
    lean_dec_ref_known(v___x_1680_, 14);
    return v___x_1681_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8___redArg___boxed(
    mut v_ref_1682_: *mut LeanObject,
    mut v_msg_1683_: *mut LeanObject,
    mut v___y_1684_: *mut LeanObject,
    mut v___y_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1687_: *mut LeanObject = core::ptr::null_mut();
    v_res_1687_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8___redArg(v_ref_1682_, v_msg_1683_, v___y_1684_, v___y_1685_);
    lean_dec(v___y_1685_);
    lean_dec_ref(v___y_1684_);
    lean_dec(v_ref_1682_);
    return v_res_1687_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    v___x_1689_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__0;
    v___x_1690_ = l_Lean_stringToMessageData(v___x_1689_);
    return v___x_1690_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    v___x_1692_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__2;
    v___x_1693_ = l_Lean_stringToMessageData(v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    v___x_1695_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__4;
    v___x_1696_ = l_Lean_stringToMessageData(v___x_1695_);
    return v___x_1696_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    v___x_1698_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__6;
    v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
    return v___x_1699_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    v___x_1701_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__8;
    v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
    return v___x_1702_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    v___x_1704_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__10;
    v___x_1705_ = l_Lean_stringToMessageData(v___x_1704_);
    return v___x_1705_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    v___x_1707_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__12;
    v___x_1708_ = l_Lean_stringToMessageData(v___x_1707_);
    return v___x_1708_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg(
    mut v_msg_1709_: *mut LeanObject,
    mut v_declHint_1710_: *mut LeanObject,
    mut v___y_1711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v_isExporting_1716_: u8 = 0;
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: u8 = 0;
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1738_: u8 = 0;
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1713_ = lean_st_ref_get(v___y_1711_);
                v_env_1714_ = lean_ctor_get(v___x_1713_, 0);
                lean_inc_ref(v_env_1714_);
                lean_dec(v___x_1713_);
                v___x_1715_ = l_Lean_Name_isAnonymous(v_declHint_1710_);
                if v___x_1715_ == 0 {
                    v_isExporting_1716_ = lean_ctor_get_uint8(
                        v_env_1714_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1716_ == 0 {
                        lean_dec_ref(v_env_1714_);
                        lean_dec(v_declHint_1710_);
                        v___x_1717_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1717_, 0, v_msg_1709_);
                        return v___x_1717_;
                    } else {
                        lean_inc_ref(v_env_1714_);
                        v___x_1718_ = l_Lean_Environment_setExporting(v_env_1714_, v___x_1715_);
                        lean_inc(v_declHint_1710_);
                        lean_inc_ref(v___x_1718_);
                        v___x_1719_ = l_Lean_Environment_contains(
                            v___x_1718_,
                            v_declHint_1710_,
                            v_isExporting_1716_,
                        );
                        if v___x_1719_ == 0 {
                            lean_dec_ref(v___x_1718_);
                            lean_dec_ref(v_env_1714_);
                            lean_dec(v_declHint_1710_);
                            v___x_1720_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1720_, 0, v_msg_1709_);
                            return v___x_1720_;
                        } else {
                            v___x_1721_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__2);
                            v___x_1722_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1_spec__2___closed__5);
                            v___x_1723_ = l_Lean_Options_empty;
                            v___x_1724_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1724_, 0, v___x_1718_);
                            lean_ctor_set(v___x_1724_, 1, v___x_1721_);
                            lean_ctor_set(v___x_1724_, 2, v___x_1722_);
                            lean_ctor_set(v___x_1724_, 3, v___x_1723_);
                            lean_inc(v_declHint_1710_);
                            v___x_1725_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1710_, v___x_1715_);
                            v_c_1726_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1726_, 0, v___x_1724_);
                            lean_ctor_set(v_c_1726_, 1, v___x_1725_);
                            v___x_1727_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1714_,
                                v_declHint_1710_,
                            );
                            if lean_obj_tag(v___x_1727_) == 0 {
                                lean_dec_ref(v_env_1714_);
                                lean_dec(v_declHint_1710_);
                                v___x_1728_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1);
                                v___x_1729_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1729_, 0, v___x_1728_);
                                lean_ctor_set(v___x_1729_, 1, v_c_1726_);
                                v___x_1730_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__3);
                                v___x_1731_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1731_, 0, v___x_1729_);
                                lean_ctor_set(v___x_1731_, 1, v___x_1730_);
                                v___x_1732_ = l_Lean_MessageData_note(v___x_1731_);
                                v___x_1733_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1733_, 0, v_msg_1709_);
                                lean_ctor_set(v___x_1733_, 1, v___x_1732_);
                                v___x_1734_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1734_, 0, v___x_1733_);
                                return v___x_1734_;
                            } else {
                                v_val_1735_ = lean_ctor_get(v___x_1727_, 0);
                                v_isSharedCheck_1770_ = (!lean_is_exclusive(v___x_1727_)) as u8;
                                if v_isSharedCheck_1770_ == 0 {
                                    v___x_1737_ = v___x_1727_;
                                    v_isShared_1738_ = v_isSharedCheck_1770_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1735_);
                                    lean_dec(v___x_1727_);
                                    v___x_1737_ = lean_box(0);
                                    v_isShared_1738_ = v_isSharedCheck_1770_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1714_);
                    lean_dec(v_declHint_1710_);
                    v___x_1771_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1771_, 0, v_msg_1709_);
                    return v___x_1771_;
                }
            }
            1 => {
                v___x_1739_ = lean_box(0);
                v___x_1740_ = l_Lean_Environment_header(v_env_1714_);
                lean_dec_ref(v_env_1714_);
                v___x_1741_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1740_);
                v_mod_1742_ = lean_array_get(v___x_1739_, v___x_1741_, v_val_1735_);
                lean_dec(v_val_1735_);
                lean_dec_ref(v___x_1741_);
                v___x_1743_ = l_Lean_isPrivateName(v_declHint_1710_);
                lean_dec(v_declHint_1710_);
                if v___x_1743_ == 0 {
                    v___x_1744_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__5);
                    v___x_1745_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1745_, 0, v___x_1744_);
                    lean_ctor_set(v___x_1745_, 1, v_c_1726_);
                    v___x_1746_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__7);
                    v___x_1747_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1747_, 0, v___x_1745_);
                    lean_ctor_set(v___x_1747_, 1, v___x_1746_);
                    v___x_1748_ = l_Lean_MessageData_ofName(v_mod_1742_);
                    v___x_1749_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1749_, 0, v___x_1747_);
                    lean_ctor_set(v___x_1749_, 1, v___x_1748_);
                    v___x_1750_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__9);
                    v___x_1751_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1751_, 0, v___x_1749_);
                    lean_ctor_set(v___x_1751_, 1, v___x_1750_);
                    v___x_1752_ = l_Lean_MessageData_note(v___x_1751_);
                    v___x_1753_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1753_, 0, v_msg_1709_);
                    lean_ctor_set(v___x_1753_, 1, v___x_1752_);
                    if v_isShared_1738_ == 0 {
                        lean_ctor_set_tag(v___x_1737_, 0);
                        lean_ctor_set(v___x_1737_, 0, v___x_1753_);
                        v___x_1755_ = v___x_1737_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
                        v___x_1755_ = v_reuseFailAlloc_1756_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1757_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__1);
                    v___x_1758_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1758_, 0, v___x_1757_);
                    lean_ctor_set(v___x_1758_, 1, v_c_1726_);
                    v___x_1759_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__11);
                    v___x_1760_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1760_, 0, v___x_1758_);
                    lean_ctor_set(v___x_1760_, 1, v___x_1759_);
                    v___x_1761_ = l_Lean_MessageData_ofName(v_mod_1742_);
                    v___x_1762_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1762_, 0, v___x_1760_);
                    lean_ctor_set(v___x_1762_, 1, v___x_1761_);
                    v___x_1763_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg___closed__13);
                    v___x_1764_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1764_, 0, v___x_1762_);
                    lean_ctor_set(v___x_1764_, 1, v___x_1763_);
                    v___x_1765_ = l_Lean_MessageData_note(v___x_1764_);
                    v___x_1766_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1766_, 0, v_msg_1709_);
                    lean_ctor_set(v___x_1766_, 1, v___x_1765_);
                    if v_isShared_1738_ == 0 {
                        lean_ctor_set_tag(v___x_1737_, 0);
                        lean_ctor_set(v___x_1737_, 0, v___x_1766_);
                        v___x_1768_ = v___x_1737_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
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
    mut v_msg_1772_: *mut LeanObject,
    mut v_declHint_1773_: *mut LeanObject,
    mut v___y_1774_: *mut LeanObject,
    mut v___y_1775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1776_: *mut LeanObject = core::ptr::null_mut();
    v_res_1776_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg(v_msg_1772_, v_declHint_1773_, v___y_1774_);
    lean_dec(v___y_1774_);
    return v_res_1776_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7(
    mut v_msg_1777_: *mut LeanObject,
    mut v_declHint_1778_: *mut LeanObject,
    mut v___y_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1786_: u8 = 0;
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1782_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg(v_msg_1777_, v_declHint_1778_, v___y_1780_);
                v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
                v_isSharedCheck_1792_ = (!lean_is_exclusive(v___x_1782_)) as u8;
                if v_isSharedCheck_1792_ == 0 {
                    v___x_1785_ = v___x_1782_;
                    v_isShared_1786_ = v_isSharedCheck_1792_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1783_);
                    lean_dec(v___x_1782_);
                    v___x_1785_ = lean_box(0);
                    v_isShared_1786_ = v_isSharedCheck_1792_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1787_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1788_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1788_, 0, v___x_1787_);
                lean_ctor_set(v___x_1788_, 1, v_a_1783_);
                if v_isShared_1786_ == 0 {
                    lean_ctor_set(v___x_1785_, 0, v___x_1788_);
                    v___x_1790_ = v___x_1785_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
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
    mut v_msg_1793_: *mut LeanObject,
    mut v_declHint_1794_: *mut LeanObject,
    mut v___y_1795_: *mut LeanObject,
    mut v___y_1796_: *mut LeanObject,
    mut v___y_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1798_: *mut LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7(v_msg_1793_, v_declHint_1794_, v___y_1795_, v___y_1796_);
    lean_dec(v___y_1796_);
    lean_dec_ref(v___y_1795_);
    return v_res_1798_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6___redArg(
    mut v_ref_1799_: *mut LeanObject,
    mut v_msg_1800_: *mut LeanObject,
    mut v_declHint_1801_: *mut LeanObject,
    mut v___y_1802_: *mut LeanObject,
    mut v___y_1803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    v___x_1805_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7(v_msg_1800_, v_declHint_1801_, v___y_1802_, v___y_1803_);
    v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
    lean_inc(v_a_1806_);
    lean_dec_ref(v___x_1805_);
    v___x_1807_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8___redArg(v_ref_1799_, v_a_1806_, v___y_1802_, v___y_1803_);
    return v___x_1807_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6___redArg___boxed(
    mut v_ref_1808_: *mut LeanObject,
    mut v_msg_1809_: *mut LeanObject,
    mut v_declHint_1810_: *mut LeanObject,
    mut v___y_1811_: *mut LeanObject,
    mut v___y_1812_: *mut LeanObject,
    mut v___y_1813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1814_: *mut LeanObject = core::ptr::null_mut();
    v_res_1814_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1808_, v_msg_1809_, v_declHint_1810_, v___y_1811_, v___y_1812_);
    lean_dec(v___y_1812_);
    lean_dec_ref(v___y_1811_);
    lean_dec(v_ref_1808_);
    return v_res_1814_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    v___x_1816_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1817_ = l_Lean_stringToMessageData(v___x_1816_);
    return v___x_1817_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    v___x_1819_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1820_ = l_Lean_stringToMessageData(v___x_1819_);
    return v___x_1820_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1821_: *mut LeanObject,
    mut v_constName_1822_: *mut LeanObject,
    mut v___y_1823_: *mut LeanObject,
    mut v___y_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: u8 = 0;
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    v___x_1826_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1827_ = 0;
    lean_inc(v_constName_1822_);
    v___x_1828_ = l_Lean_MessageData_ofConstName(v_constName_1822_, v___x_1827_);
    v___x_1829_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1829_, 0, v___x_1826_);
    lean_ctor_set(v___x_1829_, 1, v___x_1828_);
    v___x_1830_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1831_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1831_, 0, v___x_1829_);
    lean_ctor_set(v___x_1831_, 1, v___x_1830_);
    v___x_1832_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1821_, v___x_1831_, v_constName_1822_, v___y_1823_, v___y_1824_);
    return v___x_1832_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1833_: *mut LeanObject,
    mut v_constName_1834_: *mut LeanObject,
    mut v___y_1835_: *mut LeanObject,
    mut v___y_1836_: *mut LeanObject,
    mut v___y_1837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1838_: *mut LeanObject = core::ptr::null_mut();
    v_res_1838_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg(v_ref_1833_, v_constName_1834_, v___y_1835_, v___y_1836_);
    lean_dec(v___y_1836_);
    lean_dec_ref(v___y_1835_);
    lean_dec(v_ref_1833_);
    return v_res_1838_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0___redArg(
    mut v_constName_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1843_ = lean_ctor_get(v___y_1840_, 5);
    v___x_1844_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg(v_ref_1843_, v_constName_1839_, v___y_1840_, v___y_1841_);
    return v___x_1844_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0___redArg___boxed(
    mut v_constName_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1849_: *mut LeanObject = core::ptr::null_mut();
    v_res_1849_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0___redArg(v_constName_1845_, v___y_1846_, v___y_1847_);
    lean_dec(v___y_1847_);
    lean_dec_ref(v___y_1846_);
    return v_res_1849_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0(
    mut v_constName_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
    mut v___y_1852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1854_ = lean_st_ref_get(v___y_1852_);
                v_env_1855_ = lean_ctor_get(v___x_1854_, 0);
                lean_inc_ref(v_env_1855_);
                lean_dec(v___x_1854_);
                v___x_1856_ = 0;
                lean_inc(v_constName_1850_);
                v___x_1857_ =
                    l_Lean_Environment_find_x3f(v_env_1855_, v_constName_1850_, v___x_1856_);
                if lean_obj_tag(v___x_1857_) == 0 {
                    v___x_1858_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0___redArg(v_constName_1850_, v___y_1851_, v___y_1852_);
                    return v___x_1858_;
                } else {
                    lean_dec(v_constName_1850_);
                    v_val_1859_ = lean_ctor_get(v___x_1857_, 0);
                    v_isSharedCheck_1866_ = (!lean_is_exclusive(v___x_1857_)) as u8;
                    if v_isSharedCheck_1866_ == 0 {
                        v___x_1861_ = v___x_1857_;
                        v_isShared_1862_ = v_isSharedCheck_1866_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1859_);
                        lean_dec(v___x_1857_);
                        v___x_1861_ = lean_box(0);
                        v_isShared_1862_ = v_isSharedCheck_1866_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1862_ == 0 {
                    lean_ctor_set_tag(v___x_1861_, 0);
                    v___x_1864_ = v___x_1861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_val_1859_);
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
    mut v_constName_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
    mut v___y_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1871_: *mut LeanObject = core::ptr::null_mut();
    v_res_1871_ = l_Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0(
        v_constName_1867_,
        v___y_1868_,
        v___y_1869_,
    );
    lean_dec(v___y_1869_);
    lean_dec_ref(v___y_1868_);
    return v_res_1871_;
}
pub unsafe fn _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    v___x_1873_ = l_Lean_registerInitAttrUnsafe___lam__0___closed__0;
    v___x_1874_ = l_Lean_stringToMessageData(v___x_1873_);
    return v___x_1874_;
}
pub unsafe fn _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    v___x_1876_ = l_Lean_registerInitAttrUnsafe___lam__0___closed__2;
    v___x_1877_ = l_Lean_stringToMessageData(v___x_1876_);
    return v___x_1877_;
}
pub unsafe fn _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__5() -> *mut LeanObject {
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    v___x_1879_ = l_Lean_registerInitAttrUnsafe___lam__0___closed__4;
    v___x_1880_ = l_Lean_stringToMessageData(v___x_1879_);
    return v___x_1880_;
}
pub unsafe fn _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__7() -> *mut LeanObject {
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    v___x_1882_ = l_Lean_registerInitAttrUnsafe___lam__0___closed__6;
    v___x_1883_ = l_Lean_stringToMessageData(v___x_1882_);
    return v___x_1883_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__0(
    mut v_declName_1884_: *mut LeanObject,
    mut v_stx_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
    mut v___y_1887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1933_: u8 = 0;
    let mut v_a_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1941_: u8 = 0;
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut v_a_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1946_: u8 = 0;
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1950_: u8 = 0;
    let mut v_a_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1954_: u8 = 0;
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1957_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_1889_) == 0 {
                    v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
                    lean_inc(v_a_1890_);
                    lean_dec_ref_known(v___x_1889_, 1);
                    v___x_1891_ = l_Lean_Attribute_Builtin_getIdent_x3f(
                        v_stx_1885_,
                        v___y_1886_,
                        v___y_1887_,
                    );
                    if lean_obj_tag(v___x_1891_) == 0 {
                        v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
                        v_isSharedCheck_1942_ = (!lean_is_exclusive(v___x_1891_)) as u8;
                        if v_isSharedCheck_1942_ == 0 {
                            v___x_1894_ = v___x_1891_;
                            v_isShared_1895_ = v_isSharedCheck_1942_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1892_);
                            lean_dec(v___x_1891_);
                            v___x_1894_ = lean_box(0);
                            v_isShared_1895_ = v_isSharedCheck_1942_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1890_);
                        v_a_1943_ = lean_ctor_get(v___x_1891_, 0);
                        v_isSharedCheck_1950_ = (!lean_is_exclusive(v___x_1891_)) as u8;
                        if v_isSharedCheck_1950_ == 0 {
                            v___x_1945_ = v___x_1891_;
                            v_isShared_1946_ = v_isSharedCheck_1950_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1943_);
                            lean_dec(v___x_1891_);
                            v___x_1945_ = lean_box(0);
                            v_isShared_1946_ = v_isSharedCheck_1950_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_stx_1885_);
                    v_a_1951_ = lean_ctor_get(v___x_1889_, 0);
                    v_isSharedCheck_1958_ = (!lean_is_exclusive(v___x_1889_)) as u8;
                    if v_isSharedCheck_1958_ == 0 {
                        v___x_1953_ = v___x_1889_;
                        v_isShared_1954_ = v_isSharedCheck_1958_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1951_);
                        lean_dec(v___x_1889_);
                        v___x_1953_ = lean_box(0);
                        v_isShared_1954_ = v_isSharedCheck_1958_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1892_) == 0 {
                    v___x_1896_ = l_Lean_ConstantInfo_type(v_a_1890_);
                    lean_dec(v_a_1890_);
                    v___x_1897_ = l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit(v___x_1896_);
                    lean_dec_ref(v___x_1896_);
                    if v___x_1897_ == 0 {
                        lean_del_object(v___x_1894_);
                        v___x_1898_ = lean_obj_once(
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
                        v___x_1900_ = lean_box(0);
                        if v_isShared_1895_ == 0 {
                            lean_ctor_set(v___x_1894_, 0, v___x_1900_);
                            v___x_1902_ = v___x_1894_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
                            v___x_1902_ = v_reuseFailAlloc_1903_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1894_);
                    v_val_1904_ = lean_ctor_get(v_a_1892_, 0);
                    lean_inc(v_val_1904_);
                    lean_dec_ref_known(v_a_1892_, 1);
                    v___x_1905_ = lean_box(0);
                    v___x_1906_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                        v_val_1904_,
                        v___x_1905_,
                        v___y_1886_,
                        v___y_1887_,
                    );
                    if lean_obj_tag(v___x_1906_) == 0 {
                        v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
                        lean_inc_n(v_a_1907_, 2);
                        lean_dec_ref_known(v___x_1906_, 1);
                        v___x_1908_ =
                            l_Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0(
                                v_a_1907_,
                                v___y_1886_,
                                v___y_1887_,
                            );
                        if lean_obj_tag(v___x_1908_) == 0 {
                            v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
                            v_isSharedCheck_1933_ = (!lean_is_exclusive(v___x_1908_)) as u8;
                            if v_isSharedCheck_1933_ == 0 {
                                v___x_1911_ = v___x_1908_;
                                v_isShared_1912_ = v_isSharedCheck_1933_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1909_);
                                lean_dec(v___x_1908_);
                                v___x_1911_ = lean_box(0);
                                v_isShared_1912_ = v_isSharedCheck_1933_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1907_);
                            lean_dec(v_a_1890_);
                            v_a_1934_ = lean_ctor_get(v___x_1908_, 0);
                            v_isSharedCheck_1941_ = (!lean_is_exclusive(v___x_1908_)) as u8;
                            if v_isSharedCheck_1941_ == 0 {
                                v___x_1936_ = v___x_1908_;
                                v_isShared_1937_ = v_isSharedCheck_1941_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1934_);
                                lean_dec(v___x_1908_);
                                v___x_1936_ = lean_box(0);
                                v_isShared_1937_ = v_isSharedCheck_1941_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1890_);
                        return v___x_1906_;
                    }
                }
            }
            2 => {
                return v___x_1902_;
            }
            3 => {
                v___x_1913_ = l_Lean_ConstantInfo_type(v_a_1909_);
                lean_dec(v_a_1909_);
                v___x_1914_ = l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(v___x_1913_);
                lean_dec_ref(v___x_1913_);
                if lean_obj_tag(v___x_1914_) == 0 {
                    lean_del_object(v___x_1911_);
                    lean_dec(v_a_1890_);
                    v___x_1915_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_registerInitAttrUnsafe___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_registerInitAttrUnsafe___lam__0___closed__3_once
                        ),
                        _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__3,
                    );
                    v___x_1916_ = l_Lean_MessageData_ofName(v_a_1907_);
                    v___x_1917_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1917_, 0, v___x_1915_);
                    lean_ctor_set(v___x_1917_, 1, v___x_1916_);
                    v___x_1918_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_registerInitAttrUnsafe___lam__0___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_registerInitAttrUnsafe___lam__0___closed__5_once
                        ),
                        _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__5,
                    );
                    v___x_1919_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1919_, 0, v___x_1917_);
                    lean_ctor_set(v___x_1919_, 1, v___x_1918_);
                    v___x_1920_ =
                        l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
                            v___x_1919_,
                            v___y_1886_,
                            v___y_1887_,
                        );
                    return v___x_1920_;
                } else {
                    v_val_1921_ = lean_ctor_get(v___x_1914_, 0);
                    lean_inc(v_val_1921_);
                    lean_dec_ref_known(v___x_1914_, 1);
                    v___x_1922_ = l_Lean_ConstantInfo_type(v_a_1890_);
                    lean_dec(v_a_1890_);
                    v___x_1923_ = lean_expr_eqv(v___x_1922_, v_val_1921_);
                    lean_dec(v_val_1921_);
                    lean_dec_ref(v___x_1922_);
                    if v___x_1923_ == 0 {
                        lean_del_object(v___x_1911_);
                        v___x_1924_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_registerInitAttrUnsafe___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_registerInitAttrUnsafe___lam__0___closed__3_once
                            ),
                            _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__3,
                        );
                        v___x_1925_ = l_Lean_MessageData_ofName(v_a_1907_);
                        v___x_1926_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1926_, 0, v___x_1924_);
                        lean_ctor_set(v___x_1926_, 1, v___x_1925_);
                        v___x_1927_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_registerInitAttrUnsafe___lam__0___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_registerInitAttrUnsafe___lam__0___closed__7_once
                            ),
                            _init_l_Lean_registerInitAttrUnsafe___lam__0___closed__7,
                        );
                        v___x_1928_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1928_, 0, v___x_1926_);
                        lean_ctor_set(v___x_1928_, 1, v___x_1927_);
                        v___x_1929_ =
                            l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
                                v___x_1928_,
                                v___y_1886_,
                                v___y_1887_,
                            );
                        return v___x_1929_;
                    } else {
                        if v_isShared_1912_ == 0 {
                            lean_ctor_set(v___x_1911_, 0, v_a_1907_);
                            v___x_1931_ = v___x_1911_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1907_);
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
                    v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
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
                    v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
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
                    v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
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
    mut v_declName_1959_: *mut LeanObject,
    mut v_stx_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
    mut v___y_1962_: *mut LeanObject,
    mut v___y_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1964_: *mut LeanObject = core::ptr::null_mut();
    v_res_1964_ = l_Lean_registerInitAttrUnsafe___lam__0(
        v_declName_1959_,
        v_stx_1960_,
        v___y_1961_,
        v___y_1962_,
    );
    lean_dec(v___y_1962_);
    lean_dec_ref(v___y_1961_);
    return v_res_1964_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___lam__0(
    mut v___y_1965_: *mut LeanObject,
    mut v_isExporting_1966_: u8,
    mut v___x_1967_: *mut LeanObject,
    mut v_a_x3f_1968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut v_unused_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1970_ = lean_st_ref_take(v___y_1965_);
                v_env_1971_ = lean_ctor_get(v___x_1970_, 0);
                v_nextMacroScope_1972_ = lean_ctor_get(v___x_1970_, 1);
                v_ngen_1973_ = lean_ctor_get(v___x_1970_, 2);
                v_auxDeclNGen_1974_ = lean_ctor_get(v___x_1970_, 3);
                v_traceState_1975_ = lean_ctor_get(v___x_1970_, 4);
                v_messages_1976_ = lean_ctor_get(v___x_1970_, 6);
                v_infoState_1977_ = lean_ctor_get(v___x_1970_, 7);
                v_snapshotTasks_1978_ = lean_ctor_get(v___x_1970_, 8);
                v_isSharedCheck_1989_ = (!lean_is_exclusive(v___x_1970_)) as u8;
                if v_isSharedCheck_1989_ == 0 {
                    v_unused_1990_ = lean_ctor_get(v___x_1970_, 5);
                    lean_dec(v_unused_1990_);
                    v___x_1980_ = v___x_1970_;
                    v_isShared_1981_ = v_isSharedCheck_1989_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1978_);
                    lean_inc(v_infoState_1977_);
                    lean_inc(v_messages_1976_);
                    lean_inc(v_traceState_1975_);
                    lean_inc(v_auxDeclNGen_1974_);
                    lean_inc(v_ngen_1973_);
                    lean_inc(v_nextMacroScope_1972_);
                    lean_inc(v_env_1971_);
                    lean_dec(v___x_1970_);
                    v___x_1980_ = lean_box(0);
                    v_isShared_1981_ = v_isSharedCheck_1989_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1982_ = l_Lean_Environment_setExporting(v_env_1971_, v_isExporting_1966_);
                if v_isShared_1981_ == 0 {
                    lean_ctor_set(v___x_1980_, 5, v___x_1967_);
                    lean_ctor_set(v___x_1980_, 0, v___x_1982_);
                    v___x_1984_ = v___x_1980_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1982_);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_nextMacroScope_1972_);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_ngen_1973_);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 3, v_auxDeclNGen_1974_);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 4, v_traceState_1975_);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 5, v___x_1967_);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 6, v_messages_1976_);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 7, v_infoState_1977_);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 8, v_snapshotTasks_1978_);
                    v___x_1984_ = v_reuseFailAlloc_1988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1985_ = lean_st_ref_set(v___y_1965_, v___x_1984_);
                v___x_1986_ = lean_box(0);
                v___x_1987_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1987_, 0, v___x_1986_);
                return v___x_1987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___lam__0___boxed(
    mut v___y_1991_: *mut LeanObject,
    mut v_isExporting_1992_: *mut LeanObject,
    mut v___x_1993_: *mut LeanObject,
    mut v_a_x3f_1994_: *mut LeanObject,
    mut v___y_1995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_1996_: u8 = 0;
    let mut v_res_1997_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_1996_ = (lean_unbox(v_isExporting_1992_) as u8);
    v_res_1997_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___lam__0(v___y_1991_, v_isExporting_boxed_1996_, v___x_1993_, v_a_x3f_1994_);
    lean_dec(v_a_x3f_1994_);
    lean_dec(v___y_1991_);
    return v_res_1997_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    v___x_1998_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1998_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    v___x_1999_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__0);
    v___x_2000_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2000_, 0, v___x_1999_);
    return v___x_2000_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    v___x_2001_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__1);
    v___x_2002_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2002_, 0, v___x_2001_);
    lean_ctor_set(v___x_2002_, 1, v___x_2001_);
    return v___x_2002_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg(
    mut v_x_2003_: *mut LeanObject,
    mut v_isExporting_2004_: u8,
    mut v___y_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2010_: u8 = 0;
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2022_: u8 = 0;
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2042_: u8 = 0;
    let mut v_unused_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut v_a_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut v_unused_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_unused_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2008_ = lean_st_ref_get(v___y_2006_);
                v_env_2009_ = lean_ctor_get(v___x_2008_, 0);
                lean_inc_ref(v_env_2009_);
                lean_dec(v___x_2008_);
                v_isExporting_2010_ = lean_ctor_get_uint8(
                    v_env_2009_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_2009_);
                v___x_2011_ = lean_st_ref_take(v___y_2006_);
                v_env_2012_ = lean_ctor_get(v___x_2011_, 0);
                v_nextMacroScope_2013_ = lean_ctor_get(v___x_2011_, 1);
                v_ngen_2014_ = lean_ctor_get(v___x_2011_, 2);
                v_auxDeclNGen_2015_ = lean_ctor_get(v___x_2011_, 3);
                v_traceState_2016_ = lean_ctor_get(v___x_2011_, 4);
                v_messages_2017_ = lean_ctor_get(v___x_2011_, 6);
                v_infoState_2018_ = lean_ctor_get(v___x_2011_, 7);
                v_snapshotTasks_2019_ = lean_ctor_get(v___x_2011_, 8);
                v_isSharedCheck_2058_ = (!lean_is_exclusive(v___x_2011_)) as u8;
                if v_isSharedCheck_2058_ == 0 {
                    v_unused_2059_ = lean_ctor_get(v___x_2011_, 5);
                    lean_dec(v_unused_2059_);
                    v___x_2021_ = v___x_2011_;
                    v_isShared_2022_ = v_isSharedCheck_2058_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2019_);
                    lean_inc(v_infoState_2018_);
                    lean_inc(v_messages_2017_);
                    lean_inc(v_traceState_2016_);
                    lean_inc(v_auxDeclNGen_2015_);
                    lean_inc(v_ngen_2014_);
                    lean_inc(v_nextMacroScope_2013_);
                    lean_inc(v_env_2012_);
                    lean_dec(v___x_2011_);
                    v___x_2021_ = lean_box(0);
                    v_isShared_2022_ = v_isSharedCheck_2058_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2023_ = l_Lean_Environment_setExporting(v_env_2012_, v_isExporting_2004_);
                v___x_2024_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2);
                if v_isShared_2022_ == 0 {
                    lean_ctor_set(v___x_2021_, 5, v___x_2024_);
                    lean_ctor_set(v___x_2021_, 0, v___x_2023_);
                    v___x_2026_ = v___x_2021_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2023_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_nextMacroScope_2013_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_ngen_2014_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 3, v_auxDeclNGen_2015_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 4, v_traceState_2016_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 5, v___x_2024_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 6, v_messages_2017_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 7, v_infoState_2018_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 8, v_snapshotTasks_2019_);
                    v___x_2026_ = v_reuseFailAlloc_2057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2027_ = lean_st_ref_set(v___y_2006_, v___x_2026_);
                lean_inc(v___y_2006_);
                lean_inc_ref(v___y_2005_);
                v_r_2028_ = lean_apply_3(v_x_2003_, v___y_2005_, v___y_2006_, lean_box(0));
                if lean_obj_tag(v_r_2028_) == 0 {
                    v_a_2029_ = lean_ctor_get(v_r_2028_, 0);
                    v_isSharedCheck_2045_ = (!lean_is_exclusive(v_r_2028_)) as u8;
                    if v_isSharedCheck_2045_ == 0 {
                        v___x_2031_ = v_r_2028_;
                        v_isShared_2032_ = v_isSharedCheck_2045_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2029_);
                        lean_dec(v_r_2028_);
                        v___x_2031_ = lean_box(0);
                        v_isShared_2032_ = v_isSharedCheck_2045_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2046_ = lean_ctor_get(v_r_2028_, 0);
                    lean_inc(v_a_2046_);
                    lean_dec_ref_known(v_r_2028_, 1);
                    v___x_2047_ = lean_box(0);
                    v___x_2048_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___lam__0(v___y_2006_, v_isExporting_2010_, v___x_2024_, v___x_2047_);
                    v_isSharedCheck_2055_ = (!lean_is_exclusive(v___x_2048_)) as u8;
                    if v_isSharedCheck_2055_ == 0 {
                        v_unused_2056_ = lean_ctor_get(v___x_2048_, 0);
                        lean_dec(v_unused_2056_);
                        v___x_2050_ = v___x_2048_;
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_2048_);
                        v___x_2050_ = lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v_a_2029_);
                if v_isShared_2032_ == 0 {
                    lean_ctor_set_tag(v___x_2031_, 1);
                    v___x_2034_ = v___x_2031_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2029_);
                    v___x_2034_ = v_reuseFailAlloc_2044_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2035_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___lam__0(v___y_2006_, v_isExporting_2010_, v___x_2024_, v___x_2034_);
                lean_dec_ref(v___x_2034_);
                v_isSharedCheck_2042_ = (!lean_is_exclusive(v___x_2035_)) as u8;
                if v_isSharedCheck_2042_ == 0 {
                    v_unused_2043_ = lean_ctor_get(v___x_2035_, 0);
                    lean_dec(v_unused_2043_);
                    v___x_2037_ = v___x_2035_;
                    v_isShared_2038_ = v_isSharedCheck_2042_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___x_2035_);
                    v___x_2037_ = lean_box(0);
                    v_isShared_2038_ = v_isSharedCheck_2042_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2038_ == 0 {
                    lean_ctor_set(v___x_2037_, 0, v_a_2029_);
                    v___x_2040_ = v___x_2037_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2029_);
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
                    lean_ctor_set_tag(v___x_2050_, 1);
                    lean_ctor_set(v___x_2050_, 0, v_a_2046_);
                    v___x_2053_ = v___x_2050_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2046_);
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
    mut v_x_2060_: *mut LeanObject,
    mut v_isExporting_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
    mut v___y_2063_: *mut LeanObject,
    mut v___y_2064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_2065_: u8 = 0;
    let mut v_res_2066_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2065_ = (lean_unbox(v_isExporting_2061_) as u8);
    v_res_2066_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg(v_x_2060_, v_isExporting_boxed_2065_, v___y_2062_, v___y_2063_);
    lean_dec(v___y_2063_);
    lean_dec_ref(v___y_2062_);
    return v_res_2066_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2___redArg(
    mut v_x_2067_: *mut LeanObject,
    mut v_when_2068_: u8,
    mut v___y_2069_: *mut LeanObject,
    mut v___y_2070_: *mut LeanObject,
) -> *mut LeanObject {
    if v_when_2068_ == 0 {
        let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___y_2070_);
        lean_inc_ref(v___y_2069_);
        v___x_2072_ = lean_apply_3(v_x_2067_, v___y_2069_, v___y_2070_, lean_box(0));
        return v___x_2072_;
    } else {
        let mut v___x_2073_: u8 = 0;
        let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
        v___x_2073_ = 0;
        v___x_2074_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg(v_x_2067_, v___x_2073_, v___y_2069_, v___y_2070_);
        return v___x_2074_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2___redArg___boxed(
    mut v_x_2075_: *mut LeanObject,
    mut v_when_2076_: *mut LeanObject,
    mut v___y_2077_: *mut LeanObject,
    mut v___y_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_2080_: u8 = 0;
    let mut v_res_2081_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_2080_ = (lean_unbox(v_when_2076_) as u8);
    v_res_2081_ = l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2___redArg(
        v_x_2075_,
        v_when_boxed_2080_,
        v___y_2077_,
        v___y_2078_,
    );
    lean_dec(v___y_2078_);
    lean_dec_ref(v___y_2077_);
    return v_res_2081_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__1(
    mut v_declName_2082_: *mut LeanObject,
    mut v_stx_2083_: *mut LeanObject,
    mut v___y_2084_: *mut LeanObject,
    mut v___y_2085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: u8 = 0;
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    v___f_2087_ = lean_alloc_closure(
        l_Lean_registerInitAttrUnsafe___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2087_, 0, v_declName_2082_);
    lean_closure_set(v___f_2087_, 1, v_stx_2083_);
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
    mut v_declName_2090_: *mut LeanObject,
    mut v_stx_2091_: *mut LeanObject,
    mut v___y_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2095_: *mut LeanObject = core::ptr::null_mut();
    v_res_2095_ = l_Lean_registerInitAttrUnsafe___lam__1(
        v_declName_2090_,
        v_stx_2091_,
        v___y_2092_,
        v___y_2093_,
    );
    lean_dec(v___y_2093_);
    lean_dec_ref(v___y_2092_);
    return v_res_2095_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__2(
    mut v_x_2096_: *mut LeanObject,
    mut v_x_2097_: *mut LeanObject,
    mut v_x_2098_: *mut LeanObject,
    mut v___y_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    v___x_2101_ = lean_box(0);
    v___x_2102_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2102_, 0, v___x_2101_);
    return v___x_2102_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__2___boxed(
    mut v_x_2103_: *mut LeanObject,
    mut v_x_2104_: *mut LeanObject,
    mut v_x_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
    mut v___y_2107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2108_: *mut LeanObject = core::ptr::null_mut();
    v_res_2108_ =
        l_Lean_registerInitAttrUnsafe___lam__2(v_x_2103_, v_x_2104_, v_x_2105_, v___y_2106_);
    lean_dec(v___y_2106_);
    lean_dec_ref(v_x_2105_);
    lean_dec(v_x_2104_);
    lean_dec(v_x_2103_);
    return v_res_2108_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__3(
    mut v_runAfterImport_2109_: u8,
    mut v___x_2110_: u8,
    mut v_env_2111_: *mut LeanObject,
    mut v_declName_2112_: *mut LeanObject,
    mut v_x_2113_: *mut LeanObject,
) -> u8 {
    if v_runAfterImport_2109_ == 0 {
        lean_dec(v_declName_2112_);
        lean_dec_ref(v_env_2111_);
        return v___x_2110_;
    } else {
        let mut v___x_2114_: u8 = 0;
        v___x_2114_ = l_Lean_isMarkedMeta(v_env_2111_, v_declName_2112_);
        return v___x_2114_;
    }
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___lam__3___boxed(
    mut v_runAfterImport_2115_: *mut LeanObject,
    mut v___x_2116_: *mut LeanObject,
    mut v_env_2117_: *mut LeanObject,
    mut v_declName_2118_: *mut LeanObject,
    mut v_x_2119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_runAfterImport_boxed_2120_: u8 = 0;
    let mut v___x_5418__boxed_2121_: u8 = 0;
    let mut v_res_2122_: u8 = 0;
    let mut v_r_2123_: *mut LeanObject = core::ptr::null_mut();
    v_runAfterImport_boxed_2120_ = (lean_unbox(v_runAfterImport_2115_) as u8);
    v___x_5418__boxed_2121_ = (lean_unbox(v___x_2116_) as u8);
    v_res_2122_ = l_Lean_registerInitAttrUnsafe___lam__3(
        v_runAfterImport_boxed_2120_,
        v___x_5418__boxed_2121_,
        v_env_2117_,
        v_declName_2118_,
        v_x_2119_,
    );
    lean_dec(v_x_2119_);
    v_r_2123_ = lean_box((v_res_2122_) as usize);
    return v_r_2123_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe(
    mut v_attrName_2127_: *mut LeanObject,
    mut v_runAfterImport_2128_: u8,
    mut v_ref_2129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: u8 = 0;
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    v___f_2131_ = l_Lean_registerInitAttrUnsafe___closed__0;
    v___f_2132_ = l_Lean_registerInitAttrUnsafe___closed__1;
    v___x_2133_ = l_Lean_registerInitAttrUnsafe___closed__2;
    v___x_2134_ = 0;
    v___x_2135_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_2135_, 0, v_ref_2129_);
    lean_ctor_set(v___x_2135_, 1, v_attrName_2127_);
    lean_ctor_set(v___x_2135_, 2, v___x_2133_);
    lean_ctor_set_uint8(
        v___x_2135_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2134_,
    );
    v___x_2136_ = 1;
    v___x_2137_ = lean_box((v_runAfterImport_2128_) as usize);
    v___x_2138_ = lean_box((v___x_2136_) as usize);
    v___f_2139_ = lean_alloc_closure(
        l_Lean_registerInitAttrUnsafe___lam__3___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2139_, 0, v___x_2137_);
    lean_closure_set(v___f_2139_, 1, v___x_2138_);
    v___x_2140_ = lean_alloc_ctor(0, 4, (1) as u32);
    lean_ctor_set(v___x_2140_, 0, v___x_2135_);
    lean_ctor_set(v___x_2140_, 1, v___f_2131_);
    lean_ctor_set(v___x_2140_, 2, v___f_2132_);
    lean_ctor_set(v___x_2140_, 3, v___f_2139_);
    lean_ctor_set_uint8(
        v___x_2140_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_2136_,
    );
    v___x_2141_ = l_Lean_registerParametricAttribute___redArg(v___x_2140_);
    return v___x_2141_;
}
pub unsafe fn l_Lean_registerInitAttrUnsafe___boxed(
    mut v_attrName_2142_: *mut LeanObject,
    mut v_runAfterImport_2143_: *mut LeanObject,
    mut v_ref_2144_: *mut LeanObject,
    mut v_a_2145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_runAfterImport_boxed_2146_: u8 = 0;
    let mut v_res_2147_: *mut LeanObject = core::ptr::null_mut();
    v_runAfterImport_boxed_2146_ = (lean_unbox(v_runAfterImport_2143_) as u8);
    v_res_2147_ =
        l_Lean_registerInitAttrUnsafe(v_attrName_2142_, v_runAfterImport_boxed_2146_, v_ref_2144_);
    return v_res_2147_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1(
    mut v_00_u03b1_2148_: *mut LeanObject,
    mut v_msg_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    v___x_2153_ = l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___redArg(
        v_msg_2149_,
        v___y_2150_,
        v___y_2151_,
    );
    return v___x_2153_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1___boxed(
    mut v_00_u03b1_2154_: *mut LeanObject,
    mut v_msg_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2159_: *mut LeanObject = core::ptr::null_mut();
    v_res_2159_ = l_Lean_throwError___at___00Lean_registerInitAttrUnsafe_spec__1(
        v_00_u03b1_2154_,
        v_msg_2155_,
        v___y_2156_,
        v___y_2157_,
    );
    lean_dec(v___y_2157_);
    lean_dec_ref(v___y_2156_);
    return v_res_2159_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4(
    mut v_00_u03b1_2160_: *mut LeanObject,
    mut v_x_2161_: *mut LeanObject,
    mut v_isExporting_2162_: u8,
    mut v___y_2163_: *mut LeanObject,
    mut v___y_2164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    v___x_2166_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg(v_x_2161_, v_isExporting_2162_, v___y_2163_, v___y_2164_);
    return v___x_2166_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___boxed(
    mut v_00_u03b1_2167_: *mut LeanObject,
    mut v_x_2168_: *mut LeanObject,
    mut v_isExporting_2169_: *mut LeanObject,
    mut v___y_2170_: *mut LeanObject,
    mut v___y_2171_: *mut LeanObject,
    mut v___y_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_2173_: u8 = 0;
    let mut v_res_2174_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2173_ = (lean_unbox(v_isExporting_2169_) as u8);
    v_res_2174_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4(v_00_u03b1_2167_, v_x_2168_, v_isExporting_boxed_2173_, v___y_2170_, v___y_2171_);
    lean_dec(v___y_2171_);
    lean_dec_ref(v___y_2170_);
    return v_res_2174_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2(
    mut v_00_u03b1_2175_: *mut LeanObject,
    mut v_x_2176_: *mut LeanObject,
    mut v_when_2177_: u8,
    mut v___y_2178_: *mut LeanObject,
    mut v___y_2179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    v___x_2181_ = l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2___redArg(
        v_x_2176_,
        v_when_2177_,
        v___y_2178_,
        v___y_2179_,
    );
    return v___x_2181_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2___boxed(
    mut v_00_u03b1_2182_: *mut LeanObject,
    mut v_x_2183_: *mut LeanObject,
    mut v_when_2184_: *mut LeanObject,
    mut v___y_2185_: *mut LeanObject,
    mut v___y_2186_: *mut LeanObject,
    mut v___y_2187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_2188_: u8 = 0;
    let mut v_res_2189_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_2188_ = (lean_unbox(v_when_2184_) as u8);
    v_res_2189_ = l_Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2(
        v_00_u03b1_2182_,
        v_x_2183_,
        v_when_boxed_2188_,
        v___y_2185_,
        v___y_2186_,
    );
    lean_dec(v___y_2186_);
    lean_dec_ref(v___y_2185_);
    return v_res_2189_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0(
    mut v_00_u03b1_2190_: *mut LeanObject,
    mut v_constName_2191_: *mut LeanObject,
    mut v___y_2192_: *mut LeanObject,
    mut v___y_2193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    v___x_2195_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0___redArg(v_constName_2191_, v___y_2192_, v___y_2193_);
    return v___x_2195_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0___boxed(
    mut v_00_u03b1_2196_: *mut LeanObject,
    mut v_constName_2197_: *mut LeanObject,
    mut v___y_2198_: *mut LeanObject,
    mut v___y_2199_: *mut LeanObject,
    mut v___y_2200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2201_: *mut LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0(v_00_u03b1_2196_, v_constName_2197_, v___y_2198_, v___y_2199_);
    lean_dec(v___y_2199_);
    lean_dec_ref(v___y_2198_);
    return v_res_2201_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2202_: *mut LeanObject,
    mut v_ref_2203_: *mut LeanObject,
    mut v_constName_2204_: *mut LeanObject,
    mut v___y_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    v___x_2208_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___redArg(v_ref_2203_, v_constName_2204_, v___y_2205_, v___y_2206_);
    return v___x_2208_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2209_: *mut LeanObject,
    mut v_ref_2210_: *mut LeanObject,
    mut v_constName_2211_: *mut LeanObject,
    mut v___y_2212_: *mut LeanObject,
    mut v___y_2213_: *mut LeanObject,
    mut v___y_2214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2215_: *mut LeanObject = core::ptr::null_mut();
    v_res_2215_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_2209_, v_ref_2210_, v_constName_2211_, v___y_2212_, v___y_2213_);
    lean_dec(v___y_2213_);
    lean_dec_ref(v___y_2212_);
    lean_dec(v_ref_2210_);
    return v_res_2215_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6(
    mut v_00_u03b1_2216_: *mut LeanObject,
    mut v_ref_2217_: *mut LeanObject,
    mut v_msg_2218_: *mut LeanObject,
    mut v_declHint_2219_: *mut LeanObject,
    mut v___y_2220_: *mut LeanObject,
    mut v___y_2221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    v___x_2223_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_2217_, v_msg_2218_, v_declHint_2219_, v___y_2220_, v___y_2221_);
    return v___x_2223_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6___boxed(
    mut v_00_u03b1_2224_: *mut LeanObject,
    mut v_ref_2225_: *mut LeanObject,
    mut v_msg_2226_: *mut LeanObject,
    mut v_declHint_2227_: *mut LeanObject,
    mut v___y_2228_: *mut LeanObject,
    mut v___y_2229_: *mut LeanObject,
    mut v___y_2230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2231_: *mut LeanObject = core::ptr::null_mut();
    v_res_2231_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_2224_, v_ref_2225_, v_msg_2226_, v_declHint_2227_, v___y_2228_, v___y_2229_);
    lean_dec(v___y_2229_);
    lean_dec_ref(v___y_2228_);
    lean_dec(v_ref_2225_);
    return v_res_2231_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8(
    mut v_msg_2232_: *mut LeanObject,
    mut v_declHint_2233_: *mut LeanObject,
    mut v___y_2234_: *mut LeanObject,
    mut v___y_2235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    v___x_2237_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___redArg(v_msg_2232_, v_declHint_2233_, v___y_2235_);
    return v___x_2237_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8___boxed(
    mut v_msg_2238_: *mut LeanObject,
    mut v_declHint_2239_: *mut LeanObject,
    mut v___y_2240_: *mut LeanObject,
    mut v___y_2241_: *mut LeanObject,
    mut v___y_2242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2243_: *mut LeanObject = core::ptr::null_mut();
    v_res_2243_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__7_spec__8(v_msg_2238_, v_declHint_2239_, v___y_2240_, v___y_2241_);
    lean_dec(v___y_2241_);
    lean_dec_ref(v___y_2240_);
    return v_res_2243_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8(
    mut v_00_u03b1_2244_: *mut LeanObject,
    mut v_ref_2245_: *mut LeanObject,
    mut v_msg_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    v___x_2250_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8___redArg(v_ref_2245_, v_msg_2246_, v___y_2247_, v___y_2248_);
    return v___x_2250_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8___boxed(
    mut v_00_u03b1_2251_: *mut LeanObject,
    mut v_ref_2252_: *mut LeanObject,
    mut v_msg_2253_: *mut LeanObject,
    mut v___y_2254_: *mut LeanObject,
    mut v___y_2255_: *mut LeanObject,
    mut v___y_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2257_: *mut LeanObject = core::ptr::null_mut();
    v_res_2257_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_registerInitAttrUnsafe_spec__0_spec__0_spec__1_spec__6_spec__8(v_00_u03b1_2251_, v_ref_2252_, v_msg_2253_, v___y_2254_, v___y_2255_);
    lean_dec(v___y_2255_);
    lean_dec_ref(v___y_2254_);
    lean_dec(v_ref_2252_);
    return v_res_2257_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    v___x_2284_ = l_Lean_registerInitAttr___auto__1___closed__10;
    v___x_2285_ = l_Lean_mkAtom(v___x_2284_);
    return v___x_2285_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    v___x_2286_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__12_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__12,
    );
    v___x_2287_ = l_Lean_registerInitAttr___auto__1___closed__5;
    v___x_2288_ = lean_array_push(v___x_2287_, v___x_2286_);
    return v___x_2288_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    v___x_2297_ = l_Lean_registerInitAttr___auto__1___closed__17;
    v___x_2298_ = l_Lean_mkAtom(v___x_2297_);
    return v___x_2298_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    v___x_2299_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__18_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__18,
    );
    v___x_2300_ = l_Lean_registerInitAttr___auto__1___closed__5;
    v___x_2301_ = lean_array_push(v___x_2300_, v___x_2299_);
    return v___x_2301_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    v___x_2302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__19_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__19,
    );
    v___x_2303_ = l_Lean_registerInitAttr___auto__1___closed__16;
    v___x_2304_ = lean_box(2);
    v___x_2305_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2305_, 0, v___x_2304_);
    lean_ctor_set(v___x_2305_, 1, v___x_2303_);
    lean_ctor_set(v___x_2305_, 2, v___x_2302_);
    return v___x_2305_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    v___x_2306_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__20_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__20,
    );
    v___x_2307_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__13_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__13,
    );
    v___x_2308_ = lean_array_push(v___x_2307_, v___x_2306_);
    return v___x_2308_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    v___x_2309_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__21_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__21,
    );
    v___x_2310_ = l_Lean_registerInitAttr___auto__1___closed__11;
    v___x_2311_ = lean_box(2);
    v___x_2312_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2312_, 0, v___x_2311_);
    lean_ctor_set(v___x_2312_, 1, v___x_2310_);
    lean_ctor_set(v___x_2312_, 2, v___x_2309_);
    return v___x_2312_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    v___x_2313_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__22_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__22,
    );
    v___x_2314_ = l_Lean_registerInitAttr___auto__1___closed__5;
    v___x_2315_ = lean_array_push(v___x_2314_, v___x_2313_);
    return v___x_2315_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    v___x_2316_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__23_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__23,
    );
    v___x_2317_ = l_Lean_registerInitAttr___auto__1___closed__9;
    v___x_2318_ = lean_box(2);
    v___x_2319_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2319_, 0, v___x_2318_);
    lean_ctor_set(v___x_2319_, 1, v___x_2317_);
    lean_ctor_set(v___x_2319_, 2, v___x_2316_);
    return v___x_2319_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    v___x_2320_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__24_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__24,
    );
    v___x_2321_ = l_Lean_registerInitAttr___auto__1___closed__5;
    v___x_2322_ = lean_array_push(v___x_2321_, v___x_2320_);
    return v___x_2322_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    v___x_2323_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__25_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__25,
    );
    v___x_2324_ = l_Lean_registerInitAttr___auto__1___closed__7;
    v___x_2325_ = lean_box(2);
    v___x_2326_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2326_, 0, v___x_2325_);
    lean_ctor_set(v___x_2326_, 1, v___x_2324_);
    lean_ctor_set(v___x_2326_, 2, v___x_2323_);
    return v___x_2326_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__27() -> *mut LeanObject {
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    v___x_2327_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__26_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__26,
    );
    v___x_2328_ = l_Lean_registerInitAttr___auto__1___closed__5;
    v___x_2329_ = lean_array_push(v___x_2328_, v___x_2327_);
    return v___x_2329_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    v___x_2330_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__27_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__27,
    );
    v___x_2331_ = l_Lean_registerInitAttr___auto__1___closed__4;
    v___x_2332_ = lean_box(2);
    v___x_2333_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2333_, 0, v___x_2332_);
    lean_ctor_set(v___x_2333_, 1, v___x_2331_);
    lean_ctor_set(v___x_2333_, 2, v___x_2330_);
    return v___x_2333_;
}
pub unsafe fn _init_l_Lean_registerInitAttr___auto__1() -> *mut LeanObject {
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    v___x_2334_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_registerInitAttr___auto__1___closed__28_once),
        _init_l_Lean_registerInitAttr___auto__1___closed__28,
    );
    return v___x_2334_;
}
pub unsafe fn l_Lean_registerInitAttr(
    mut v_attrName_2335_: *mut LeanObject,
    mut v_runAfterImport_2336_: u8,
    mut v_ref_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    v___x_2339_ =
        l_Lean_registerInitAttrUnsafe(v_attrName_2335_, v_runAfterImport_2336_, v_ref_2337_);
    return v___x_2339_;
}
pub unsafe fn l_Lean_registerInitAttr___boxed(
    mut v_attrName_2340_: *mut LeanObject,
    mut v_runAfterImport_2341_: *mut LeanObject,
    mut v_ref_2342_: *mut LeanObject,
    mut v_a_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_runAfterImport_boxed_2344_: u8 = 0;
    let mut v_res_2345_: *mut LeanObject = core::ptr::null_mut();
    v_runAfterImport_boxed_2344_ = (lean_unbox(v_runAfterImport_2341_) as u8);
    v_res_2345_ =
        l_Lean_registerInitAttr(v_attrName_2340_, v_runAfterImport_boxed_2344_, v_ref_2342_);
    return v_res_2345_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    v___x_2354_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_;
    v___x_2355_ = 1;
    v___x_2356_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_;
    v___x_2357_ = l_Lean_registerInitAttrUnsafe(v___x_2354_, v___x_2355_, v___x_2356_);
    return v___x_2357_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2____boxed(
    mut v_a_2358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2359_: *mut LeanObject = core::ptr::null_mut();
    v_res_2359_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_();
    return v_res_2359_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1()
-> *mut LeanObject {
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    v___x_2362_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_;
    v___x_2363_ = l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1___closed__0;
    v___x_2364_ = l_Lean_addBuiltinDocString(v___x_2362_, v___x_2363_);
    return v___x_2364_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1___boxed(
    mut v_a_2365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2366_: *mut LeanObject = core::ptr::null_mut();
    v_res_2366_ = l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1();
    return v_res_2366_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3()
-> *mut LeanObject {
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    v___x_2393_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_;
    v___x_2394_ = l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___closed__6;
    v___x_2395_ = l_Lean_addBuiltinDeclarationRanges(v___x_2393_, v___x_2394_);
    return v___x_2395_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3___boxed(
    mut v_a_2396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2397_: *mut LeanObject = core::ptr::null_mut();
    v_res_2397_ = l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3();
    return v_res_2397_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: u8 = 0;
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    v___x_2406_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_;
    v___x_2407_ = 0;
    v___x_2408_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_;
    v___x_2409_ = l_Lean_registerInitAttrUnsafe(v___x_2406_, v___x_2407_, v___x_2408_);
    return v___x_2409_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2____boxed(
    mut v_a_2410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2411_: *mut LeanObject = core::ptr::null_mut();
    v_res_2411_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_();
    return v_res_2411_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1()
-> *mut LeanObject {
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    v___x_2414_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_;
    v___x_2415_ = l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1___closed__0;
    v___x_2416_ = l_Lean_addBuiltinDocString(v___x_2414_, v___x_2415_);
    return v___x_2416_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1___boxed(
    mut v_a_2417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2418_: *mut LeanObject = core::ptr::null_mut();
    v_res_2418_ = l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1();
    return v_res_2418_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3()
-> *mut LeanObject {
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    v___x_2445_ = l___private_Lean_Compiler_InitAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_;
    v___x_2446_ = l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___closed__6;
    v___x_2447_ = l_Lean_addBuiltinDeclarationRanges(v___x_2445_, v___x_2446_);
    return v___x_2447_;
}
pub unsafe fn l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3___boxed(
    mut v_a_2448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2449_: *mut LeanObject = core::ptr::null_mut();
    v_res_2449_ = l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3();
    return v_res_2449_;
}
pub unsafe fn l_Lean_getInitFnNameForCore_x3f(
    mut v_env_2450_: *mut LeanObject,
    mut v_attr_2451_: *mut LeanObject,
    mut v_fn_2452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    v___x_2453_ = lean_box(0);
    v___x_2454_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
        v___x_2453_,
        v_attr_2451_,
        v_env_2450_,
        v_fn_2452_,
    );
    if lean_obj_tag(v___x_2454_) == 1 {
        let mut v_val_2455_: *mut LeanObject = core::ptr::null_mut();
        v_val_2455_ = lean_ctor_get(v___x_2454_, 0);
        lean_inc(v_val_2455_);
        if lean_obj_tag(v_val_2455_) == 0 {
            let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_2454_, 1);
            v___x_2456_ = lean_box(0);
            return v___x_2456_;
        } else {
            lean_dec(v_val_2455_);
            return v___x_2454_;
        }
    } else {
        let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_2454_);
        v___x_2457_ = lean_box(0);
        return v___x_2457_;
    }
}
pub unsafe fn l_Lean_getInitFnNameForCore_x3f___boxed(
    mut v_env_2458_: *mut LeanObject,
    mut v_attr_2459_: *mut LeanObject,
    mut v_fn_2460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2461_: *mut LeanObject = core::ptr::null_mut();
    v_res_2461_ = l_Lean_getInitFnNameForCore_x3f(v_env_2458_, v_attr_2459_, v_fn_2460_);
    lean_dec_ref(v_attr_2459_);
    return v_res_2461_;
}
pub unsafe fn l_Lean_getBuiltinInitFnNameFor_x3f(
    mut v_env_2462_: *mut LeanObject,
    mut v_fn_2463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    v___x_2464_ = l_Lean_builtinInitAttr;
    v___x_2465_ = l_Lean_getInitFnNameForCore_x3f(v_env_2462_, v___x_2464_, v_fn_2463_);
    return v___x_2465_;
}
pub unsafe fn lean_get_regular_init_fn_name_for(
    mut v_env_2466_: *mut LeanObject,
    mut v_fn_2467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    v___x_2468_ = l_Lean_regularInitAttr;
    v___x_2469_ = l_Lean_getInitFnNameForCore_x3f(v_env_2466_, v___x_2468_, v_fn_2467_);
    return v___x_2469_;
}
pub unsafe fn lean_get_init_fn_name_for(
    mut v_env_2470_: *mut LeanObject,
    mut v_fn_2471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_fn_2471_);
    lean_inc_ref(v_env_2470_);
    v___x_2472_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_2470_, v_fn_2471_);
    if lean_obj_tag(v___x_2472_) == 0 {
        let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
        v___x_2473_ = lean_get_regular_init_fn_name_for(v_env_2470_, v_fn_2471_);
        return v___x_2473_;
    } else {
        lean_dec(v_fn_2471_);
        lean_dec_ref(v_env_2470_);
        return v___x_2472_;
    }
}
pub unsafe fn l_Lean_isIOUnitInitFnCore(
    mut v_env_2474_: *mut LeanObject,
    mut v_attr_2475_: *mut LeanObject,
    mut v_fn_2476_: *mut LeanObject,
) -> u8 {
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    v___x_2477_ = lean_box(0);
    v___x_2478_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
        v___x_2477_,
        v_attr_2475_,
        v_env_2474_,
        v_fn_2476_,
    );
    if lean_obj_tag(v___x_2478_) == 1 {
        let mut v_val_2479_: *mut LeanObject = core::ptr::null_mut();
        v_val_2479_ = lean_ctor_get(v___x_2478_, 0);
        lean_inc(v_val_2479_);
        lean_dec_ref_known(v___x_2478_, 1);
        if lean_obj_tag(v_val_2479_) == 0 {
            let mut v___x_2480_: u8 = 0;
            v___x_2480_ = 1;
            return v___x_2480_;
        } else {
            let mut v___x_2481_: u8 = 0;
            lean_dec(v_val_2479_);
            v___x_2481_ = 0;
            return v___x_2481_;
        }
    } else {
        let mut v___x_2482_: u8 = 0;
        lean_dec(v___x_2478_);
        v___x_2482_ = 0;
        return v___x_2482_;
    }
}
pub unsafe fn l_Lean_isIOUnitInitFnCore___boxed(
    mut v_env_2483_: *mut LeanObject,
    mut v_attr_2484_: *mut LeanObject,
    mut v_fn_2485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2486_: u8 = 0;
    let mut v_r_2487_: *mut LeanObject = core::ptr::null_mut();
    v_res_2486_ = l_Lean_isIOUnitInitFnCore(v_env_2483_, v_attr_2484_, v_fn_2485_);
    lean_dec_ref(v_attr_2484_);
    v_r_2487_ = lean_box((v_res_2486_) as usize);
    return v_r_2487_;
}
pub unsafe fn l_Lean_isIOUnitRegularInitFn(
    mut v_env_2488_: *mut LeanObject,
    mut v_fn_2489_: *mut LeanObject,
) -> u8 {
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    v___x_2490_ = l_Lean_regularInitAttr;
    v___x_2491_ = l_Lean_isIOUnitInitFnCore(v_env_2488_, v___x_2490_, v_fn_2489_);
    return v___x_2491_;
}
pub unsafe fn l_Lean_isIOUnitRegularInitFn___boxed(
    mut v_env_2492_: *mut LeanObject,
    mut v_fn_2493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2494_: u8 = 0;
    let mut v_r_2495_: *mut LeanObject = core::ptr::null_mut();
    v_res_2494_ = l_Lean_isIOUnitRegularInitFn(v_env_2492_, v_fn_2493_);
    v_r_2495_ = lean_box((v_res_2494_) as usize);
    return v_r_2495_;
}
pub unsafe fn l_Lean_isIOUnitBuiltinInitFn(
    mut v_env_2496_: *mut LeanObject,
    mut v_fn_2497_: *mut LeanObject,
) -> u8 {
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: u8 = 0;
    v___x_2498_ = l_Lean_builtinInitAttr;
    v___x_2499_ = l_Lean_isIOUnitInitFnCore(v_env_2496_, v___x_2498_, v_fn_2497_);
    return v___x_2499_;
}
pub unsafe fn l_Lean_isIOUnitBuiltinInitFn___boxed(
    mut v_env_2500_: *mut LeanObject,
    mut v_fn_2501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2502_: u8 = 0;
    let mut v_r_2503_: *mut LeanObject = core::ptr::null_mut();
    v_res_2502_ = l_Lean_isIOUnitBuiltinInitFn(v_env_2500_, v_fn_2501_);
    v_r_2503_ = lean_box((v_res_2502_) as usize);
    return v_r_2503_;
}
pub unsafe fn l_Lean_isIOUnitInitFn(
    mut v_env_2504_: *mut LeanObject,
    mut v_fn_2505_: *mut LeanObject,
) -> u8 {
    let mut v___x_2506_: u8 = 0;
    lean_inc(v_fn_2505_);
    lean_inc_ref(v_env_2504_);
    v___x_2506_ = l_Lean_isIOUnitBuiltinInitFn(v_env_2504_, v_fn_2505_);
    if v___x_2506_ == 0 {
        let mut v___x_2507_: u8 = 0;
        v___x_2507_ = l_Lean_isIOUnitRegularInitFn(v_env_2504_, v_fn_2505_);
        return v___x_2507_;
    } else {
        lean_dec(v_fn_2505_);
        lean_dec_ref(v_env_2504_);
        return v___x_2506_;
    }
}
pub unsafe fn l_Lean_isIOUnitInitFn___boxed(
    mut v_env_2508_: *mut LeanObject,
    mut v_fn_2509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2510_: u8 = 0;
    let mut v_r_2511_: *mut LeanObject = core::ptr::null_mut();
    v_res_2510_ = l_Lean_isIOUnitInitFn(v_env_2508_, v_fn_2509_);
    v_r_2511_ = lean_box((v_res_2510_) as usize);
    return v_r_2511_;
}
pub unsafe fn l_Lean_hasInitAttr(
    mut v_env_2512_: *mut LeanObject,
    mut v_fn_2513_: *mut LeanObject,
) -> u8 {
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    v___x_2514_ = lean_get_init_fn_name_for(v_env_2512_, v_fn_2513_);
    if lean_obj_tag(v___x_2514_) == 0 {
        let mut v___x_2515_: u8 = 0;
        v___x_2515_ = 0;
        return v___x_2515_;
    } else {
        let mut v___x_2516_: u8 = 0;
        lean_dec_ref_known(v___x_2514_, 1);
        v___x_2516_ = 1;
        return v___x_2516_;
    }
}
pub unsafe fn l_Lean_hasInitAttr___boxed(
    mut v_env_2517_: *mut LeanObject,
    mut v_fn_2518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2519_: u8 = 0;
    let mut v_r_2520_: *mut LeanObject = core::ptr::null_mut();
    v_res_2519_ = l_Lean_hasInitAttr(v_env_2517_, v_fn_2518_);
    v_r_2520_ = lean_box((v_res_2519_) as usize);
    return v_r_2520_;
}
pub unsafe fn l_Lean_setBuiltinInitAttr(
    mut v_env_2521_: *mut LeanObject,
    mut v_declName_2522_: *mut LeanObject,
    mut v_initFnName_2523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_kind_2526_: *mut LeanObject,
    mut v___y_2527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2547_: u8 = 0;
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2553_: u8 = 0;
    let mut v_unused_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2529_ = lean_st_ref_get(v___y_2527_);
                v_auxDeclNGen_2530_ = lean_ctor_get(v___x_2529_, 3);
                lean_inc_ref(v_auxDeclNGen_2530_);
                lean_dec(v___x_2529_);
                v___x_2531_ = lean_st_ref_get(v___y_2527_);
                v_env_2532_ = lean_ctor_get(v___x_2531_, 0);
                lean_inc_ref(v_env_2532_);
                lean_dec(v___x_2531_);
                v___x_2533_ = l_Lean_DeclNameGenerator_mkUniqueName(
                    v_env_2532_,
                    v_auxDeclNGen_2530_,
                    v_kind_2526_,
                );
                v_fst_2534_ = lean_ctor_get(v___x_2533_, 0);
                lean_inc(v_fst_2534_);
                v_snd_2535_ = lean_ctor_get(v___x_2533_, 1);
                lean_inc(v_snd_2535_);
                lean_dec_ref(v___x_2533_);
                v___x_2536_ = lean_st_ref_take(v___y_2527_);
                v_env_2537_ = lean_ctor_get(v___x_2536_, 0);
                v_nextMacroScope_2538_ = lean_ctor_get(v___x_2536_, 1);
                v_ngen_2539_ = lean_ctor_get(v___x_2536_, 2);
                v_traceState_2540_ = lean_ctor_get(v___x_2536_, 4);
                v_cache_2541_ = lean_ctor_get(v___x_2536_, 5);
                v_messages_2542_ = lean_ctor_get(v___x_2536_, 6);
                v_infoState_2543_ = lean_ctor_get(v___x_2536_, 7);
                v_snapshotTasks_2544_ = lean_ctor_get(v___x_2536_, 8);
                v_isSharedCheck_2553_ = (!lean_is_exclusive(v___x_2536_)) as u8;
                if v_isSharedCheck_2553_ == 0 {
                    v_unused_2554_ = lean_ctor_get(v___x_2536_, 3);
                    lean_dec(v_unused_2554_);
                    v___x_2546_ = v___x_2536_;
                    v_isShared_2547_ = v_isSharedCheck_2553_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2544_);
                    lean_inc(v_infoState_2543_);
                    lean_inc(v_messages_2542_);
                    lean_inc(v_cache_2541_);
                    lean_inc(v_traceState_2540_);
                    lean_inc(v_ngen_2539_);
                    lean_inc(v_nextMacroScope_2538_);
                    lean_inc(v_env_2537_);
                    lean_dec(v___x_2536_);
                    v___x_2546_ = lean_box(0);
                    v_isShared_2547_ = v_isSharedCheck_2553_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2547_ == 0 {
                    lean_ctor_set(v___x_2546_, 3, v_snd_2535_);
                    v___x_2549_ = v___x_2546_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_env_2537_);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_nextMacroScope_2538_);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_ngen_2539_);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_snd_2535_);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 4, v_traceState_2540_);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 5, v_cache_2541_);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 6, v_messages_2542_);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 7, v_infoState_2543_);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 8, v_snapshotTasks_2544_);
                    v___x_2549_ = v_reuseFailAlloc_2552_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2550_ = lean_st_ref_set(v___y_2527_, v___x_2549_);
                v___x_2551_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2551_, 0, v_fst_2534_);
                return v___x_2551_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0___redArg___boxed(
    mut v_kind_2555_: *mut LeanObject,
    mut v___y_2556_: *mut LeanObject,
    mut v___y_2557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2558_: *mut LeanObject = core::ptr::null_mut();
    v_res_2558_ = l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0___redArg(
        v_kind_2555_,
        v___y_2556_,
    );
    lean_dec(v___y_2556_);
    return v_res_2558_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0(
    mut v_kind_2559_: *mut LeanObject,
    mut v___y_2560_: *mut LeanObject,
    mut v___y_2561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    v___x_2563_ = l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0___redArg(
        v_kind_2559_,
        v___y_2561_,
    );
    return v___x_2563_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0___boxed(
    mut v_kind_2564_: *mut LeanObject,
    mut v___y_2565_: *mut LeanObject,
    mut v___y_2566_: *mut LeanObject,
    mut v___y_2567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2568_: *mut LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0(
        v_kind_2564_,
        v___y_2565_,
        v___y_2566_,
    );
    lean_dec(v___y_2566_);
    lean_dec_ref(v___y_2565_);
    return v_res_2568_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1___redArg(
    mut v_e_2569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2574_: u8 = 0;
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_a_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2583_: u8 = 0;
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_2569_) == 0 {
                    v_a_2571_ = lean_ctor_get(v_e_2569_, 0);
                    v_isSharedCheck_2579_ = (!lean_is_exclusive(v_e_2569_)) as u8;
                    if v_isSharedCheck_2579_ == 0 {
                        v___x_2573_ = v_e_2569_;
                        v_isShared_2574_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2571_);
                        lean_dec(v_e_2569_);
                        v___x_2573_ = lean_box(0);
                        v_isShared_2574_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2580_ = lean_ctor_get(v_e_2569_, 0);
                    v_isSharedCheck_2587_ = (!lean_is_exclusive(v_e_2569_)) as u8;
                    if v_isSharedCheck_2587_ == 0 {
                        v___x_2582_ = v_e_2569_;
                        v_isShared_2583_ = v_isSharedCheck_2587_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2580_);
                        lean_dec(v_e_2569_);
                        v___x_2582_ = lean_box(0);
                        v_isShared_2583_ = v_isSharedCheck_2587_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2575_ = lean_mk_io_user_error(v_a_2571_);
                if v_isShared_2574_ == 0 {
                    lean_ctor_set_tag(v___x_2573_, 1);
                    lean_ctor_set(v___x_2573_, 0, v___x_2575_);
                    v___x_2577_ = v___x_2573_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
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
                    lean_ctor_set_tag(v___x_2582_, 0);
                    v___x_2585_ = v___x_2582_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
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
    mut v_e_2588_: *mut LeanObject,
    mut v_a_2589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2590_: *mut LeanObject = core::ptr::null_mut();
    v_res_2590_ = l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1___redArg(v_e_2588_);
    return v_res_2590_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1(
    mut v_00_u03b1_2591_: *mut LeanObject,
    mut v_e_2592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    v___x_2594_ = l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1___redArg(v_e_2592_);
    return v___x_2594_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1___boxed(
    mut v_00_u03b1_2595_: *mut LeanObject,
    mut v_e_2596_: *mut LeanObject,
    mut v_a_2597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2598_: *mut LeanObject = core::ptr::null_mut();
    v_res_2598_ = l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1(v_00_u03b1_2595_, v_e_2596_);
    return v_res_2598_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2___redArg(
    mut v_env_2599_: *mut LeanObject,
    mut v___y_2600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2620_: u8 = 0;
    let mut v_unused_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2602_ = lean_st_ref_take(v___y_2600_);
                v_nextMacroScope_2603_ = lean_ctor_get(v___x_2602_, 1);
                v_ngen_2604_ = lean_ctor_get(v___x_2602_, 2);
                v_auxDeclNGen_2605_ = lean_ctor_get(v___x_2602_, 3);
                v_traceState_2606_ = lean_ctor_get(v___x_2602_, 4);
                v_messages_2607_ = lean_ctor_get(v___x_2602_, 6);
                v_infoState_2608_ = lean_ctor_get(v___x_2602_, 7);
                v_snapshotTasks_2609_ = lean_ctor_get(v___x_2602_, 8);
                v_isSharedCheck_2620_ = (!lean_is_exclusive(v___x_2602_)) as u8;
                if v_isSharedCheck_2620_ == 0 {
                    v_unused_2621_ = lean_ctor_get(v___x_2602_, 5);
                    lean_dec(v_unused_2621_);
                    v_unused_2622_ = lean_ctor_get(v___x_2602_, 0);
                    lean_dec(v_unused_2622_);
                    v___x_2611_ = v___x_2602_;
                    v_isShared_2612_ = v_isSharedCheck_2620_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2609_);
                    lean_inc(v_infoState_2608_);
                    lean_inc(v_messages_2607_);
                    lean_inc(v_traceState_2606_);
                    lean_inc(v_auxDeclNGen_2605_);
                    lean_inc(v_ngen_2604_);
                    lean_inc(v_nextMacroScope_2603_);
                    lean_dec(v___x_2602_);
                    v___x_2611_ = lean_box(0);
                    v_isShared_2612_ = v_isSharedCheck_2620_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2613_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_registerInitAttrUnsafe_spec__2_spec__4___redArg___closed__2);
                if v_isShared_2612_ == 0 {
                    lean_ctor_set(v___x_2611_, 5, v___x_2613_);
                    lean_ctor_set(v___x_2611_, 0, v_env_2599_);
                    v___x_2615_ = v___x_2611_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_env_2599_);
                    lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_nextMacroScope_2603_);
                    lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_ngen_2604_);
                    lean_ctor_set(v_reuseFailAlloc_2619_, 3, v_auxDeclNGen_2605_);
                    lean_ctor_set(v_reuseFailAlloc_2619_, 4, v_traceState_2606_);
                    lean_ctor_set(v_reuseFailAlloc_2619_, 5, v___x_2613_);
                    lean_ctor_set(v_reuseFailAlloc_2619_, 6, v_messages_2607_);
                    lean_ctor_set(v_reuseFailAlloc_2619_, 7, v_infoState_2608_);
                    lean_ctor_set(v_reuseFailAlloc_2619_, 8, v_snapshotTasks_2609_);
                    v___x_2615_ = v_reuseFailAlloc_2619_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2616_ = lean_st_ref_set(v___y_2600_, v___x_2615_);
                v___x_2617_ = lean_box(0);
                v___x_2618_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2618_, 0, v___x_2617_);
                return v___x_2618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2___redArg___boxed(
    mut v_env_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
    mut v___y_2625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2626_: *mut LeanObject = core::ptr::null_mut();
    v_res_2626_ =
        l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2___redArg(v_env_2623_, v___y_2624_);
    lean_dec(v___y_2624_);
    return v_res_2626_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2(
    mut v_env_2627_: *mut LeanObject,
    mut v___y_2628_: *mut LeanObject,
    mut v___y_2629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    v___x_2631_ =
        l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2___redArg(v_env_2627_, v___y_2629_);
    return v___x_2631_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2___boxed(
    mut v_env_2632_: *mut LeanObject,
    mut v___y_2633_: *mut LeanObject,
    mut v___y_2634_: *mut LeanObject,
    mut v___y_2635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2636_: *mut LeanObject = core::ptr::null_mut();
    v_res_2636_ =
        l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2(v_env_2632_, v___y_2633_, v___y_2634_);
    lean_dec(v___y_2634_);
    lean_dec_ref(v___y_2633_);
    return v_res_2636_;
}
pub unsafe fn _init_l_Lean_declareBuiltin___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    v___x_2639_ = lean_box(0);
    v___x_2640_ = l_Lean_declareBuiltin___lam__0___closed__0;
    v___x_2641_ = l_Lean_mkConst(v___x_2640_, v___x_2639_);
    return v___x_2641_;
}
pub unsafe fn _init_l_Lean_declareBuiltin___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    v___x_2644_ = lean_box(0);
    v___x_2645_ = l_Lean_declareBuiltin___lam__0___closed__2;
    v___x_2646_ = l_Lean_mkConst(v___x_2645_, v___x_2644_);
    return v___x_2646_;
}
pub unsafe fn _init_l_Lean_declareBuiltin___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    v___x_2647_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_declareBuiltin___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_declareBuiltin___lam__0___closed__3_once),
        _init_l_Lean_declareBuiltin___lam__0___closed__3,
    );
    v___x_2648_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_declareBuiltin___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_declareBuiltin___lam__0___closed__1_once),
        _init_l_Lean_declareBuiltin___lam__0___closed__1,
    );
    v___x_2649_ = l_Lean_Expr_app___override(v___x_2648_, v___x_2647_);
    return v___x_2649_;
}
pub unsafe fn l_Lean_declareBuiltin___lam__0(
    mut v___x_2650_: *mut LeanObject,
    mut v_value_2651_: *mut LeanObject,
    mut v___y_2652_: *mut LeanObject,
    mut v___y_2653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2659_: u8 = 0;
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: u8 = 0;
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: u8 = 0;
    let mut v___x_2670_: u8 = 0;
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2685_: u8 = 0;
    let mut v_ref_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut v_unused_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2655_ = l_Lean_mkAuxDeclName___at___00Lean_declareBuiltin_spec__0___redArg(
                    v___x_2650_,
                    v___y_2653_,
                );
                v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
                v_isSharedCheck_2700_ = (!lean_is_exclusive(v___x_2655_)) as u8;
                if v_isSharedCheck_2700_ == 0 {
                    v___x_2658_ = v___x_2655_;
                    v_isShared_2659_ = v_isSharedCheck_2700_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2656_);
                    lean_dec(v___x_2655_);
                    v___x_2658_ = lean_box(0);
                    v_isShared_2659_ = v_isSharedCheck_2700_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2660_ = lean_box(0);
                v___x_2661_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_declareBuiltin___lam__0___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_declareBuiltin___lam__0___closed__4_once),
                    _init_l_Lean_declareBuiltin___lam__0___closed__4,
                );
                lean_inc_n(v_a_2656_, 2);
                v___x_2662_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2662_, 0, v_a_2656_);
                lean_ctor_set(v___x_2662_, 1, v___x_2660_);
                lean_ctor_set(v___x_2662_, 2, v___x_2661_);
                v___x_2663_ = lean_box(0);
                v___x_2664_ = 1;
                v___x_2665_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2665_, 0, v_a_2656_);
                lean_ctor_set(v___x_2665_, 1, v___x_2660_);
                v___x_2666_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_2666_, 0, v___x_2662_);
                lean_ctor_set(v___x_2666_, 1, v_value_2651_);
                lean_ctor_set(v___x_2666_, 2, v___x_2663_);
                lean_ctor_set(v___x_2666_, 3, v___x_2665_);
                lean_ctor_set_uint8(
                    v___x_2666_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___x_2664_,
                );
                if v_isShared_2659_ == 0 {
                    lean_ctor_set_tag(v___x_2658_, 1);
                    lean_ctor_set(v___x_2658_, 0, v___x_2666_);
                    v___x_2668_ = v___x_2658_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2666_);
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
                if lean_obj_tag(v___x_2671_) == 0 {
                    v_isSharedCheck_2697_ = (!lean_is_exclusive(v___x_2671_)) as u8;
                    if v_isSharedCheck_2697_ == 0 {
                        v_unused_2698_ = lean_ctor_get(v___x_2671_, 0);
                        lean_dec(v_unused_2698_);
                        v___x_2673_ = v___x_2671_;
                        v_isShared_2674_ = v_isSharedCheck_2697_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_2671_);
                        v___x_2673_ = lean_box(0);
                        v_isShared_2674_ = v_isSharedCheck_2697_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2656_);
                    return v___x_2671_;
                }
            }
            3 => {
                v___x_2675_ = lean_st_ref_get(v___y_2653_);
                v_env_2676_ = lean_ctor_get(v___x_2675_, 0);
                lean_inc_ref(v_env_2676_);
                lean_dec(v___x_2675_);
                v___x_2677_ = lean_box(0);
                v___x_2678_ = l_Lean_setBuiltinInitAttr(v_env_2676_, v_a_2656_, v___x_2677_);
                v___x_2679_ =
                    l_IO_ofExcept___at___00Lean_declareBuiltin_spec__1___redArg(v___x_2678_);
                if lean_obj_tag(v___x_2679_) == 0 {
                    lean_del_object(v___x_2673_);
                    v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
                    lean_inc(v_a_2680_);
                    lean_dec_ref_known(v___x_2679_, 1);
                    v___x_2681_ = l_Lean_setEnv___at___00Lean_declareBuiltin_spec__2___redArg(
                        v_a_2680_,
                        v___y_2653_,
                    );
                    return v___x_2681_;
                } else {
                    v_a_2682_ = lean_ctor_get(v___x_2679_, 0);
                    v_isSharedCheck_2696_ = (!lean_is_exclusive(v___x_2679_)) as u8;
                    if v_isSharedCheck_2696_ == 0 {
                        v___x_2684_ = v___x_2679_;
                        v_isShared_2685_ = v_isSharedCheck_2696_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2682_);
                        lean_dec(v___x_2679_);
                        v___x_2684_ = lean_box(0);
                        v_isShared_2685_ = v_isSharedCheck_2696_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v_ref_2686_ = lean_ctor_get(v___y_2652_, 5);
                v___x_2687_ = lean_io_error_to_string(v_a_2682_);
                if v_isShared_2674_ == 0 {
                    lean_ctor_set_tag(v___x_2673_, 3);
                    lean_ctor_set(v___x_2673_, 0, v___x_2687_);
                    v___x_2689_ = v___x_2673_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2695_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2687_);
                    v___x_2689_ = v_reuseFailAlloc_2695_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2690_ = l_Lean_MessageData_ofFormat(v___x_2689_);
                lean_inc(v_ref_2686_);
                v___x_2691_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2691_, 0, v_ref_2686_);
                lean_ctor_set(v___x_2691_, 1, v___x_2690_);
                if v_isShared_2685_ == 0 {
                    lean_ctor_set(v___x_2684_, 0, v___x_2691_);
                    v___x_2693_ = v___x_2684_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
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
    mut v___x_2701_: *mut LeanObject,
    mut v_value_2702_: *mut LeanObject,
    mut v___y_2703_: *mut LeanObject,
    mut v___y_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2706_: *mut LeanObject = core::ptr::null_mut();
    v_res_2706_ =
        l_Lean_declareBuiltin___lam__0(v___x_2701_, v_value_2702_, v___y_2703_, v___y_2704_);
    lean_dec(v___y_2704_);
    lean_dec_ref(v___y_2703_);
    return v_res_2706_;
}
pub unsafe fn l_Lean_declareBuiltin(
    mut v_forDecl_2710_: *mut LeanObject,
    mut v_value_2711_: *mut LeanObject,
    mut v_a_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: u8 = 0;
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    v___x_2715_ = l_Lean_declareBuiltin___closed__1;
    v___x_2716_ = l_Lean_Name_append(v___x_2715_, v_forDecl_2710_);
    v___f_2717_ = lean_alloc_closure(
        l_Lean_declareBuiltin___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2717_, 0, v___x_2716_);
    lean_closure_set(v___f_2717_, 1, v_value_2711_);
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
    mut v_forDecl_2720_: *mut LeanObject,
    mut v_value_2721_: *mut LeanObject,
    mut v_a_2722_: *mut LeanObject,
    mut v_a_2723_: *mut LeanObject,
    mut v_a_2724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2725_: *mut LeanObject = core::ptr::null_mut();
    v_res_2725_ = l_Lean_declareBuiltin(v_forDecl_2720_, v_value_2721_, v_a_2722_, v_a_2723_);
    lean_dec(v_a_2723_);
    lean_dec_ref(v_a_2722_);
    return v_res_2725_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__3(
    mut v_opts_2726_: *mut LeanObject,
    mut v_opt_2727_: *mut LeanObject,
) -> u8 {
    let mut v_name_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    v_name_2728_ = lean_ctor_get(v_opt_2727_, 0);
    v_defValue_2729_ = lean_ctor_get(v_opt_2727_, 1);
    v_map_2730_ = lean_ctor_get(v_opts_2726_, 0);
    v___x_2731_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2730_,
            v_name_2728_,
        );
    if lean_obj_tag(v___x_2731_) == 0 {
        let mut v___x_2732_: u8 = 0;
        v___x_2732_ = (lean_unbox(v_defValue_2729_) as u8);
        return v___x_2732_;
    } else {
        let mut v_val_2733_: *mut LeanObject = core::ptr::null_mut();
        v_val_2733_ = lean_ctor_get(v___x_2731_, 0);
        lean_inc(v_val_2733_);
        lean_dec_ref_known(v___x_2731_, 1);
        if lean_obj_tag(v_val_2733_) == 1 {
            let mut v_v_2734_: u8 = 0;
            v_v_2734_ = lean_ctor_get_uint8(v_val_2733_, 0 as u32);
            lean_dec_ref_known(v_val_2733_, 0);
            return v_v_2734_;
        } else {
            let mut v___x_2735_: u8 = 0;
            lean_dec(v_val_2733_);
            v___x_2735_ = (lean_unbox(v_defValue_2729_) as u8);
            return v___x_2735_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__3___boxed(
    mut v_opts_2736_: *mut LeanObject,
    mut v_opt_2737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2738_: u8 = 0;
    let mut v_r_2739_: *mut LeanObject = core::ptr::null_mut();
    v_res_2738_ =
        l_Lean_Option_get___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__3(
            v_opts_2736_,
            v_opt_2737_,
        );
    lean_dec_ref(v_opt_2737_);
    lean_dec_ref(v_opts_2736_);
    v_r_2739_ = lean_box((v_res_2738_) as usize);
    return v_r_2739_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0_spec__0(
    mut v_a_2740_: *mut LeanObject,
    mut v_as_2741_: *mut LeanObject,
    mut v_i_2742_: usize,
    mut v_stop_2743_: usize,
) -> u8 {
    let mut v___x_2744_: u8 = 0;
    let mut v_fst_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2749_: *mut LeanObject = core::ptr::null_mut();
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
                    v_fst_2745_ = lean_ctor_get(v_a_2740_, 0);
                    v_snd_2746_ = lean_ctor_get(v_a_2740_, 1);
                    v___x_2747_ = lean_array_uget_borrowed(v_as_2741_, v_i_2742_);
                    v_fst_2748_ = lean_ctor_get(v___x_2747_, 0);
                    v_snd_2749_ = lean_ctor_get(v___x_2747_, 1);
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
    mut v_a_2759_: *mut LeanObject,
    mut v_as_2760_: *mut LeanObject,
    mut v_i_2761_: *mut LeanObject,
    mut v_stop_2762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2763_: usize = 0;
    let mut v_stop_boxed_2764_: usize = 0;
    let mut v_res_2765_: u8 = 0;
    let mut v_r_2766_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2763_ = lean_unbox_usize(v_i_2761_);
    lean_dec(v_i_2761_);
    v_stop_boxed_2764_ = lean_unbox_usize(v_stop_2762_);
    lean_dec(v_stop_2762_);
    v_res_2765_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0_spec__0(v_a_2759_, v_as_2760_, v_i_boxed_2763_, v_stop_boxed_2764_);
    lean_dec_ref(v_as_2760_);
    lean_dec_ref(v_a_2759_);
    v_r_2766_ = lean_box((v_res_2765_) as usize);
    return v_r_2766_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0(
    mut v_as_2767_: *mut LeanObject,
    mut v_a_2768_: *mut LeanObject,
) -> u8 {
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u8 = 0;
    v___x_2769_ = lean_unsigned_to_nat(0);
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
    mut v_as_2775_: *mut LeanObject,
    mut v_a_2776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2777_: u8 = 0;
    let mut v_r_2778_: *mut LeanObject = core::ptr::null_mut();
    v_res_2777_ =
        l_Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0(
            v_as_2775_, v_a_2776_,
        );
    lean_dec_ref(v_a_2776_);
    lean_dec_ref(v_as_2775_);
    v_r_2778_ = lean_box((v_res_2777_) as usize);
    return v_r_2778_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__2(
    mut v___x_2779_: *mut LeanObject,
    mut v_as_2780_: *mut LeanObject,
    mut v_i_2781_: usize,
    mut v_stop_2782_: usize,
    mut v_b_2783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: usize = 0;
    let mut v___x_2787_: usize = 0;
    let mut v___x_2789_: u8 = 0;
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: u8 = 0;
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2789_ = lean_usize_dec_eq(v_i_2781_, v_stop_2782_);
                if v___x_2789_ == 0 {
                    v___x_2790_ = lean_array_uget_borrowed(v_as_2780_, v_i_2781_);
                    v___x_2791_ = l_Array_contains___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__0(v___x_2779_, v___x_2790_);
                    if v___x_2791_ == 0 {
                        lean_inc(v___x_2790_);
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
    mut v___x_2793_: *mut LeanObject,
    mut v_as_2794_: *mut LeanObject,
    mut v_i_2795_: *mut LeanObject,
    mut v_stop_2796_: *mut LeanObject,
    mut v_b_2797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2798_: usize = 0;
    let mut v_stop_boxed_2799_: usize = 0;
    let mut v_res_2800_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2798_ = lean_unbox_usize(v_i_2795_);
    lean_dec(v_i_2795_);
    v_stop_boxed_2799_ = lean_unbox_usize(v_stop_2796_);
    lean_dec(v_stop_2796_);
    v_res_2800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__2(v___x_2793_, v_as_2794_, v_i_boxed_2798_, v_stop_boxed_2799_, v_b_2797_);
    lean_dec_ref(v_as_2794_);
    lean_dec_ref(v___x_2793_);
    return v_res_2800_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__1(
    mut v_env_2801_: *mut LeanObject,
    mut v_opts_2802_: *mut LeanObject,
    mut v___y_2803_: u8,
    mut v___x_2804_: u8,
    mut v_as_2805_: *mut LeanObject,
    mut v_sz_2806_: usize,
    mut v_i_2807_: usize,
    mut v_b_2808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: usize = 0;
    let mut v___x_2813_: usize = 0;
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: u8 = 0;
    let mut v___x_2823_: u8 = 0;
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2832_: u8 = 0;
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_dec_ref(v_env_2801_);
                    v___x_2816_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2816_, 0, v_b_2808_);
                    return v___x_2816_;
                } else {
                    v_a_2817_ = lean_array_uget_borrowed(v_as_2805_, v_i_2807_);
                    v_fst_2818_ = lean_ctor_get(v_a_2817_, 0);
                    v_snd_2819_ = lean_ctor_get(v_a_2817_, 1);
                    v___x_2820_ = lean_box(0);
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
                    if lean_obj_tag(v___x_2824_) == 0 {
                        lean_dec_ref_known(v___x_2824_, 1);
                        v_a_2811_ = v___x_2820_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_env_2801_);
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
                    if lean_obj_tag(v___x_2826_) == 0 {
                        v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
                        lean_inc(v_a_2827_);
                        lean_dec_ref_known(v___x_2826_, 1);
                        v___x_2828_ = lean_apply_1(v_a_2827_, lean_box(0));
                        if lean_obj_tag(v___x_2828_) == 0 {
                            lean_dec_ref_known(v___x_2828_, 1);
                            v_a_2811_ = v___x_2820_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_env_2801_);
                            return v___x_2828_;
                        }
                    } else {
                        lean_dec_ref(v_env_2801_);
                        v_a_2829_ = lean_ctor_get(v___x_2826_, 0);
                        v_isSharedCheck_2836_ = (!lean_is_exclusive(v___x_2826_)) as u8;
                        if v_isSharedCheck_2836_ == 0 {
                            v___x_2831_ = v___x_2826_;
                            v_isShared_2832_ = v_isSharedCheck_2836_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2829_);
                            lean_dec(v___x_2826_);
                            v___x_2831_ = lean_box(0);
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
                    v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
                    v___x_2834_ = v_reuseFailAlloc_2835_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2834_;
            }
            5 => {
                lean_inc(v_fst_2818_);
                lean_inc_ref(v_env_2801_);
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
    mut v_env_2841_: *mut LeanObject,
    mut v_opts_2842_: *mut LeanObject,
    mut v___y_2843_: *mut LeanObject,
    mut v___x_2844_: *mut LeanObject,
    mut v_as_2845_: *mut LeanObject,
    mut v_sz_2846_: *mut LeanObject,
    mut v_i_2847_: *mut LeanObject,
    mut v_b_2848_: *mut LeanObject,
    mut v___y_2849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6088__boxed_2850_: u8 = 0;
    let mut v___x_6089__boxed_2851_: u8 = 0;
    let mut v_sz_boxed_2852_: usize = 0;
    let mut v_i_boxed_2853_: usize = 0;
    let mut v_res_2854_: *mut LeanObject = core::ptr::null_mut();
    v___y_6088__boxed_2850_ = (lean_unbox(v___y_2843_) as u8);
    v___x_6089__boxed_2851_ = (lean_unbox(v___x_2844_) as u8);
    v_sz_boxed_2852_ = lean_unbox_usize(v_sz_2846_);
    lean_dec(v_sz_2846_);
    v_i_boxed_2853_ = lean_unbox_usize(v_i_2847_);
    lean_dec(v_i_2847_);
    v_res_2854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__1(v_env_2841_, v_opts_2842_, v___y_6088__boxed_2850_, v___x_6089__boxed_2851_, v_as_2845_, v_sz_boxed_2852_, v_i_boxed_2853_, v_b_2848_);
    lean_dec_ref(v_as_2845_);
    lean_dec_ref(v_opts_2842_);
    return v_res_2854_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4(
    mut v_env_2860_: *mut LeanObject,
    mut v_opts_2861_: *mut LeanObject,
    mut v___x_2862_: *mut LeanObject,
    mut v_a_2863_: u8,
    mut v_as_2864_: *mut LeanObject,
    mut v_sz_2865_: usize,
    mut v_i_2866_: usize,
    mut v_b_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: usize = 0;
    let mut v___x_2872_: usize = 0;
    let mut v___x_2874_: u8 = 0;
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2880_: u8 = 0;
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2888_: u8 = 0;
    let mut v___y_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2890_: u8 = 0;
    let mut v___y_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2894_: usize = 0;
    let mut v___x_2895_: usize = 0;
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2900_: u8 = 0;
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2904_: u8 = 0;
    let mut v___y_2906_: u8 = 0;
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: u8 = 0;
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: u8 = 0;
    let mut v___x_2925_: usize = 0;
    let mut v___x_2926_: usize = 0;
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: usize = 0;
    let mut v___x_2929_: usize = 0;
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2932_: u8 = 0;
    let mut v___y_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2934_: u8 = 0;
    let mut v_toImport_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: u8 = 0;
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: u8 = 0;
    let mut v_a_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2945_: u8 = 0;
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2949_: u8 = 0;
    let mut v___y_2951_: u8 = 0;
    let mut v_isModule_2952_: u8 = 0;
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: u8 = 0;
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: u8 = 0;
    let mut v_a_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2964_: u8 = 0;
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_toImport_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: u8 = 0;
    let mut v_a_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2983_: u8 = 0;
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: u8 = 0;
    let mut v_irPhases_2986_: u8 = 0;
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: u8 = 0;
    let mut v_reuseFailAlloc_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2874_ = lean_usize_dec_lt(v_i_2866_, v_sz_2865_);
                if v___x_2874_ == 0 {
                    lean_dec_ref(v_env_2860_);
                    v___x_2875_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2875_, 0, v_b_2867_);
                    return v___x_2875_;
                } else {
                    if lean_obj_tag(v_b_2867_) == 0 {
                        lean_dec_ref(v_env_2860_);
                        v___x_2876_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2876_, 0, v_b_2867_);
                        return v___x_2876_;
                    } else {
                        v_val_2877_ = lean_ctor_get(v_b_2867_, 0);
                        v_isSharedCheck_2990_ = (!lean_is_exclusive(v_b_2867_)) as u8;
                        if v_isSharedCheck_2990_ == 0 {
                            v___x_2879_ = v_b_2867_;
                            v_isShared_2880_ = v_isSharedCheck_2990_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_2877_);
                            lean_dec(v_b_2867_);
                            v___x_2879_ = lean_box(0);
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
                v___x_2881_ = lean_unsigned_to_nat(0);
                v_a_2882_ = lean_array_uget_borrowed(v_as_2864_, v_i_2866_);
                v___x_2883_ = lean_unsigned_to_nat(1);
                v___x_2884_ = lean_nat_add(v_val_2877_, v___x_2883_);
                if v_isShared_2880_ == 0 {
                    lean_ctor_set(v___x_2879_, 0, v___x_2884_);
                    v___x_2886_ = v___x_2879_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2884_);
                    v___x_2886_ = v_reuseFailAlloc_2989_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2984_ = l_Lean_Elab_inServer;
                v___x_2985_ = l_Lean_Option_get___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__3(v_opts_2861_, v___x_2984_);
                if v___x_2985_ == 0 {
                    v_irPhases_2986_ = lean_ctor_get_uint8(
                        v_a_2882_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                lean_dec_ref(v___y_2891_);
                v___x_2893_ = lean_box(0);
                v_sz_2894_ = lean_array_size(v___x_2892_);
                v___x_2895_ = 0usize;
                lean_inc_ref(v_env_2860_);
                v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__1(v_env_2860_, v_opts_2861_, v___y_2888_, v___y_2890_, v___x_2892_, v_sz_2894_, v___x_2895_, v___x_2893_);
                lean_dec_ref(v___x_2892_);
                if lean_obj_tag(v___x_2896_) == 0 {
                    lean_dec_ref_known(v___x_2896_, 1);
                    v_a_2870_ = v___x_2886_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___x_2886_);
                    lean_dec_ref(v_env_2860_);
                    v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
                    v_isSharedCheck_2904_ = (!lean_is_exclusive(v___x_2896_)) as u8;
                    if v_isSharedCheck_2904_ == 0 {
                        v___x_2899_ = v___x_2896_;
                        v_isShared_2900_ = v_isSharedCheck_2904_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2897_);
                        lean_dec(v___x_2896_);
                        v___x_2899_ = lean_box(0);
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
                    v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
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
                v_toImport_2909_ = lean_ctor_get(v_a_2882_, 0);
                v_module_2910_ = lean_ctor_get(v_toImport_2909_, 0);
                v___x_2911_ = l_Lean_NameSet_contains(v___x_2908_, v_module_2910_);
                lean_dec(v___x_2908_);
                if v___x_2911_ == 0 {
                    v___x_2912_ = lean_st_ref_take(v___x_2907_);
                    lean_inc(v_module_2910_);
                    v___x_2913_ = l_Lean_NameSet_insert(v___x_2912_, v_module_2910_);
                    v___x_2914_ = lean_st_ref_set(v___x_2907_, v___x_2913_);
                    v___x_2915_ = l_Lean_regularInitAttr;
                    v_ext_2916_ = lean_ctor_get(v___x_2915_, 1);
                    v___x_2917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__0;
                    v___x_2918_ = 0;
                    v___x_2919_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                        v___x_2917_,
                        v_ext_2916_,
                        v_env_2860_,
                        v_val_2877_,
                        v___x_2918_,
                    );
                    v___x_2920_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_2917_, v_ext_2916_, v_env_2860_, v_val_2877_);
                    lean_dec(v_val_2877_);
                    v___x_2921_ = lean_array_get_size(v___x_2920_);
                    v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4___closed__1;
                    v___x_2923_ = lean_nat_dec_lt(v___x_2881_, v___x_2921_);
                    if v___x_2923_ == 0 {
                        lean_dec_ref(v___x_2920_);
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
                                lean_dec_ref(v___x_2920_);
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
                                lean_dec_ref(v___x_2920_);
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
                            lean_dec_ref(v___x_2920_);
                            v___y_2888_ = v___y_2906_;
                            v___y_2889_ = v___x_2919_;
                            v___y_2890_ = v___x_2911_;
                            v___y_2891_ = v___x_2930_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_val_2877_);
                    v_a_2870_ = v___x_2886_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                v_toImport_2935_ = lean_ctor_get(v_a_2882_, 0);
                v_module_2936_ = lean_ctor_get(v_toImport_2935_, 0);
                v___x_2937_ = 1;
                lean_inc(v_module_2936_);
                v___x_2938_ = l_Lean_mkModuleInitializationFunctionName(
                    v_module_2936_,
                    v___y_2933_,
                    v___x_2937_,
                );
                lean_dec(v___y_2933_);
                v___x_2939_ = lean_run_mod_init_core(v___x_2938_);
                lean_dec_ref(v___x_2938_);
                if lean_obj_tag(v___x_2939_) == 0 {
                    if v_a_2934_ == 0 {
                        v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
                        lean_inc(v_a_2940_);
                        lean_dec_ref_known(v___x_2939_, 1);
                        v___x_2941_ = (lean_unbox(v_a_2940_) as u8);
                        lean_dec(v_a_2940_);
                        if v___x_2941_ == 0 {
                            v___y_2906_ = v___y_2932_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v_val_2877_);
                            v_a_2870_ = v___x_2886_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_2939_, 1);
                        lean_dec(v_val_2877_);
                        v_a_2870_ = v___x_2886_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2886_);
                    lean_dec(v_val_2877_);
                    lean_dec_ref(v_env_2860_);
                    v_a_2942_ = lean_ctor_get(v___x_2939_, 0);
                    v_isSharedCheck_2949_ = (!lean_is_exclusive(v___x_2939_)) as u8;
                    if v_isSharedCheck_2949_ == 0 {
                        v___x_2944_ = v___x_2939_;
                        v_isShared_2945_ = v_isSharedCheck_2949_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2942_);
                        lean_dec(v___x_2939_);
                        v___x_2944_ = lean_box(0);
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
                    v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
                    v___x_2947_ = v_reuseFailAlloc_2948_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2947_;
            }
            11 => {
                v_isModule_2952_ = lean_ctor_get_uint8(
                    v___x_2862_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 4) as u32,
                );
                v___x_2953_ =
                    l_Lean_Environment_getModulePackageByIdx_x3f(v_env_2860_, v_val_2877_);
                if v_isModule_2952_ == 0 {
                    v_toImport_2954_ = lean_ctor_get(v_a_2882_, 0);
                    v_module_2955_ = lean_ctor_get(v_toImport_2954_, 0);
                    v___x_2956_ = 2;
                    lean_inc(v_module_2955_);
                    v___x_2957_ = l_Lean_mkModuleInitializationFunctionName(
                        v_module_2955_,
                        v___x_2953_,
                        v___x_2956_,
                    );
                    lean_dec(v___x_2953_);
                    v___x_2958_ = lean_run_mod_init_core(v___x_2957_);
                    lean_dec_ref(v___x_2957_);
                    if lean_obj_tag(v___x_2958_) == 0 {
                        v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
                        lean_inc(v_a_2959_);
                        lean_dec_ref_known(v___x_2958_, 1);
                        v___x_2960_ = (lean_unbox(v_a_2959_) as u8);
                        lean_dec(v_a_2959_);
                        if v___x_2960_ == 0 {
                            v___y_2906_ = v___y_2951_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v_val_2877_);
                            v_a_2870_ = v___x_2886_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_2886_);
                        lean_dec(v_val_2877_);
                        lean_dec_ref(v_env_2860_);
                        v_a_2961_ = lean_ctor_get(v___x_2958_, 0);
                        v_isSharedCheck_2968_ = (!lean_is_exclusive(v___x_2958_)) as u8;
                        if v_isSharedCheck_2968_ == 0 {
                            v___x_2963_ = v___x_2958_;
                            v_isShared_2964_ = v_isSharedCheck_2968_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2961_);
                            lean_dec(v___x_2958_);
                            v___x_2963_ = lean_box(0);
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
                        v_toImport_2969_ = lean_ctor_get(v_a_2882_, 0);
                        v_module_2970_ = lean_ctor_get(v_toImport_2969_, 0);
                        v___x_2971_ = 0;
                        lean_inc(v_module_2970_);
                        v___x_2972_ = l_Lean_mkModuleInitializationFunctionName(
                            v_module_2970_,
                            v___x_2953_,
                            v___x_2971_,
                        );
                        v___x_2973_ = lean_run_mod_init_core(v___x_2972_);
                        lean_dec_ref(v___x_2972_);
                        if lean_obj_tag(v___x_2973_) == 0 {
                            v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
                            lean_inc(v_a_2974_);
                            lean_dec_ref_known(v___x_2973_, 1);
                            v___x_2975_ = (lean_unbox(v_a_2974_) as u8);
                            lean_dec(v_a_2974_);
                            v___y_2932_ = v___y_2951_;
                            v___y_2933_ = v___x_2953_;
                            v_a_2934_ = v___x_2975_;
                            state = 8;
                            continue;
                        } else {
                            lean_dec(v___x_2953_);
                            lean_dec_ref(v___x_2886_);
                            lean_dec(v_val_2877_);
                            lean_dec_ref(v_env_2860_);
                            v_a_2976_ = lean_ctor_get(v___x_2973_, 0);
                            v_isSharedCheck_2983_ = (!lean_is_exclusive(v___x_2973_)) as u8;
                            if v_isSharedCheck_2983_ == 0 {
                                v___x_2978_ = v___x_2973_;
                                v_isShared_2979_ = v_isSharedCheck_2983_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_2976_);
                                lean_dec(v___x_2973_);
                                v___x_2978_ = lean_box(0);
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
                    v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
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
                    v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
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
    mut v_env_2991_: *mut LeanObject,
    mut v_opts_2992_: *mut LeanObject,
    mut v___x_2993_: *mut LeanObject,
    mut v_a_2994_: *mut LeanObject,
    mut v_as_2995_: *mut LeanObject,
    mut v_sz_2996_: *mut LeanObject,
    mut v_i_2997_: *mut LeanObject,
    mut v_b_2998_: *mut LeanObject,
    mut v___y_2999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6172__boxed_3000_: u8 = 0;
    let mut v_sz_boxed_3001_: usize = 0;
    let mut v_i_boxed_3002_: usize = 0;
    let mut v_res_3003_: *mut LeanObject = core::ptr::null_mut();
    v_a_6172__boxed_3000_ = (lean_unbox(v_a_2994_) as u8);
    v_sz_boxed_3001_ = lean_unbox_usize(v_sz_2996_);
    lean_dec(v_sz_2996_);
    v_i_boxed_3002_ = lean_unbox_usize(v_i_2997_);
    lean_dec(v_i_2997_);
    v_res_3003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4(v_env_2991_, v_opts_2992_, v___x_2993_, v_a_6172__boxed_3000_, v_as_2995_, v_sz_boxed_3001_, v_i_boxed_3002_, v_b_2998_);
    lean_dec_ref(v_as_2995_);
    lean_dec_ref(v___x_2993_);
    lean_dec_ref(v_opts_2992_);
    return v_res_3003_;
}
pub unsafe fn _init_l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__1()
-> *mut LeanObject {
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    v___x_3005_ = l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__0;
    v___x_3006_ = lean_mk_io_user_error(v___x_3005_);
    return v___x_3006_;
}
pub unsafe fn lean_run_init_attrs(
    mut v_env_3009_: *mut LeanObject,
    mut v_opts_3010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v___x_3017_: u8 = 0;
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3025_: usize = 0;
    let mut v___x_3026_: usize = 0;
    let mut v___x_3027_: u8 = 0;
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3031_: u8 = 0;
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3036_: u8 = 0;
    let mut v_unused_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3041_: u8 = 0;
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut v_isSharedCheck_3046_: u8 = 0;
    let mut v_a_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3050_: u8 = 0;
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3012_ = l_Lean_isInitializerExecutionEnabled();
                if lean_obj_tag(v___x_3012_) == 0 {
                    v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
                    v_isSharedCheck_3046_ = (!lean_is_exclusive(v___x_3012_)) as u8;
                    if v_isSharedCheck_3046_ == 0 {
                        v___x_3015_ = v___x_3012_;
                        v_isShared_3016_ = v_isSharedCheck_3046_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3013_);
                        lean_dec(v___x_3012_);
                        v___x_3015_ = lean_box(0);
                        v_isShared_3016_ = v_isSharedCheck_3046_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_opts_3010_);
                    lean_dec_ref(v_env_3009_);
                    v_a_3047_ = lean_ctor_get(v___x_3012_, 0);
                    v_isSharedCheck_3054_ = (!lean_is_exclusive(v___x_3012_)) as u8;
                    if v_isSharedCheck_3054_ == 0 {
                        v___x_3049_ = v___x_3012_;
                        v_isShared_3050_ = v_isSharedCheck_3054_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3047_);
                        lean_dec(v___x_3012_);
                        v___x_3049_ = lean_box(0);
                        v_isShared_3050_ = v_isSharedCheck_3054_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3017_ = (lean_unbox(v_a_3013_) as u8);
                if v___x_3017_ == 0 {
                    lean_dec(v_a_3013_);
                    lean_dec_ref(v_opts_3010_);
                    lean_dec_ref(v_env_3009_);
                    v___x_3018_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__1_once), _init_l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__1);
                    if v_isShared_3016_ == 0 {
                        lean_ctor_set_tag(v___x_3015_, 1);
                        lean_ctor_set(v___x_3015_, 0, v___x_3018_);
                        v___x_3020_ = v___x_3015_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
                        v___x_3020_ = v_reuseFailAlloc_3021_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3015_);
                    v___x_3022_ = l_Lean_Environment_header(v_env_3009_);
                    v_modules_3023_ = lean_ctor_get(v___x_3022_, 3);
                    lean_inc_ref(v_modules_3023_);
                    v___x_3024_ =
                        l___private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs___closed__2;
                    v_sz_3025_ = lean_array_size(v_modules_3023_);
                    v___x_3026_ = 0usize;
                    v___x_3027_ = (lean_unbox(v_a_3013_) as u8);
                    lean_dec(v_a_3013_);
                    v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_InitAttr_0__Lean_runInitAttrs_spec__4(v_env_3009_, v_opts_3010_, v___x_3022_, v___x_3027_, v_modules_3023_, v_sz_3025_, v___x_3026_, v___x_3024_);
                    lean_dec_ref(v_modules_3023_);
                    lean_dec_ref(v___x_3022_);
                    lean_dec_ref(v_opts_3010_);
                    if lean_obj_tag(v___x_3028_) == 0 {
                        v_isSharedCheck_3036_ = (!lean_is_exclusive(v___x_3028_)) as u8;
                        if v_isSharedCheck_3036_ == 0 {
                            v_unused_3037_ = lean_ctor_get(v___x_3028_, 0);
                            lean_dec(v_unused_3037_);
                            v___x_3030_ = v___x_3028_;
                            v_isShared_3031_ = v_isSharedCheck_3036_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_3028_);
                            v___x_3030_ = lean_box(0);
                            v_isShared_3031_ = v_isSharedCheck_3036_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3038_ = lean_ctor_get(v___x_3028_, 0);
                        v_isSharedCheck_3045_ = (!lean_is_exclusive(v___x_3028_)) as u8;
                        if v_isSharedCheck_3045_ == 0 {
                            v___x_3040_ = v___x_3028_;
                            v_isShared_3041_ = v_isSharedCheck_3045_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3038_);
                            lean_dec(v___x_3028_);
                            v___x_3040_ = lean_box(0);
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
                v___x_3032_ = lean_box(0);
                if v_isShared_3031_ == 0 {
                    lean_ctor_set(v___x_3030_, 0, v___x_3032_);
                    v___x_3034_ = v___x_3030_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
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
                    v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
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
                    v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
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
    mut v_env_3055_: *mut LeanObject,
    mut v_opts_3056_: *mut LeanObject,
    mut v_a_3057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3058_: *mut LeanObject = core::ptr::null_mut();
    v_res_3058_ = lean_run_init_attrs(v_env_3055_, v_opts_3056_);
    return v_res_3058_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_InitAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_NameMangling(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3590725331____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_interpretedModInits = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_interpretedModInits);
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_3980671908____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_regularInitAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_regularInitAttr);
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_regularInitAttr___regBuiltin_Lean_regularInitAttr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_initFn_00___x40_Lean_Compiler_InitAttr_1632222590____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_builtinInitAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_builtinInitAttr);
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_InitAttr_0__Lean_builtinInitAttr___regBuiltin_Lean_builtinInitAttr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_InitAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_registerInitAttr___auto__1 = _init_l_Lean_registerInitAttr___auto__1();
    lean_mark_persistent(l_Lean_registerInitAttr___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_InitAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_InfoTree_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_NameMangling(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_ModPkgExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_InitAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_InitAttr(builtin);
}
