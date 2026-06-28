// Lean compiler output
// Module: Lean.Server.Completion.EligibleHeaderDecls
// Imports: Lean.Meta.CompletionName Lean.Data.Lsp.LanguageFeatures Lean.AddDecl Lean.ProjFns Std.Sync.Mutex Lean.Linter.Deprecated
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Prelude::l_Lean_replaceRef;
use crate::r#gen::Lean::AddDecl::{initialize_Lean_AddDecl, runtime_initialize_Lean_AddDecl};
use crate::r#gen::Lean::Class::lean_is_class;
use crate::r#gen::Lean::Data::Lsp::LanguageFeatures::{
    initialize_Lean_Data_Lsp_LanguageFeatures, runtime_initialize_Lean_Data_Lsp_LanguageFeatures,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_forM___redArg, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_isCtor, l_Lean_ConstantInfo_isInductive, l_Lean_ConstantInfo_name,
    l_Lean_ConstantInfo_type, l_Lean_InductiveVal_numTypeFormers,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_constants, l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_isForall, l_Lean_Expr_isProp};
use crate::r#gen::Lean::Linter::Deprecated::{
    initialize_Lean_Linter_Deprecated, l_Lean_Linter_isDeprecated,
    runtime_initialize_Lean_Linter_Deprecated,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::CompletionName::{
    initialize_Lean_Meta_CompletionName, l_Lean_Meta_allowCompletion,
    runtime_initialize_Lean_Meta_CompletionName,
};
use crate::r#gen::Lean::OriginalConstKind::l_Lean_wasOriginallyTheorem;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ProjFns::{
    initialize_Lean_ProjFns, l_Lean_Environment_isProjectionFn, runtime_initialize_Lean_ProjFns,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::l_Std_DHashMap_Internal_AssocList_foldlM___redArg;
use crate::r#gen::Std::Sync::Mutex::{
    initialize_Std_Sync_Mutex, l_Std_Mutex_new___redArg, runtime_initialize_Std_Sync_Mutex,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_get, lean_st_ref_set};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_whnf;
use crate::lean_imports_rs::Std::Sync::Mutex::{lean_io_basemutex_lock, lean_io_basemutex_unlock};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Completion_getCompletionTagsForDecl___redArg___closed__0_value:
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
static mut l_Lean_Server_Completion_getCompletionTagsForDecl___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Completion_getCompletionTagsForDecl___redArg___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Server_Completion_getCompletionTagsForDecl___redArg___closed__1_value:
    LeanArrayObject<1> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Server_Completion_getCompletionTagsForDecl___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Completion_getCompletionTagsForDecl___redArg___closed__1_value
)
    as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0: u64 = 0;
static mut l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___closed__1: usize = 0;
pub unsafe fn l___private_Lean_Server_Completion_EligibleHeaderDecls_0__Lean_Server_Completion_initFn_00___x40_Lean_Server_Completion_EligibleHeaderDecls_1911833064____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    v___x_1392_ = lean_box(0);
    v___x_1393_ = l_Std_Mutex_new___redArg(v___x_1392_);
    v___x_1394_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1394_, 0, v___x_1393_);
    return v___x_1394_;
}
pub unsafe fn l___private_Lean_Server_Completion_EligibleHeaderDecls_0__Lean_Server_Completion_initFn_00___x40_Lean_Server_Completion_EligibleHeaderDecls_1911833064____hygCtx___hyg_2____boxed(
    mut v_a_1395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1396_: *mut LeanObject = core::ptr::null_mut();
    v_res_1396_ = l___private_Lean_Server_Completion_EligibleHeaderDecls_0__Lean_Server_Completion_initFn_00___x40_Lean_Server_Completion_EligibleHeaderDecls_1911833064____hygCtx___hyg_2_();
    return v_res_1396_;
}
pub unsafe fn l_Lean_isProjectionFn___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__0___redArg(
    mut v_declName_1397_: *mut LeanObject,
    mut v___y_1398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: u8 = 0;
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    v___x_1400_ = lean_st_ref_get(v___y_1398_);
    v_env_1401_ = lean_ctor_get(v___x_1400_, 0);
    lean_inc_ref(v_env_1401_);
    lean_dec(v___x_1400_);
    v___x_1402_ = l_Lean_Environment_isProjectionFn(v_env_1401_, v_declName_1397_);
    v___x_1403_ = lean_box((v___x_1402_) as usize);
    v___x_1404_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Lean_isProjectionFn___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__0___redArg___boxed(
    mut v_declName_1405_: *mut LeanObject,
    mut v___y_1406_: *mut LeanObject,
    mut v___y_1407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1408_: *mut LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_Lean_isProjectionFn___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__0___redArg(v_declName_1405_, v___y_1406_);
    lean_dec(v___y_1406_);
    return v_res_1408_;
}
pub unsafe fn l_Lean_isProjectionFn___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__0(
    mut v_declName_1409_: *mut LeanObject,
    mut v___y_1410_: *mut LeanObject,
    mut v___y_1411_: *mut LeanObject,
    mut v___y_1412_: *mut LeanObject,
    mut v___y_1413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    v___x_1415_ = l_Lean_isProjectionFn___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__0___redArg(v_declName_1409_, v___y_1413_);
    return v___x_1415_;
}
pub unsafe fn l_Lean_isProjectionFn___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__0___boxed(
    mut v_declName_1416_: *mut LeanObject,
    mut v___y_1417_: *mut LeanObject,
    mut v___y_1418_: *mut LeanObject,
    mut v___y_1419_: *mut LeanObject,
    mut v___y_1420_: *mut LeanObject,
    mut v___y_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1422_: *mut LeanObject = core::ptr::null_mut();
    v_res_1422_ =
        l_Lean_isProjectionFn___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__0(
            v_declName_1416_,
            v___y_1417_,
            v___y_1418_,
            v___y_1419_,
            v___y_1420_,
        );
    lean_dec(v___y_1420_);
    lean_dec_ref(v___y_1419_);
    lean_dec(v___y_1418_);
    lean_dec_ref(v___y_1417_);
    return v_res_1422_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    v___x_1423_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1423_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    v___x_1424_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0);
    v___x_1425_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1425_, 0, v___x_1424_);
    return v___x_1425_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    v___x_1426_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
    v___x_1427_ = lean_unsigned_to_nat(0);
    v___x_1428_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1428_, 0, v___x_1427_);
    lean_ctor_set(v___x_1428_, 1, v___x_1427_);
    lean_ctor_set(v___x_1428_, 2, v___x_1427_);
    lean_ctor_set(v___x_1428_, 3, v___x_1427_);
    lean_ctor_set(v___x_1428_, 4, v___x_1426_);
    lean_ctor_set(v___x_1428_, 5, v___x_1426_);
    lean_ctor_set(v___x_1428_, 6, v___x_1426_);
    lean_ctor_set(v___x_1428_, 7, v___x_1426_);
    lean_ctor_set(v___x_1428_, 8, v___x_1426_);
    lean_ctor_set(v___x_1428_, 9, v___x_1426_);
    return v___x_1428_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    v___x_1429_ = lean_unsigned_to_nat(32);
    v___x_1430_ = lean_mk_empty_array_with_capacity(v___x_1429_);
    v___x_1431_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1431_, 0, v___x_1430_);
    return v___x_1431_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1432_: usize = 0;
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    v___x_1432_ = 5usize;
    v___x_1433_ = lean_unsigned_to_nat(0);
    v___x_1434_ = lean_unsigned_to_nat(32);
    v___x_1435_ = lean_mk_empty_array_with_capacity(v___x_1434_);
    v___x_1436_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
    v___x_1437_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1437_, 0, v___x_1436_);
    lean_ctor_set(v___x_1437_, 1, v___x_1435_);
    lean_ctor_set(v___x_1437_, 2, v___x_1433_);
    lean_ctor_set(v___x_1437_, 3, v___x_1433_);
    lean_ctor_set_usize(v___x_1437_, 4, v___x_1432_);
    return v___x_1437_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    v___x_1438_ = lean_box(1);
    v___x_1439_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4);
    v___x_1440_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
    v___x_1441_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1441_, 0, v___x_1440_);
    lean_ctor_set(v___x_1441_, 1, v___x_1439_);
    lean_ctor_set(v___x_1441_, 2, v___x_1438_);
    return v___x_1441_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v___x_1443_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6;
    v___x_1444_ = l_Lean_stringToMessageData(v___x_1443_);
    return v___x_1444_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    v___x_1446_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8;
    v___x_1447_ = l_Lean_stringToMessageData(v___x_1446_);
    return v___x_1447_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    v___x_1449_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10;
    v___x_1450_ = l_Lean_stringToMessageData(v___x_1449_);
    return v___x_1450_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    v___x_1452_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12;
    v___x_1453_ = l_Lean_stringToMessageData(v___x_1452_);
    return v___x_1453_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    v___x_1455_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__14;
    v___x_1456_ = l_Lean_stringToMessageData(v___x_1455_);
    return v___x_1456_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    v___x_1458_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__16;
    v___x_1459_ = l_Lean_stringToMessageData(v___x_1458_);
    return v___x_1459_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    v___x_1461_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__18;
    v___x_1462_ = l_Lean_stringToMessageData(v___x_1461_);
    return v___x_1462_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(
    mut v_msg_1463_: *mut LeanObject,
    mut v_declHint_1464_: *mut LeanObject,
    mut v___y_1465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v_isExporting_1470_: u8 = 0;
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: u8 = 0;
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: u8 = 0;
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1524_: u8 = 0;
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1467_ = lean_st_ref_get(v___y_1465_);
                v_env_1468_ = lean_ctor_get(v___x_1467_, 0);
                lean_inc_ref(v_env_1468_);
                lean_dec(v___x_1467_);
                v___x_1469_ = l_Lean_Name_isAnonymous(v_declHint_1464_);
                if v___x_1469_ == 0 {
                    v_isExporting_1470_ = lean_ctor_get_uint8(
                        v_env_1468_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1470_ == 0 {
                        lean_dec_ref(v_env_1468_);
                        lean_dec(v_declHint_1464_);
                        v___x_1471_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1471_, 0, v_msg_1463_);
                        return v___x_1471_;
                    } else {
                        lean_inc_ref(v_env_1468_);
                        v___x_1472_ = l_Lean_Environment_setExporting(v_env_1468_, v___x_1469_);
                        lean_inc(v_declHint_1464_);
                        lean_inc_ref(v___x_1472_);
                        v___x_1473_ = l_Lean_Environment_contains(
                            v___x_1472_,
                            v_declHint_1464_,
                            v_isExporting_1470_,
                        );
                        if v___x_1473_ == 0 {
                            lean_dec_ref(v___x_1472_);
                            lean_dec_ref(v_env_1468_);
                            lean_dec(v_declHint_1464_);
                            v___x_1474_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1474_, 0, v_msg_1463_);
                            return v___x_1474_;
                        } else {
                            v___x_1475_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2);
                            v___x_1476_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
                            v___x_1477_ = l_Lean_Options_empty;
                            v___x_1478_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1478_, 0, v___x_1472_);
                            lean_ctor_set(v___x_1478_, 1, v___x_1475_);
                            lean_ctor_set(v___x_1478_, 2, v___x_1476_);
                            lean_ctor_set(v___x_1478_, 3, v___x_1477_);
                            lean_inc(v_declHint_1464_);
                            v___x_1479_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1464_, v___x_1469_);
                            v_c_1480_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1480_, 0, v___x_1478_);
                            lean_ctor_set(v_c_1480_, 1, v___x_1479_);
                            v___x_1481_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1468_,
                                v_declHint_1464_,
                            );
                            if lean_obj_tag(v___x_1481_) == 0 {
                                lean_dec_ref(v_env_1468_);
                                lean_dec(v_declHint_1464_);
                                v___x_1482_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
                                v___x_1483_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1483_, 0, v___x_1482_);
                                lean_ctor_set(v___x_1483_, 1, v_c_1480_);
                                v___x_1484_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
                                v___x_1485_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1485_, 0, v___x_1483_);
                                lean_ctor_set(v___x_1485_, 1, v___x_1484_);
                                v___x_1486_ = l_Lean_MessageData_note(v___x_1485_);
                                v___x_1487_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1487_, 0, v_msg_1463_);
                                lean_ctor_set(v___x_1487_, 1, v___x_1486_);
                                v___x_1488_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1488_, 0, v___x_1487_);
                                return v___x_1488_;
                            } else {
                                v_val_1489_ = lean_ctor_get(v___x_1481_, 0);
                                v_isSharedCheck_1524_ = (!lean_is_exclusive(v___x_1481_)) as u8;
                                if v_isSharedCheck_1524_ == 0 {
                                    v___x_1491_ = v___x_1481_;
                                    v_isShared_1492_ = v_isSharedCheck_1524_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1489_);
                                    lean_dec(v___x_1481_);
                                    v___x_1491_ = lean_box(0);
                                    v_isShared_1492_ = v_isSharedCheck_1524_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1468_);
                    lean_dec(v_declHint_1464_);
                    v___x_1525_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1525_, 0, v_msg_1463_);
                    return v___x_1525_;
                }
            }
            1 => {
                v___x_1493_ = lean_box(0);
                v___x_1494_ = l_Lean_Environment_header(v_env_1468_);
                lean_dec_ref(v_env_1468_);
                v___x_1495_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1494_);
                v_mod_1496_ = lean_array_get(v___x_1493_, v___x_1495_, v_val_1489_);
                lean_dec(v_val_1489_);
                lean_dec_ref(v___x_1495_);
                v___x_1497_ = l_Lean_isPrivateName(v_declHint_1464_);
                lean_dec(v_declHint_1464_);
                if v___x_1497_ == 0 {
                    v___x_1498_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
                    v___x_1499_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1499_, 0, v___x_1498_);
                    lean_ctor_set(v___x_1499_, 1, v_c_1480_);
                    v___x_1500_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
                    v___x_1501_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1501_, 0, v___x_1499_);
                    lean_ctor_set(v___x_1501_, 1, v___x_1500_);
                    v___x_1502_ = l_Lean_MessageData_ofName(v_mod_1496_);
                    v___x_1503_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1503_, 0, v___x_1501_);
                    lean_ctor_set(v___x_1503_, 1, v___x_1502_);
                    v___x_1504_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__15);
                    v___x_1505_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1505_, 0, v___x_1503_);
                    lean_ctor_set(v___x_1505_, 1, v___x_1504_);
                    v___x_1506_ = l_Lean_MessageData_note(v___x_1505_);
                    v___x_1507_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1507_, 0, v_msg_1463_);
                    lean_ctor_set(v___x_1507_, 1, v___x_1506_);
                    if v_isShared_1492_ == 0 {
                        lean_ctor_set_tag(v___x_1491_, 0);
                        lean_ctor_set(v___x_1491_, 0, v___x_1507_);
                        v___x_1509_ = v___x_1491_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
                        v___x_1509_ = v_reuseFailAlloc_1510_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1511_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
                    v___x_1512_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1512_, 0, v___x_1511_);
                    lean_ctor_set(v___x_1512_, 1, v_c_1480_);
                    v___x_1513_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__17);
                    v___x_1514_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1514_, 0, v___x_1512_);
                    lean_ctor_set(v___x_1514_, 1, v___x_1513_);
                    v___x_1515_ = l_Lean_MessageData_ofName(v_mod_1496_);
                    v___x_1516_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1516_, 0, v___x_1514_);
                    lean_ctor_set(v___x_1516_, 1, v___x_1515_);
                    v___x_1517_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__19);
                    v___x_1518_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1518_, 0, v___x_1516_);
                    lean_ctor_set(v___x_1518_, 1, v___x_1517_);
                    v___x_1519_ = l_Lean_MessageData_note(v___x_1518_);
                    v___x_1520_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1520_, 0, v_msg_1463_);
                    lean_ctor_set(v___x_1520_, 1, v___x_1519_);
                    if v_isShared_1492_ == 0 {
                        lean_ctor_set_tag(v___x_1491_, 0);
                        lean_ctor_set(v___x_1491_, 0, v___x_1520_);
                        v___x_1522_ = v___x_1491_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
                        v___x_1522_ = v_reuseFailAlloc_1523_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1509_;
            }
            3 => {
                return v___x_1522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(
    mut v_msg_1526_: *mut LeanObject,
    mut v_declHint_1527_: *mut LeanObject,
    mut v___y_1528_: *mut LeanObject,
    mut v___y_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1530_: *mut LeanObject = core::ptr::null_mut();
    v_res_1530_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1526_, v_declHint_1527_, v___y_1528_);
    lean_dec(v___y_1528_);
    return v_res_1530_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6(
    mut v_msg_1531_: *mut LeanObject,
    mut v_declHint_1532_: *mut LeanObject,
    mut v___y_1533_: *mut LeanObject,
    mut v___y_1534_: *mut LeanObject,
    mut v___y_1535_: *mut LeanObject,
    mut v___y_1536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1538_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1531_, v_declHint_1532_, v___y_1536_);
                v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
                v_isSharedCheck_1548_ = (!lean_is_exclusive(v___x_1538_)) as u8;
                if v_isSharedCheck_1548_ == 0 {
                    v___x_1541_ = v___x_1538_;
                    v_isShared_1542_ = v_isSharedCheck_1548_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1539_);
                    lean_dec(v___x_1538_);
                    v___x_1541_ = lean_box(0);
                    v_isShared_1542_ = v_isSharedCheck_1548_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1543_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1544_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1544_, 0, v___x_1543_);
                lean_ctor_set(v___x_1544_, 1, v_a_1539_);
                if v_isShared_1542_ == 0 {
                    lean_ctor_set(v___x_1541_, 0, v___x_1544_);
                    v___x_1546_ = v___x_1541_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
                    v___x_1546_ = v_reuseFailAlloc_1547_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6___boxed(
    mut v_msg_1549_: *mut LeanObject,
    mut v_declHint_1550_: *mut LeanObject,
    mut v___y_1551_: *mut LeanObject,
    mut v___y_1552_: *mut LeanObject,
    mut v___y_1553_: *mut LeanObject,
    mut v___y_1554_: *mut LeanObject,
    mut v___y_1555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1556_: *mut LeanObject = core::ptr::null_mut();
    v_res_1556_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6(v_msg_1549_, v_declHint_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
    lean_dec(v___y_1554_);
    lean_dec_ref(v___y_1553_);
    lean_dec(v___y_1552_);
    lean_dec_ref(v___y_1551_);
    return v_res_1556_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9_spec__10(
    mut v_msgData_1557_: *mut LeanObject,
    mut v___y_1558_: *mut LeanObject,
    mut v___y_1559_: *mut LeanObject,
    mut v___y_1560_: *mut LeanObject,
    mut v___y_1561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    v___x_1563_ = lean_st_ref_get(v___y_1561_);
    v_env_1564_ = lean_ctor_get(v___x_1563_, 0);
    lean_inc_ref(v_env_1564_);
    lean_dec(v___x_1563_);
    v___x_1565_ = lean_st_ref_get(v___y_1559_);
    v_mctx_1566_ = lean_ctor_get(v___x_1565_, 0);
    lean_inc_ref(v_mctx_1566_);
    lean_dec(v___x_1565_);
    v_lctx_1567_ = lean_ctor_get(v___y_1558_, 2);
    v_options_1568_ = lean_ctor_get(v___y_1560_, 2);
    lean_inc_ref(v_options_1568_);
    lean_inc_ref(v_lctx_1567_);
    v___x_1569_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1569_, 0, v_env_1564_);
    lean_ctor_set(v___x_1569_, 1, v_mctx_1566_);
    lean_ctor_set(v___x_1569_, 2, v_lctx_1567_);
    lean_ctor_set(v___x_1569_, 3, v_options_1568_);
    v___x_1570_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1570_, 0, v___x_1569_);
    lean_ctor_set(v___x_1570_, 1, v_msgData_1557_);
    v___x_1571_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1571_, 0, v___x_1570_);
    return v___x_1571_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9_spec__10___boxed(
    mut v_msgData_1572_: *mut LeanObject,
    mut v___y_1573_: *mut LeanObject,
    mut v___y_1574_: *mut LeanObject,
    mut v___y_1575_: *mut LeanObject,
    mut v___y_1576_: *mut LeanObject,
    mut v___y_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1578_: *mut LeanObject = core::ptr::null_mut();
    v_res_1578_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9_spec__10(v_msgData_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
    lean_dec(v___y_1576_);
    lean_dec_ref(v___y_1575_);
    lean_dec(v___y_1574_);
    lean_dec_ref(v___y_1573_);
    return v_res_1578_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(
    mut v_msg_1579_: *mut LeanObject,
    mut v___y_1580_: *mut LeanObject,
    mut v___y_1581_: *mut LeanObject,
    mut v___y_1582_: *mut LeanObject,
    mut v___y_1583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1590_: u8 = 0;
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1585_ = lean_ctor_get(v___y_1582_, 5);
                v___x_1586_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9_spec__10(v_msg_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
                v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
                v_isSharedCheck_1595_ = (!lean_is_exclusive(v___x_1586_)) as u8;
                if v_isSharedCheck_1595_ == 0 {
                    v___x_1589_ = v___x_1586_;
                    v_isShared_1590_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1587_);
                    lean_dec(v___x_1586_);
                    v___x_1589_ = lean_box(0);
                    v_isShared_1590_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1585_);
                v___x_1591_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1591_, 0, v_ref_1585_);
                lean_ctor_set(v___x_1591_, 1, v_a_1587_);
                if v_isShared_1590_ == 0 {
                    lean_ctor_set_tag(v___x_1589_, 1);
                    lean_ctor_set(v___x_1589_, 0, v___x_1591_);
                    v___x_1593_ = v___x_1589_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
                    v___x_1593_ = v_reuseFailAlloc_1594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(
    mut v_msg_1596_: *mut LeanObject,
    mut v___y_1597_: *mut LeanObject,
    mut v___y_1598_: *mut LeanObject,
    mut v___y_1599_: *mut LeanObject,
    mut v___y_1600_: *mut LeanObject,
    mut v___y_1601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1602_: *mut LeanObject = core::ptr::null_mut();
    v_res_1602_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
    lean_dec(v___y_1600_);
    lean_dec_ref(v___y_1599_);
    lean_dec(v___y_1598_);
    lean_dec_ref(v___y_1597_);
    return v_res_1602_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(
    mut v_ref_1603_: *mut LeanObject,
    mut v_msg_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
    mut v___y_1606_: *mut LeanObject,
    mut v___y_1607_: *mut LeanObject,
    mut v___y_1608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1622_: u8 = 0;
    let mut v_cancelTk_x3f_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1624_: u8 = 0;
    let mut v_inheritedTraceOptions_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1610_ = lean_ctor_get(v___y_1607_, 0);
    v_fileMap_1611_ = lean_ctor_get(v___y_1607_, 1);
    v_options_1612_ = lean_ctor_get(v___y_1607_, 2);
    v_currRecDepth_1613_ = lean_ctor_get(v___y_1607_, 3);
    v_maxRecDepth_1614_ = lean_ctor_get(v___y_1607_, 4);
    v_ref_1615_ = lean_ctor_get(v___y_1607_, 5);
    v_currNamespace_1616_ = lean_ctor_get(v___y_1607_, 6);
    v_openDecls_1617_ = lean_ctor_get(v___y_1607_, 7);
    v_initHeartbeats_1618_ = lean_ctor_get(v___y_1607_, 8);
    v_maxHeartbeats_1619_ = lean_ctor_get(v___y_1607_, 9);
    v_quotContext_1620_ = lean_ctor_get(v___y_1607_, 10);
    v_currMacroScope_1621_ = lean_ctor_get(v___y_1607_, 11);
    v_diag_1622_ = lean_ctor_get_uint8(
        v___y_1607_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1623_ = lean_ctor_get(v___y_1607_, 12);
    v_suppressElabErrors_1624_ = lean_ctor_get_uint8(
        v___y_1607_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1625_ = lean_ctor_get(v___y_1607_, 13);
    v_ref_1626_ = l_Lean_replaceRef(v_ref_1603_, v_ref_1615_);
    lean_inc_ref(v_inheritedTraceOptions_1625_);
    lean_inc(v_cancelTk_x3f_1623_);
    lean_inc(v_currMacroScope_1621_);
    lean_inc(v_quotContext_1620_);
    lean_inc(v_maxHeartbeats_1619_);
    lean_inc(v_initHeartbeats_1618_);
    lean_inc(v_openDecls_1617_);
    lean_inc(v_currNamespace_1616_);
    lean_inc(v_maxRecDepth_1614_);
    lean_inc(v_currRecDepth_1613_);
    lean_inc_ref(v_options_1612_);
    lean_inc_ref(v_fileMap_1611_);
    lean_inc_ref(v_fileName_1610_);
    v___x_1627_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1627_, 0, v_fileName_1610_);
    lean_ctor_set(v___x_1627_, 1, v_fileMap_1611_);
    lean_ctor_set(v___x_1627_, 2, v_options_1612_);
    lean_ctor_set(v___x_1627_, 3, v_currRecDepth_1613_);
    lean_ctor_set(v___x_1627_, 4, v_maxRecDepth_1614_);
    lean_ctor_set(v___x_1627_, 5, v_ref_1626_);
    lean_ctor_set(v___x_1627_, 6, v_currNamespace_1616_);
    lean_ctor_set(v___x_1627_, 7, v_openDecls_1617_);
    lean_ctor_set(v___x_1627_, 8, v_initHeartbeats_1618_);
    lean_ctor_set(v___x_1627_, 9, v_maxHeartbeats_1619_);
    lean_ctor_set(v___x_1627_, 10, v_quotContext_1620_);
    lean_ctor_set(v___x_1627_, 11, v_currMacroScope_1621_);
    lean_ctor_set(v___x_1627_, 12, v_cancelTk_x3f_1623_);
    lean_ctor_set(v___x_1627_, 13, v_inheritedTraceOptions_1625_);
    lean_ctor_set_uint8(
        v___x_1627_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1622_,
    );
    lean_ctor_set_uint8(
        v___x_1627_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1624_,
    );
    v___x_1628_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1604_, v___y_1605_, v___y_1606_, v___x_1627_, v___y_1608_);
    lean_dec_ref_known(v___x_1627_, 14);
    return v___x_1628_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_ref_1629_: *mut LeanObject,
    mut v_msg_1630_: *mut LeanObject,
    mut v___y_1631_: *mut LeanObject,
    mut v___y_1632_: *mut LeanObject,
    mut v___y_1633_: *mut LeanObject,
    mut v___y_1634_: *mut LeanObject,
    mut v___y_1635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1636_: *mut LeanObject = core::ptr::null_mut();
    v_res_1636_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1629_, v_msg_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
    lean_dec(v___y_1634_);
    lean_dec_ref(v___y_1633_);
    lean_dec(v___y_1632_);
    lean_dec_ref(v___y_1631_);
    lean_dec(v_ref_1629_);
    return v_res_1636_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_ref_1637_: *mut LeanObject,
    mut v_msg_1638_: *mut LeanObject,
    mut v_declHint_1639_: *mut LeanObject,
    mut v___y_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
    mut v___y_1642_: *mut LeanObject,
    mut v___y_1643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    v___x_1645_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6(v_msg_1638_, v_declHint_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
    v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
    lean_inc(v_a_1646_);
    lean_dec_ref(v___x_1645_);
    v___x_1647_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1637_, v_a_1646_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
    return v___x_1647_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_ref_1648_: *mut LeanObject,
    mut v_msg_1649_: *mut LeanObject,
    mut v_declHint_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
    mut v___y_1652_: *mut LeanObject,
    mut v___y_1653_: *mut LeanObject,
    mut v___y_1654_: *mut LeanObject,
    mut v___y_1655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1656_: *mut LeanObject = core::ptr::null_mut();
    v_res_1656_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_1648_, v_msg_1649_, v_declHint_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
    lean_dec(v___y_1654_);
    lean_dec_ref(v___y_1653_);
    lean_dec(v___y_1652_);
    lean_dec_ref(v___y_1651_);
    lean_dec(v_ref_1648_);
    return v_res_1656_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    v___x_1658_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__0;
    v___x_1659_ = l_Lean_stringToMessageData(v___x_1658_);
    return v___x_1659_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    v___x_1661_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__2;
    v___x_1662_ = l_Lean_stringToMessageData(v___x_1661_);
    return v___x_1662_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg(
    mut v_ref_1663_: *mut LeanObject,
    mut v_constName_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: u8 = 0;
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    v___x_1670_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__1);
    v___x_1671_ = 0;
    lean_inc(v_constName_1664_);
    v___x_1672_ = l_Lean_MessageData_ofConstName(v_constName_1664_, v___x_1671_);
    v___x_1673_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1673_, 0, v___x_1670_);
    lean_ctor_set(v___x_1673_, 1, v___x_1672_);
    v___x_1674_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___closed__3);
    v___x_1675_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1675_, 0, v___x_1673_);
    lean_ctor_set(v___x_1675_, 1, v___x_1674_);
    v___x_1676_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_1663_, v___x_1675_, v_constName_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
    return v___x_1676_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_ref_1677_: *mut LeanObject,
    mut v_constName_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
    mut v___y_1681_: *mut LeanObject,
    mut v___y_1682_: *mut LeanObject,
    mut v___y_1683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1684_: *mut LeanObject = core::ptr::null_mut();
    v_res_1684_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg(v_ref_1677_, v_constName_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
    lean_dec(v___y_1682_);
    lean_dec_ref(v___y_1681_);
    lean_dec(v___y_1680_);
    lean_dec_ref(v___y_1679_);
    lean_dec(v_ref_1677_);
    return v_res_1684_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2___redArg(
    mut v_constName_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
    mut v___y_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1691_ = lean_ctor_get(v___y_1688_, 5);
    v___x_1692_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg(v_ref_1691_, v_constName_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
    return v___x_1692_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_constName_1693_: *mut LeanObject,
    mut v___y_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1699_: *mut LeanObject = core::ptr::null_mut();
    v_res_1699_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2___redArg(v_constName_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
    lean_dec(v___y_1697_);
    lean_dec_ref(v___y_1696_);
    lean_dec(v___y_1695_);
    lean_dec_ref(v___y_1694_);
    return v_res_1699_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1(
    mut v_constName_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
    mut v___y_1702_: *mut LeanObject,
    mut v___y_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: u8 = 0;
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1714_: u8 = 0;
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1706_ = lean_st_ref_get(v___y_1704_);
                v_env_1707_ = lean_ctor_get(v___x_1706_, 0);
                lean_inc_ref(v_env_1707_);
                lean_dec(v___x_1706_);
                v___x_1708_ = 0;
                lean_inc(v_constName_1700_);
                v___x_1709_ =
                    l_Lean_Environment_find_x3f(v_env_1707_, v_constName_1700_, v___x_1708_);
                if lean_obj_tag(v___x_1709_) == 0 {
                    v___x_1710_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2___redArg(v_constName_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
                    return v___x_1710_;
                } else {
                    lean_dec(v_constName_1700_);
                    v_val_1711_ = lean_ctor_get(v___x_1709_, 0);
                    v_isSharedCheck_1718_ = (!lean_is_exclusive(v___x_1709_)) as u8;
                    if v_isSharedCheck_1718_ == 0 {
                        v___x_1713_ = v___x_1709_;
                        v_isShared_1714_ = v_isSharedCheck_1718_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1711_);
                        lean_dec(v___x_1709_);
                        v___x_1713_ = lean_box(0);
                        v_isShared_1714_ = v_isSharedCheck_1718_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1714_ == 0 {
                    lean_ctor_set_tag(v___x_1713_, 0);
                    v___x_1716_ = v___x_1713_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_val_1711_);
                    v___x_1716_ = v_reuseFailAlloc_1717_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1___boxed(
    mut v_constName_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
    mut v___y_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1725_: *mut LeanObject = core::ptr::null_mut();
    v_res_1725_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1(v_constName_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
    lean_dec(v___y_1723_);
    lean_dec_ref(v___y_1722_);
    lean_dec(v___y_1721_);
    lean_dec_ref(v___y_1720_);
    return v_res_1725_;
}
pub unsafe fn l_List_allM___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__2(
    mut v___x_1726_: u8,
    mut v_x_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
    mut v___y_1730_: *mut LeanObject,
    mut v___y_1731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1742_: u8 = 0;
    let mut v___y_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1745_: u8 = 0;
    let mut v_val_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: u8 = 0;
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1759_: u8 = 0;
    let mut v_a_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1727_) == 0 {
                    v___x_1733_ = 1;
                    v___x_1734_ = lean_box((v___x_1733_) as usize);
                    v___x_1735_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1735_, 0, v___x_1734_);
                    return v___x_1735_;
                } else {
                    v_head_1736_ = lean_ctor_get(v_x_1727_, 0);
                    lean_inc(v_head_1736_);
                    v_tail_1737_ = lean_ctor_get(v_x_1727_, 1);
                    lean_inc(v_tail_1737_);
                    lean_dec_ref_known(v_x_1727_, 2);
                    v___x_1738_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1(v_head_1736_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
                    if lean_obj_tag(v___x_1738_) == 0 {
                        v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
                        v_isSharedCheck_1759_ = (!lean_is_exclusive(v___x_1738_)) as u8;
                        if v_isSharedCheck_1759_ == 0 {
                            v___x_1741_ = v___x_1738_;
                            v_isShared_1742_ = v_isSharedCheck_1759_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1739_);
                            lean_dec(v___x_1738_);
                            v___x_1741_ = lean_box(0);
                            v_isShared_1742_ = v_isSharedCheck_1759_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_tail_1737_);
                        v_a_1760_ = lean_ctor_get(v___x_1738_, 0);
                        v_isSharedCheck_1767_ = (!lean_is_exclusive(v___x_1738_)) as u8;
                        if v_isSharedCheck_1767_ == 0 {
                            v___x_1762_ = v___x_1738_;
                            v_isShared_1763_ = v_isSharedCheck_1767_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1760_);
                            lean_dec(v___x_1738_);
                            v___x_1762_ = lean_box(0);
                            v_isShared_1763_ = v_isSharedCheck_1767_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1739_) == 6 {
                    v_val_1747_ = lean_ctor_get(v_a_1739_, 0);
                    lean_inc_ref(v_val_1747_);
                    lean_dec_ref_known(v_a_1739_, 1);
                    v_numFields_1748_ = lean_ctor_get(v_val_1747_, 4);
                    lean_inc(v_numFields_1748_);
                    lean_dec_ref(v_val_1747_);
                    v___x_1749_ = lean_unsigned_to_nat(0);
                    v___x_1750_ = lean_nat_dec_eq(v_numFields_1748_, v___x_1749_);
                    lean_dec(v_numFields_1748_);
                    v___x_1751_ = lean_box((v___x_1750_) as usize);
                    if v_isShared_1742_ == 0 {
                        lean_ctor_set(v___x_1741_, 0, v___x_1751_);
                        v___x_1753_ = v___x_1741_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
                        v___x_1753_ = v_reuseFailAlloc_1754_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1739_);
                    v___x_1755_ = lean_box((v___x_1726_) as usize);
                    if v_isShared_1742_ == 0 {
                        lean_ctor_set(v___x_1741_, 0, v___x_1755_);
                        v___x_1757_ = v___x_1741_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
                        v___x_1757_ = v_reuseFailAlloc_1758_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_a_1745_ == 0 {
                    lean_dec(v_tail_1737_);
                    return v___y_1744_;
                } else {
                    lean_dec_ref(v___y_1744_);
                    v_x_1727_ = v_tail_1737_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                v___y_1744_ = v___x_1753_;
                v_a_1745_ = v___x_1750_;
                state = 2;
                continue;
            }
            4 => {
                v___y_1744_ = v___x_1757_;
                v_a_1745_ = v___x_1726_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_1763_ == 0 {
                    v___x_1765_ = v___x_1762_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
                    v___x_1765_ = v_reuseFailAlloc_1766_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_allM___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__2___boxed(
    mut v___x_1768_: *mut LeanObject,
    mut v_x_1769_: *mut LeanObject,
    mut v___y_1770_: *mut LeanObject,
    mut v___y_1771_: *mut LeanObject,
    mut v___y_1772_: *mut LeanObject,
    mut v___y_1773_: *mut LeanObject,
    mut v___y_1774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7419__boxed_1775_: u8 = 0;
    let mut v_res_1776_: *mut LeanObject = core::ptr::null_mut();
    v___x_7419__boxed_1775_ = (lean_unbox(v___x_1768_) as u8);
    v_res_1776_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__2(v___x_7419__boxed_1775_, v_x_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
    lean_dec(v___y_1773_);
    lean_dec_ref(v___y_1772_);
    lean_dec(v___y_1771_);
    lean_dec_ref(v___y_1770_);
    return v_res_1776_;
}
pub unsafe fn l_Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1(
    mut v_declName_1777_: *mut LeanObject,
    mut v___y_1778_: *mut LeanObject,
    mut v___y_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1787_: u8 = 0;
    let mut v_val_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isRec_1793_: u8 = 0;
    let mut v_isUnsafe_1794_: u8 = 0;
    let mut v_type_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: u8 = 0;
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: u8 = 0;
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut v_a_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1843_: u8 = 0;
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1847_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1783_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1(v_declName_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
                if lean_obj_tag(v___x_1783_) == 0 {
                    v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
                    v_isSharedCheck_1839_ = (!lean_is_exclusive(v___x_1783_)) as u8;
                    if v_isSharedCheck_1839_ == 0 {
                        v___x_1786_ = v___x_1783_;
                        v_isShared_1787_ = v_isSharedCheck_1839_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1784_);
                        lean_dec(v___x_1783_);
                        v___x_1786_ = lean_box(0);
                        v_isShared_1787_ = v_isSharedCheck_1839_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1840_ = lean_ctor_get(v___x_1783_, 0);
                    v_isSharedCheck_1847_ = (!lean_is_exclusive(v___x_1783_)) as u8;
                    if v_isSharedCheck_1847_ == 0 {
                        v___x_1842_ = v___x_1783_;
                        v_isShared_1843_ = v_isSharedCheck_1847_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_1840_);
                        lean_dec(v___x_1783_);
                        v___x_1842_ = lean_box(0);
                        v_isShared_1843_ = v_isSharedCheck_1847_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1784_) == 5 {
                    v_val_1788_ = lean_ctor_get(v_a_1784_, 0);
                    lean_inc_ref(v_val_1788_);
                    lean_dec_ref_known(v_a_1784_, 1);
                    v_toConstantVal_1789_ = lean_ctor_get(v_val_1788_, 0);
                    v_numParams_1790_ = lean_ctor_get(v_val_1788_, 1);
                    lean_inc(v_numParams_1790_);
                    v_numIndices_1791_ = lean_ctor_get(v_val_1788_, 2);
                    lean_inc(v_numIndices_1791_);
                    v_ctors_1792_ = lean_ctor_get(v_val_1788_, 4);
                    lean_inc(v_ctors_1792_);
                    v_isRec_1793_ = lean_ctor_get_uint8(
                        v_val_1788_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                    );
                    v_isUnsafe_1794_ = lean_ctor_get_uint8(
                        v_val_1788_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                    );
                    v_type_1795_ = lean_ctor_get(v_toConstantVal_1789_, 2);
                    v___x_1796_ = l_Lean_Expr_isProp(v_type_1795_);
                    if v___x_1796_ == 0 {
                        v___x_1797_ = l_Lean_InductiveVal_numTypeFormers(v_val_1788_);
                        lean_dec_ref(v_val_1788_);
                        v___x_1798_ = lean_unsigned_to_nat(1);
                        v___x_1799_ = lean_nat_dec_eq(v___x_1797_, v___x_1798_);
                        lean_dec(v___x_1797_);
                        if v___x_1799_ == 0 {
                            lean_dec(v_ctors_1792_);
                            lean_dec(v_numIndices_1791_);
                            lean_dec(v_numParams_1790_);
                            v___x_1800_ = lean_box((v___x_1799_) as usize);
                            if v_isShared_1787_ == 0 {
                                lean_ctor_set(v___x_1786_, 0, v___x_1800_);
                                v___x_1802_ = v___x_1786_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
                                v___x_1802_ = v_reuseFailAlloc_1803_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_1804_ = lean_unsigned_to_nat(0);
                            v___x_1805_ = lean_nat_dec_eq(v_numIndices_1791_, v___x_1804_);
                            lean_dec(v_numIndices_1791_);
                            if v___x_1805_ == 0 {
                                lean_dec(v_ctors_1792_);
                                lean_dec(v_numParams_1790_);
                                v___x_1806_ = lean_box((v___x_1805_) as usize);
                                if v_isShared_1787_ == 0 {
                                    lean_ctor_set(v___x_1786_, 0, v___x_1806_);
                                    v___x_1808_ = v___x_1786_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
                                    v___x_1808_ = v_reuseFailAlloc_1809_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v___x_1810_ = lean_nat_dec_eq(v_numParams_1790_, v___x_1804_);
                                lean_dec(v_numParams_1790_);
                                if v___x_1810_ == 0 {
                                    lean_dec(v_ctors_1792_);
                                    v___x_1811_ = lean_box((v___x_1810_) as usize);
                                    if v_isShared_1787_ == 0 {
                                        lean_ctor_set(v___x_1786_, 0, v___x_1811_);
                                        v___x_1813_ = v___x_1786_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
                                        v___x_1813_ = v_reuseFailAlloc_1814_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    v___x_1815_ = l_List_isEmpty___redArg(v_ctors_1792_);
                                    if v___x_1815_ == 0 {
                                        if v_isRec_1793_ == 0 {
                                            if v_isUnsafe_1794_ == 0 {
                                                lean_del_object(v___x_1786_);
                                                v___x_1816_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__2(v_isUnsafe_1794_, v_ctors_1792_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
                                                return v___x_1816_;
                                            } else {
                                                lean_dec(v_ctors_1792_);
                                                v___x_1817_ = lean_box((v_isRec_1793_) as usize);
                                                if v_isShared_1787_ == 0 {
                                                    lean_ctor_set(v___x_1786_, 0, v___x_1817_);
                                                    v___x_1819_ = v___x_1786_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_1820_ =
                                                        lean_alloc_ctor(0, 1, (0) as u32);
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_1820_,
                                                        0,
                                                        v___x_1817_,
                                                    );
                                                    v___x_1819_ = v_reuseFailAlloc_1820_;
                                                    state = 5;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_ctors_1792_);
                                            v___x_1821_ = lean_box((v___x_1815_) as usize);
                                            if v_isShared_1787_ == 0 {
                                                lean_ctor_set(v___x_1786_, 0, v___x_1821_);
                                                v___x_1823_ = v___x_1786_;
                                                state = 6;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_1824_ =
                                                    lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(
                                                    v_reuseFailAlloc_1824_,
                                                    0,
                                                    v___x_1821_,
                                                );
                                                v___x_1823_ = v_reuseFailAlloc_1824_;
                                                state = 6;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_ctors_1792_);
                                        v___x_1825_ = lean_box((v___x_1796_) as usize);
                                        if v_isShared_1787_ == 0 {
                                            lean_ctor_set(v___x_1786_, 0, v___x_1825_);
                                            v___x_1827_ = v___x_1786_;
                                            state = 7;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1828_ =
                                                lean_alloc_ctor(0, 1, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
                                            v___x_1827_ = v_reuseFailAlloc_1828_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_ctors_1792_);
                        lean_dec(v_numIndices_1791_);
                        lean_dec(v_numParams_1790_);
                        lean_dec_ref(v_val_1788_);
                        v___x_1829_ = 0;
                        v___x_1830_ = lean_box((v___x_1829_) as usize);
                        if v_isShared_1787_ == 0 {
                            lean_ctor_set(v___x_1786_, 0, v___x_1830_);
                            v___x_1832_ = v___x_1786_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
                            v___x_1832_ = v_reuseFailAlloc_1833_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1784_);
                    v___x_1834_ = 0;
                    v___x_1835_ = lean_box((v___x_1834_) as usize);
                    if v_isShared_1787_ == 0 {
                        lean_ctor_set(v___x_1786_, 0, v___x_1835_);
                        v___x_1837_ = v___x_1786_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
                        v___x_1837_ = v_reuseFailAlloc_1838_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1802_;
            }
            3 => {
                return v___x_1808_;
            }
            4 => {
                return v___x_1813_;
            }
            5 => {
                return v___x_1819_;
            }
            6 => {
                return v___x_1823_;
            }
            7 => {
                return v___x_1827_;
            }
            8 => {
                return v___x_1832_;
            }
            9 => {
                return v___x_1837_;
            }
            10 => {
                if v_isShared_1843_ == 0 {
                    v___x_1845_ = v___x_1842_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
                    v___x_1845_ = v_reuseFailAlloc_1846_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1845_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1___boxed(
    mut v_declName_1848_: *mut LeanObject,
    mut v___y_1849_: *mut LeanObject,
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
    mut v___y_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1854_: *mut LeanObject = core::ptr::null_mut();
    v_res_1854_ =
        l_Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1(
            v_declName_1848_,
            v___y_1849_,
            v___y_1850_,
            v___y_1851_,
            v___y_1852_,
        );
    lean_dec(v___y_1852_);
    lean_dec_ref(v___y_1851_);
    lean_dec(v___y_1850_);
    lean_dec_ref(v___y_1849_);
    return v_res_1854_;
}
pub unsafe fn l_Lean_Server_Completion_getCompletionKindForDecl(
    mut v_constInfo_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
    mut v_a_1857_: *mut LeanObject,
    mut v_a_1858_: *mut LeanObject,
    mut v_a_1859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: u8 = 0;
    let mut v_env_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: u8 = 0;
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1871_: u8 = 0;
    let mut v___x_1872_: u8 = 0;
    let mut v_fileName_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1884_: u8 = 0;
    let mut v_cancelTk_x3f_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1886_: u8 = 0;
    let mut v_inheritedTraceOptions_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1896_: u8 = 0;
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: u8 = 0;
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1907_: u8 = 0;
    let mut v_a_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1911_: u8 = 0;
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1915_: u8 = 0;
    let mut v___x_1916_: u8 = 0;
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v___x_1922_: u8 = 0;
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: u8 = 0;
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1931_: u8 = 0;
    let mut v___x_1932_: u8 = 0;
    let mut v___x_1933_: u8 = 0;
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: u8 = 0;
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut v_a_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut v___x_1952_: u8 = 0;
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1861_ = lean_st_ref_get(v_a_1859_);
                v___x_1862_ = l_Lean_ConstantInfo_isCtor(v_constInfo_1855_);
                if v___x_1862_ == 0 {
                    v_env_1863_ = lean_ctor_get(v___x_1861_, 0);
                    lean_inc_ref(v_env_1863_);
                    lean_dec(v___x_1861_);
                    v___x_1864_ = l_Lean_ConstantInfo_isInductive(v_constInfo_1855_);
                    if v___x_1864_ == 0 {
                        v___x_1865_ = l_Lean_ConstantInfo_name(v_constInfo_1855_);
                        lean_inc(v___x_1865_);
                        v___x_1866_ = l_Lean_wasOriginallyTheorem(v_env_1863_, v___x_1865_);
                        if v___x_1866_ == 0 {
                            v___x_1867_ = l_Lean_isProjectionFn___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__0___redArg(v___x_1865_, v_a_1859_);
                            v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
                            v_isSharedCheck_1921_ = (!lean_is_exclusive(v___x_1867_)) as u8;
                            if v_isSharedCheck_1921_ == 0 {
                                v___x_1870_ = v___x_1867_;
                                v_isShared_1871_ = v_isSharedCheck_1921_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1868_);
                                lean_dec(v___x_1867_);
                                v___x_1870_ = lean_box(0);
                                v_isShared_1871_ = v_isSharedCheck_1921_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_1865_);
                            v___x_1922_ = 22;
                            v___x_1923_ = lean_box((v___x_1922_) as usize);
                            v___x_1924_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1924_, 0, v___x_1923_);
                            return v___x_1924_;
                        }
                    } else {
                        v___x_1925_ = l_Lean_ConstantInfo_name(v_constInfo_1855_);
                        lean_inc(v___x_1925_);
                        v___x_1926_ = lean_is_class(v_env_1863_, v___x_1925_);
                        if v___x_1926_ == 0 {
                            v___x_1927_ = l_Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1(v___x_1925_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
                            if lean_obj_tag(v___x_1927_) == 0 {
                                v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
                                v_isSharedCheck_1943_ = (!lean_is_exclusive(v___x_1927_)) as u8;
                                if v_isSharedCheck_1943_ == 0 {
                                    v___x_1930_ = v___x_1927_;
                                    v_isShared_1931_ = v_isSharedCheck_1943_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_1928_);
                                    lean_dec(v___x_1927_);
                                    v___x_1930_ = lean_box(0);
                                    v_isShared_1931_ = v_isSharedCheck_1943_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                v_a_1944_ = lean_ctor_get(v___x_1927_, 0);
                                v_isSharedCheck_1951_ = (!lean_is_exclusive(v___x_1927_)) as u8;
                                if v_isSharedCheck_1951_ == 0 {
                                    v___x_1946_ = v___x_1927_;
                                    v_isShared_1947_ = v_isSharedCheck_1951_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_1944_);
                                    lean_dec(v___x_1927_);
                                    v___x_1946_ = lean_box(0);
                                    v_isShared_1947_ = v_isSharedCheck_1951_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_1925_);
                            v___x_1952_ = 6;
                            v___x_1953_ = lean_box((v___x_1952_) as usize);
                            v___x_1954_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1954_, 0, v___x_1953_);
                            return v___x_1954_;
                        }
                    }
                } else {
                    lean_dec(v___x_1861_);
                    v___x_1955_ = 3;
                    v___x_1956_ = lean_box((v___x_1955_) as usize);
                    v___x_1957_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1957_, 0, v___x_1956_);
                    return v___x_1957_;
                }
            }
            1 => {
                v___x_1872_ = (lean_unbox(v_a_1868_) as u8);
                lean_dec(v_a_1868_);
                if v___x_1872_ == 0 {
                    lean_del_object(v___x_1870_);
                    v_fileName_1873_ = lean_ctor_get(v_a_1858_, 0);
                    v_fileMap_1874_ = lean_ctor_get(v_a_1858_, 1);
                    v_options_1875_ = lean_ctor_get(v_a_1858_, 2);
                    v_currRecDepth_1876_ = lean_ctor_get(v_a_1858_, 3);
                    v_maxRecDepth_1877_ = lean_ctor_get(v_a_1858_, 4);
                    v_ref_1878_ = lean_ctor_get(v_a_1858_, 5);
                    v_currNamespace_1879_ = lean_ctor_get(v_a_1858_, 6);
                    v_openDecls_1880_ = lean_ctor_get(v_a_1858_, 7);
                    v_initHeartbeats_1881_ = lean_ctor_get(v_a_1858_, 8);
                    v_quotContext_1882_ = lean_ctor_get(v_a_1858_, 10);
                    v_currMacroScope_1883_ = lean_ctor_get(v_a_1858_, 11);
                    v_diag_1884_ = lean_ctor_get_uint8(
                        v_a_1858_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_1885_ = lean_ctor_get(v_a_1858_, 12);
                    v_suppressElabErrors_1886_ = lean_ctor_get_uint8(
                        v_a_1858_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_1887_ = lean_ctor_get(v_a_1858_, 13);
                    v___x_1888_ = l_Lean_ConstantInfo_type(v_constInfo_1855_);
                    v___x_1889_ = lean_unsigned_to_nat(0);
                    lean_inc_ref(v_inheritedTraceOptions_1887_);
                    lean_inc(v_cancelTk_x3f_1885_);
                    lean_inc(v_currMacroScope_1883_);
                    lean_inc(v_quotContext_1882_);
                    lean_inc(v_initHeartbeats_1881_);
                    lean_inc(v_openDecls_1880_);
                    lean_inc(v_currNamespace_1879_);
                    lean_inc(v_ref_1878_);
                    lean_inc(v_maxRecDepth_1877_);
                    lean_inc(v_currRecDepth_1876_);
                    lean_inc_ref(v_options_1875_);
                    lean_inc_ref(v_fileMap_1874_);
                    lean_inc_ref(v_fileName_1873_);
                    v___x_1890_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v___x_1890_, 0, v_fileName_1873_);
                    lean_ctor_set(v___x_1890_, 1, v_fileMap_1874_);
                    lean_ctor_set(v___x_1890_, 2, v_options_1875_);
                    lean_ctor_set(v___x_1890_, 3, v_currRecDepth_1876_);
                    lean_ctor_set(v___x_1890_, 4, v_maxRecDepth_1877_);
                    lean_ctor_set(v___x_1890_, 5, v_ref_1878_);
                    lean_ctor_set(v___x_1890_, 6, v_currNamespace_1879_);
                    lean_ctor_set(v___x_1890_, 7, v_openDecls_1880_);
                    lean_ctor_set(v___x_1890_, 8, v_initHeartbeats_1881_);
                    lean_ctor_set(v___x_1890_, 9, v___x_1889_);
                    lean_ctor_set(v___x_1890_, 10, v_quotContext_1882_);
                    lean_ctor_set(v___x_1890_, 11, v_currMacroScope_1883_);
                    lean_ctor_set(v___x_1890_, 12, v_cancelTk_x3f_1885_);
                    lean_ctor_set(v___x_1890_, 13, v_inheritedTraceOptions_1887_);
                    lean_ctor_set_uint8(
                        v___x_1890_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                        v_diag_1884_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1890_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1886_,
                    );
                    lean_inc(v_a_1859_);
                    lean_inc(v_a_1857_);
                    lean_inc_ref(v_a_1856_);
                    v___x_1891_ =
                        lean_whnf(v___x_1888_, v_a_1856_, v_a_1857_, v___x_1890_, v_a_1859_);
                    if lean_obj_tag(v___x_1891_) == 0 {
                        v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
                        v_isSharedCheck_1907_ = (!lean_is_exclusive(v___x_1891_)) as u8;
                        if v_isSharedCheck_1907_ == 0 {
                            v___x_1894_ = v___x_1891_;
                            v_isShared_1895_ = v_isSharedCheck_1907_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1892_);
                            lean_dec(v___x_1891_);
                            v___x_1894_ = lean_box(0);
                            v_isShared_1895_ = v_isSharedCheck_1907_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1908_ = lean_ctor_get(v___x_1891_, 0);
                        v_isSharedCheck_1915_ = (!lean_is_exclusive(v___x_1891_)) as u8;
                        if v_isSharedCheck_1915_ == 0 {
                            v___x_1910_ = v___x_1891_;
                            v_isShared_1911_ = v_isSharedCheck_1915_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1908_);
                            lean_dec(v___x_1891_);
                            v___x_1910_ = lean_box(0);
                            v_isShared_1911_ = v_isSharedCheck_1915_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v___x_1916_ = 4;
                    v___x_1917_ = lean_box((v___x_1916_) as usize);
                    if v_isShared_1871_ == 0 {
                        lean_ctor_set(v___x_1870_, 0, v___x_1917_);
                        v___x_1919_ = v___x_1870_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
                        v___x_1919_ = v_reuseFailAlloc_1920_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1896_ = l_Lean_Expr_isForall(v_a_1892_);
                lean_dec(v_a_1892_);
                if v___x_1896_ == 0 {
                    v___x_1897_ = 20;
                    v___x_1898_ = lean_box((v___x_1897_) as usize);
                    if v_isShared_1895_ == 0 {
                        lean_ctor_set(v___x_1894_, 0, v___x_1898_);
                        v___x_1900_ = v___x_1894_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
                        v___x_1900_ = v_reuseFailAlloc_1901_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1902_ = 2;
                    v___x_1903_ = lean_box((v___x_1902_) as usize);
                    if v_isShared_1895_ == 0 {
                        lean_ctor_set(v___x_1894_, 0, v___x_1903_);
                        v___x_1905_ = v___x_1894_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
                        v___x_1905_ = v_reuseFailAlloc_1906_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1900_;
            }
            4 => {
                return v___x_1905_;
            }
            5 => {
                if v_isShared_1911_ == 0 {
                    v___x_1913_ = v___x_1910_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
                    v___x_1913_ = v_reuseFailAlloc_1914_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1913_;
            }
            7 => {
                return v___x_1919_;
            }
            8 => {
                v___x_1932_ = (lean_unbox(v_a_1928_) as u8);
                lean_dec(v_a_1928_);
                if v___x_1932_ == 0 {
                    v___x_1933_ = 21;
                    v___x_1934_ = lean_box((v___x_1933_) as usize);
                    if v_isShared_1931_ == 0 {
                        lean_ctor_set(v___x_1930_, 0, v___x_1934_);
                        v___x_1936_ = v___x_1930_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
                        v___x_1936_ = v_reuseFailAlloc_1937_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___x_1938_ = 12;
                    v___x_1939_ = lean_box((v___x_1938_) as usize);
                    if v_isShared_1931_ == 0 {
                        lean_ctor_set(v___x_1930_, 0, v___x_1939_);
                        v___x_1941_ = v___x_1930_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
                        v___x_1941_ = v_reuseFailAlloc_1942_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_1936_;
            }
            10 => {
                return v___x_1941_;
            }
            11 => {
                if v_isShared_1947_ == 0 {
                    v___x_1949_ = v___x_1946_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
                    v___x_1949_ = v_reuseFailAlloc_1950_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Completion_getCompletionKindForDecl___boxed(
    mut v_constInfo_1958_: *mut LeanObject,
    mut v_a_1959_: *mut LeanObject,
    mut v_a_1960_: *mut LeanObject,
    mut v_a_1961_: *mut LeanObject,
    mut v_a_1962_: *mut LeanObject,
    mut v_a_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1964_: *mut LeanObject = core::ptr::null_mut();
    v_res_1964_ = l_Lean_Server_Completion_getCompletionKindForDecl(
        v_constInfo_1958_,
        v_a_1959_,
        v_a_1960_,
        v_a_1961_,
        v_a_1962_,
    );
    lean_dec(v_a_1962_);
    lean_dec_ref(v_a_1961_);
    lean_dec(v_a_1960_);
    lean_dec_ref(v_a_1959_);
    lean_dec_ref(v_constInfo_1958_);
    return v_res_1964_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2(
    mut v_00_u03b1_1965_: *mut LeanObject,
    mut v_constName_1966_: *mut LeanObject,
    mut v___y_1967_: *mut LeanObject,
    mut v___y_1968_: *mut LeanObject,
    mut v___y_1969_: *mut LeanObject,
    mut v___y_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    v___x_1972_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2___redArg(v_constName_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
    return v___x_1972_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b1_1973_: *mut LeanObject,
    mut v_constName_1974_: *mut LeanObject,
    mut v___y_1975_: *mut LeanObject,
    mut v___y_1976_: *mut LeanObject,
    mut v___y_1977_: *mut LeanObject,
    mut v___y_1978_: *mut LeanObject,
    mut v___y_1979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1980_: *mut LeanObject = core::ptr::null_mut();
    v_res_1980_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2(v_00_u03b1_1973_, v_constName_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
    lean_dec(v___y_1978_);
    lean_dec_ref(v___y_1977_);
    lean_dec(v___y_1976_);
    lean_dec_ref(v___y_1975_);
    return v_res_1980_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b1_1981_: *mut LeanObject,
    mut v_ref_1982_: *mut LeanObject,
    mut v_constName_1983_: *mut LeanObject,
    mut v___y_1984_: *mut LeanObject,
    mut v___y_1985_: *mut LeanObject,
    mut v___y_1986_: *mut LeanObject,
    mut v___y_1987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    v___x_1989_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___redArg(v_ref_1982_, v_constName_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
    return v___x_1989_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b1_1990_: *mut LeanObject,
    mut v_ref_1991_: *mut LeanObject,
    mut v_constName_1992_: *mut LeanObject,
    mut v___y_1993_: *mut LeanObject,
    mut v___y_1994_: *mut LeanObject,
    mut v___y_1995_: *mut LeanObject,
    mut v___y_1996_: *mut LeanObject,
    mut v___y_1997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1998_: *mut LeanObject = core::ptr::null_mut();
    v_res_1998_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_1990_, v_ref_1991_, v_constName_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
    lean_dec(v___y_1996_);
    lean_dec_ref(v___y_1995_);
    lean_dec(v___y_1994_);
    lean_dec_ref(v___y_1993_);
    lean_dec(v_ref_1991_);
    return v_res_1998_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b1_1999_: *mut LeanObject,
    mut v_ref_2000_: *mut LeanObject,
    mut v_msg_2001_: *mut LeanObject,
    mut v_declHint_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
    mut v___y_2004_: *mut LeanObject,
    mut v___y_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    v___x_2008_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_2000_, v_msg_2001_, v_declHint_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
    return v___x_2008_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_2009_: *mut LeanObject,
    mut v_ref_2010_: *mut LeanObject,
    mut v_msg_2011_: *mut LeanObject,
    mut v_declHint_2012_: *mut LeanObject,
    mut v___y_2013_: *mut LeanObject,
    mut v___y_2014_: *mut LeanObject,
    mut v___y_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
    mut v___y_2017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2018_: *mut LeanObject = core::ptr::null_mut();
    v_res_2018_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_2009_, v_ref_2010_, v_msg_2011_, v_declHint_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
    lean_dec(v___y_2016_);
    lean_dec_ref(v___y_2015_);
    lean_dec(v___y_2014_);
    lean_dec_ref(v___y_2013_);
    lean_dec(v_ref_2010_);
    return v_res_2018_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7(
    mut v_msg_2019_: *mut LeanObject,
    mut v_declHint_2020_: *mut LeanObject,
    mut v___y_2021_: *mut LeanObject,
    mut v___y_2022_: *mut LeanObject,
    mut v___y_2023_: *mut LeanObject,
    mut v___y_2024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    v___x_2026_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_2019_, v_declHint_2020_, v___y_2024_);
    return v___x_2026_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(
    mut v_msg_2027_: *mut LeanObject,
    mut v_declHint_2028_: *mut LeanObject,
    mut v___y_2029_: *mut LeanObject,
    mut v___y_2030_: *mut LeanObject,
    mut v___y_2031_: *mut LeanObject,
    mut v___y_2032_: *mut LeanObject,
    mut v___y_2033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2034_: *mut LeanObject = core::ptr::null_mut();
    v_res_2034_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7(v_msg_2027_, v_declHint_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
    lean_dec(v___y_2032_);
    lean_dec_ref(v___y_2031_);
    lean_dec(v___y_2030_);
    lean_dec_ref(v___y_2029_);
    return v_res_2034_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7(
    mut v_00_u03b1_2035_: *mut LeanObject,
    mut v_ref_2036_: *mut LeanObject,
    mut v_msg_2037_: *mut LeanObject,
    mut v___y_2038_: *mut LeanObject,
    mut v___y_2039_: *mut LeanObject,
    mut v___y_2040_: *mut LeanObject,
    mut v___y_2041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    v___x_2043_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_2036_, v_msg_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
    return v___x_2043_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b1_2044_: *mut LeanObject,
    mut v_ref_2045_: *mut LeanObject,
    mut v_msg_2046_: *mut LeanObject,
    mut v___y_2047_: *mut LeanObject,
    mut v___y_2048_: *mut LeanObject,
    mut v___y_2049_: *mut LeanObject,
    mut v___y_2050_: *mut LeanObject,
    mut v___y_2051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2052_: *mut LeanObject = core::ptr::null_mut();
    v_res_2052_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_2044_, v_ref_2045_, v_msg_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
    lean_dec(v___y_2050_);
    lean_dec_ref(v___y_2049_);
    lean_dec(v___y_2048_);
    lean_dec_ref(v___y_2047_);
    lean_dec(v_ref_2045_);
    return v_res_2052_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9(
    mut v_00_u03b1_2053_: *mut LeanObject,
    mut v_msg_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    v___x_2060_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
    return v___x_2060_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(
    mut v_00_u03b1_2061_: *mut LeanObject,
    mut v_msg_2062_: *mut LeanObject,
    mut v___y_2063_: *mut LeanObject,
    mut v___y_2064_: *mut LeanObject,
    mut v___y_2065_: *mut LeanObject,
    mut v___y_2066_: *mut LeanObject,
    mut v___y_2067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2068_: *mut LeanObject = core::ptr::null_mut();
    v_res_2068_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00Lean_Server_Completion_getCompletionKindForDecl_spec__1_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_2061_, v_msg_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
    lean_dec(v___y_2066_);
    lean_dec_ref(v___y_2065_);
    lean_dec(v___y_2064_);
    lean_dec_ref(v___y_2063_);
    return v_res_2068_;
}
pub unsafe fn l_Lean_Server_Completion_getCompletionTagsForDecl___redArg(
    mut v_declName_2075_: *mut LeanObject,
    mut v_a_2076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: u8 = 0;
    v___x_2078_ = lean_st_ref_get(v_a_2076_);
    v_env_2079_ = lean_ctor_get(v___x_2078_, 0);
    lean_inc_ref(v_env_2079_);
    lean_dec(v___x_2078_);
    v___x_2080_ = l_Lean_Linter_isDeprecated(v_env_2079_, v_declName_2075_);
    if v___x_2080_ == 0 {
        let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
        v___x_2081_ = l_Lean_Server_Completion_getCompletionTagsForDecl___redArg___closed__0;
        v___x_2082_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2082_, 0, v___x_2081_);
        return v___x_2082_;
    } else {
        let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
        v___x_2083_ = l_Lean_Server_Completion_getCompletionTagsForDecl___redArg___closed__1;
        v___x_2084_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2084_, 0, v___x_2083_);
        return v___x_2084_;
    }
}
pub unsafe fn l_Lean_Server_Completion_getCompletionTagsForDecl___redArg___boxed(
    mut v_declName_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
    mut v_a_2087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2088_: *mut LeanObject = core::ptr::null_mut();
    v_res_2088_ =
        l_Lean_Server_Completion_getCompletionTagsForDecl___redArg(v_declName_2085_, v_a_2086_);
    lean_dec(v_a_2086_);
    return v_res_2088_;
}
pub unsafe fn l_Lean_Server_Completion_getCompletionTagsForDecl(
    mut v_declName_2089_: *mut LeanObject,
    mut v_a_2090_: *mut LeanObject,
    mut v_a_2091_: *mut LeanObject,
    mut v_a_2092_: *mut LeanObject,
    mut v_a_2093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    v___x_2095_ =
        l_Lean_Server_Completion_getCompletionTagsForDecl___redArg(v_declName_2089_, v_a_2093_);
    return v___x_2095_;
}
pub unsafe fn l_Lean_Server_Completion_getCompletionTagsForDecl___boxed(
    mut v_declName_2096_: *mut LeanObject,
    mut v_a_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
    mut v_a_2099_: *mut LeanObject,
    mut v_a_2100_: *mut LeanObject,
    mut v_a_2101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2102_: *mut LeanObject = core::ptr::null_mut();
    v_res_2102_ = l_Lean_Server_Completion_getCompletionTagsForDecl(
        v_declName_2096_,
        v_a_2097_,
        v_a_2098_,
        v_a_2099_,
        v_a_2100_,
    );
    lean_dec(v_a_2100_);
    lean_dec_ref(v_a_2099_);
    lean_dec(v_a_2098_);
    lean_dec_ref(v_a_2097_);
    return v_res_2102_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3___redArg___lam__0(
    mut v_mutex_2103_: *mut LeanObject,
    mut v_a_x3f_2104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    v___x_2106_ = lean_io_basemutex_unlock(v_mutex_2103_);
    v___x_2107_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2107_, 0, v___x_2106_);
    return v___x_2107_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3___redArg___lam__0___boxed(
    mut v_mutex_2108_: *mut LeanObject,
    mut v_a_x3f_2109_: *mut LeanObject,
    mut v___y_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2111_: *mut LeanObject = core::ptr::null_mut();
    v_res_2111_ = l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3___redArg___lam__0(v_mutex_2108_, v_a_x3f_2109_);
    lean_dec(v_a_x3f_2109_);
    lean_dec(v_mutex_2108_);
    return v_res_2111_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3___redArg(
    mut v_mutex_2112_: *mut LeanObject,
    mut v_k_2113_: *mut LeanObject,
    mut v___y_2114_: *mut LeanObject,
    mut v___y_2115_: *mut LeanObject,
    mut v___y_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2126_: u8 = 0;
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2132_: u8 = 0;
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2136_: u8 = 0;
    let mut v_unused_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2139_: u8 = 0;
    let mut v_a_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2145_: u8 = 0;
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut v_unused_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2119_ = lean_ctor_get(v_mutex_2112_, 0);
                lean_inc(v_ref_2119_);
                v_mutex_2120_ = lean_ctor_get(v_mutex_2112_, 1);
                lean_inc(v_mutex_2120_);
                lean_dec_ref(v_mutex_2112_);
                v___x_2121_ = lean_io_basemutex_lock(v_mutex_2120_);
                lean_inc(v___y_2117_);
                lean_inc_ref(v___y_2116_);
                lean_inc(v___y_2115_);
                lean_inc_ref(v___y_2114_);
                v___x_2122_ = lean_apply_6(
                    v_k_2113_,
                    v_ref_2119_,
                    v___y_2114_,
                    v___y_2115_,
                    v___y_2116_,
                    v___y_2117_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2122_) == 0 {
                    v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
                    v_isSharedCheck_2139_ = (!lean_is_exclusive(v___x_2122_)) as u8;
                    if v_isSharedCheck_2139_ == 0 {
                        v___x_2125_ = v___x_2122_;
                        v_isShared_2126_ = v_isSharedCheck_2139_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2123_);
                        lean_dec(v___x_2122_);
                        v___x_2125_ = lean_box(0);
                        v_isShared_2126_ = v_isSharedCheck_2139_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2140_ = lean_ctor_get(v___x_2122_, 0);
                    lean_inc(v_a_2140_);
                    lean_dec_ref_known(v___x_2122_, 1);
                    v___x_2141_ = lean_box(0);
                    v___x_2142_ = l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3___redArg___lam__0(v_mutex_2120_, v___x_2141_);
                    lean_dec(v_mutex_2120_);
                    v_isSharedCheck_2149_ = (!lean_is_exclusive(v___x_2142_)) as u8;
                    if v_isSharedCheck_2149_ == 0 {
                        v_unused_2150_ = lean_ctor_get(v___x_2142_, 0);
                        lean_dec(v_unused_2150_);
                        v___x_2144_ = v___x_2142_;
                        v_isShared_2145_ = v_isSharedCheck_2149_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v___x_2142_);
                        v___x_2144_ = lean_box(0);
                        v_isShared_2145_ = v_isSharedCheck_2149_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_2123_);
                if v_isShared_2126_ == 0 {
                    lean_ctor_set_tag(v___x_2125_, 1);
                    v___x_2128_ = v___x_2125_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2123_);
                    v___x_2128_ = v_reuseFailAlloc_2138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2129_ = l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3___redArg___lam__0(v_mutex_2120_, v___x_2128_);
                lean_dec_ref(v___x_2128_);
                lean_dec(v_mutex_2120_);
                v_isSharedCheck_2136_ = (!lean_is_exclusive(v___x_2129_)) as u8;
                if v_isSharedCheck_2136_ == 0 {
                    v_unused_2137_ = lean_ctor_get(v___x_2129_, 0);
                    lean_dec(v_unused_2137_);
                    v___x_2131_ = v___x_2129_;
                    v_isShared_2132_ = v_isSharedCheck_2136_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_2129_);
                    v___x_2131_ = lean_box(0);
                    v_isShared_2132_ = v_isSharedCheck_2136_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2132_ == 0 {
                    lean_ctor_set(v___x_2131_, 0, v_a_2123_);
                    v___x_2134_ = v___x_2131_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2123_);
                    v___x_2134_ = v_reuseFailAlloc_2135_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2134_;
            }
            5 => {
                if v_isShared_2145_ == 0 {
                    lean_ctor_set_tag(v___x_2144_, 1);
                    lean_ctor_set(v___x_2144_, 0, v_a_2140_);
                    v___x_2147_ = v___x_2144_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2140_);
                    v___x_2147_ = v_reuseFailAlloc_2148_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3___redArg___boxed(
    mut v_mutex_2151_: *mut LeanObject,
    mut v_k_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2158_: *mut LeanObject = core::ptr::null_mut();
    v_res_2158_ = l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3___redArg(v_mutex_2151_, v_k_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
    lean_dec(v___y_2156_);
    lean_dec_ref(v___y_2155_);
    lean_dec(v___y_2154_);
    lean_dec_ref(v___y_2153_);
    return v_res_2158_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3(
    mut v_00_u03b1_2159_: *mut LeanObject,
    mut v_00_u03b2_2160_: *mut LeanObject,
    mut v_mutex_2161_: *mut LeanObject,
    mut v_k_2162_: *mut LeanObject,
    mut v___y_2163_: *mut LeanObject,
    mut v___y_2164_: *mut LeanObject,
    mut v___y_2165_: *mut LeanObject,
    mut v___y_2166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    v___x_2168_ = l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3___redArg(v_mutex_2161_, v_k_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
    return v___x_2168_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3___boxed(
    mut v_00_u03b1_2169_: *mut LeanObject,
    mut v_00_u03b2_2170_: *mut LeanObject,
    mut v_mutex_2171_: *mut LeanObject,
    mut v_k_2172_: *mut LeanObject,
    mut v___y_2173_: *mut LeanObject,
    mut v___y_2174_: *mut LeanObject,
    mut v___y_2175_: *mut LeanObject,
    mut v___y_2176_: *mut LeanObject,
    mut v___y_2177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2178_: *mut LeanObject = core::ptr::null_mut();
    v_res_2178_ =
        l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3(
            v_00_u03b1_2169_,
            v_00_u03b2_2170_,
            v_mutex_2171_,
            v_k_2172_,
            v___y_2173_,
            v___y_2174_,
            v___y_2175_,
            v___y_2176_,
        );
    lean_dec(v___y_2176_);
    lean_dec_ref(v___y_2175_);
    lean_dec(v___y_2174_);
    lean_dec_ref(v___y_2173_);
    return v_res_2178_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg___lam__0(
    mut v_a_2179_: u8,
    mut v___y_2180_: *mut LeanObject,
    mut v___y_2181_: *mut LeanObject,
    mut v___y_2182_: *mut LeanObject,
    mut v___y_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    v___x_2185_ = lean_box((v_a_2179_) as usize);
    v___x_2186_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2186_, 0, v___x_2185_);
    return v___x_2186_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg___lam__0___boxed(
    mut v_a_2187_: *mut LeanObject,
    mut v___y_2188_: *mut LeanObject,
    mut v___y_2189_: *mut LeanObject,
    mut v___y_2190_: *mut LeanObject,
    mut v___y_2191_: *mut LeanObject,
    mut v___y_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4533__boxed_2193_: u8 = 0;
    let mut v_res_2194_: *mut LeanObject = core::ptr::null_mut();
    v_a_4533__boxed_2193_ = (lean_unbox(v_a_2187_) as u8);
    v_res_2194_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg___lam__0(v_a_4533__boxed_2193_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
    lean_dec(v___y_2191_);
    lean_dec_ref(v___y_2190_);
    lean_dec(v___y_2189_);
    lean_dec_ref(v___y_2188_);
    return v_res_2194_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg___lam__1(
    mut v_a_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
    mut v___y_2198_: *mut LeanObject,
    mut v___y_2199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    v___x_2201_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2201_, 0, v_a_2195_);
    return v___x_2201_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg___lam__1___boxed(
    mut v_a_2202_: *mut LeanObject,
    mut v___y_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
    mut v___y_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2208_: *mut LeanObject = core::ptr::null_mut();
    v_res_2208_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg___lam__1(v_a_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
    lean_dec(v___y_2206_);
    lean_dec_ref(v___y_2205_);
    lean_dec(v___y_2204_);
    lean_dec_ref(v___y_2203_);
    return v_res_2208_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0()
-> u64 {
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: u64 = 0;
    v___x_2209_ = lean_unsigned_to_nat(1723);
    v___x_2210_ = lean_uint64_of_nat(v___x_2209_);
    return v___x_2210_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_x_2211_: *mut LeanObject,
    mut v_x_2212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2221_: u64 = 0;
    let mut v___x_2222_: u64 = 0;
    let mut v___x_2223_: u64 = 0;
    let mut v_fold_2224_: u64 = 0;
    let mut v___x_2225_: u64 = 0;
    let mut v___x_2226_: u64 = 0;
    let mut v___x_2227_: u64 = 0;
    let mut v___x_2228_: usize = 0;
    let mut v___x_2229_: usize = 0;
    let mut v___x_2230_: usize = 0;
    let mut v___x_2231_: usize = 0;
    let mut v___x_2232_: usize = 0;
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: u64 = 0;
    let mut v_hash_2240_: u64 = 0;
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2212_) == 0 {
                    return v_x_2211_;
                } else {
                    v_key_2213_ = lean_ctor_get(v_x_2212_, 0);
                    v_value_2214_ = lean_ctor_get(v_x_2212_, 1);
                    v_tail_2215_ = lean_ctor_get(v_x_2212_, 2);
                    v_isSharedCheck_2241_ = (!lean_is_exclusive(v_x_2212_)) as u8;
                    if v_isSharedCheck_2241_ == 0 {
                        v___x_2217_ = v_x_2212_;
                        v_isShared_2218_ = v_isSharedCheck_2241_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2215_);
                        lean_inc(v_value_2214_);
                        lean_inc(v_key_2213_);
                        lean_dec(v_x_2212_);
                        v___x_2217_ = lean_box(0);
                        v_isShared_2218_ = v_isSharedCheck_2241_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2219_ = lean_array_get_size(v_x_2211_);
                if lean_obj_tag(v_key_2213_) == 0 {
                    v___x_2239_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0);
                    v___y_2221_ = v___x_2239_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2240_ = lean_ctor_get_uint64(
                        v_key_2213_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2221_ = v_hash_2240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2222_ = 32u64;
                v___x_2223_ = lean_uint64_shift_right(v___y_2221_, v___x_2222_);
                v_fold_2224_ = lean_uint64_xor(v___y_2221_, v___x_2223_);
                v___x_2225_ = 16u64;
                v___x_2226_ = lean_uint64_shift_right(v_fold_2224_, v___x_2225_);
                v___x_2227_ = lean_uint64_xor(v_fold_2224_, v___x_2226_);
                v___x_2228_ = lean_uint64_to_usize(v___x_2227_);
                v___x_2229_ = lean_usize_of_nat(v___x_2219_);
                v___x_2230_ = 1usize;
                v___x_2231_ = lean_usize_sub(v___x_2229_, v___x_2230_);
                v___x_2232_ = lean_usize_land(v___x_2228_, v___x_2231_);
                v___x_2233_ = lean_array_uget_borrowed(v_x_2211_, v___x_2232_);
                lean_inc(v___x_2233_);
                if v_isShared_2218_ == 0 {
                    lean_ctor_set(v___x_2217_, 2, v___x_2233_);
                    v___x_2235_ = v___x_2217_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_key_2213_);
                    lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_value_2214_);
                    lean_ctor_set(v_reuseFailAlloc_2238_, 2, v___x_2233_);
                    v___x_2235_ = v_reuseFailAlloc_2238_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2236_ = lean_array_uset(v_x_2211_, v___x_2232_, v___x_2235_);
                v_x_2211_ = v___x_2236_;
                v_x_2212_ = v_tail_2215_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3___redArg(
    mut v_i_2242_: *mut LeanObject,
    mut v_source_2243_: *mut LeanObject,
    mut v_target_2244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: u8 = 0;
    let mut v_es_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2245_ = lean_array_get_size(v_source_2243_);
                v___x_2246_ = lean_nat_dec_lt(v_i_2242_, v___x_2245_);
                if v___x_2246_ == 0 {
                    lean_dec_ref(v_source_2243_);
                    lean_dec(v_i_2242_);
                    return v_target_2244_;
                } else {
                    v_es_2247_ = lean_array_fget(v_source_2243_, v_i_2242_);
                    v___x_2248_ = lean_box(0);
                    v_source_2249_ = lean_array_fset(v_source_2243_, v_i_2242_, v___x_2248_);
                    v_target_2250_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg(v_target_2244_, v_es_2247_);
                    v___x_2251_ = lean_unsigned_to_nat(1);
                    v___x_2252_ = lean_nat_add(v_i_2242_, v___x_2251_);
                    lean_dec(v_i_2242_);
                    v_i_2242_ = v___x_2252_;
                    v_source_2243_ = v_source_2249_;
                    v_target_2244_ = v_target_2250_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1___redArg(
    mut v_data_2254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    v___x_2255_ = lean_array_get_size(v_data_2254_);
    v___x_2256_ = lean_unsigned_to_nat(2);
    v_nbuckets_2257_ = lean_nat_mul(v___x_2255_, v___x_2256_);
    v___x_2258_ = lean_unsigned_to_nat(0);
    v___x_2259_ = lean_box(0);
    v___x_2260_ = lean_mk_array(v_nbuckets_2257_, v___x_2259_);
    v___x_2261_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3___redArg(v___x_2258_, v_data_2254_, v___x_2260_);
    return v___x_2261_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__0___redArg(
    mut v_a_2262_: *mut LeanObject,
    mut v_x_2263_: *mut LeanObject,
) -> u8 {
    let mut v___x_2264_: u8 = 0;
    let mut v_key_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2263_) == 0 {
                    v___x_2264_ = 0;
                    return v___x_2264_;
                } else {
                    v_key_2265_ = lean_ctor_get(v_x_2263_, 0);
                    v_tail_2266_ = lean_ctor_get(v_x_2263_, 2);
                    v___x_2267_ = lean_name_eq(v_key_2265_, v_a_2262_);
                    if v___x_2267_ == 0 {
                        v_x_2263_ = v_tail_2266_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2267_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__0___redArg___boxed(
    mut v_a_2269_: *mut LeanObject,
    mut v_x_2270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2271_: u8 = 0;
    let mut v_r_2272_: *mut LeanObject = core::ptr::null_mut();
    v_res_2271_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__0___redArg(v_a_2269_, v_x_2270_);
    lean_dec(v_x_2270_);
    lean_dec(v_a_2269_);
    v_r_2272_ = lean_box((v_res_2271_) as usize);
    return v_r_2272_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__2___redArg(
    mut v_a_2273_: *mut LeanObject,
    mut v_b_2274_: *mut LeanObject,
    mut v_x_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2281_: u8 = 0;
    let mut v___x_2282_: u8 = 0;
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2275_) == 0 {
                    lean_dec(v_b_2274_);
                    lean_dec(v_a_2273_);
                    return v_x_2275_;
                } else {
                    v_key_2276_ = lean_ctor_get(v_x_2275_, 0);
                    v_value_2277_ = lean_ctor_get(v_x_2275_, 1);
                    v_tail_2278_ = lean_ctor_get(v_x_2275_, 2);
                    v_isSharedCheck_2290_ = (!lean_is_exclusive(v_x_2275_)) as u8;
                    if v_isSharedCheck_2290_ == 0 {
                        v___x_2280_ = v_x_2275_;
                        v_isShared_2281_ = v_isSharedCheck_2290_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2278_);
                        lean_inc(v_value_2277_);
                        lean_inc(v_key_2276_);
                        lean_dec(v_x_2275_);
                        v___x_2280_ = lean_box(0);
                        v_isShared_2281_ = v_isSharedCheck_2290_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2282_ = lean_name_eq(v_key_2276_, v_a_2273_);
                if v___x_2282_ == 0 {
                    v___x_2283_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__2___redArg(v_a_2273_, v_b_2274_, v_tail_2278_);
                    if v_isShared_2281_ == 0 {
                        lean_ctor_set(v___x_2280_, 2, v___x_2283_);
                        v___x_2285_ = v___x_2280_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_key_2276_);
                        lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_value_2277_);
                        lean_ctor_set(v_reuseFailAlloc_2286_, 2, v___x_2283_);
                        v___x_2285_ = v_reuseFailAlloc_2286_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2277_);
                    lean_dec(v_key_2276_);
                    if v_isShared_2281_ == 0 {
                        lean_ctor_set(v___x_2280_, 1, v_b_2274_);
                        lean_ctor_set(v___x_2280_, 0, v_a_2273_);
                        v___x_2288_ = v___x_2280_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2273_);
                        lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_b_2274_);
                        lean_ctor_set(v_reuseFailAlloc_2289_, 2, v_tail_2278_);
                        v___x_2288_ = v_reuseFailAlloc_2289_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2285_;
            }
            3 => {
                return v___x_2288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0___redArg(
    mut v_m_2291_: *mut LeanObject,
    mut v_a_2292_: *mut LeanObject,
    mut v_b_2293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2298_: u8 = 0;
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2301_: u64 = 0;
    let mut v___x_2302_: u64 = 0;
    let mut v___x_2303_: u64 = 0;
    let mut v_fold_2304_: u64 = 0;
    let mut v___x_2305_: u64 = 0;
    let mut v___x_2306_: u64 = 0;
    let mut v___x_2307_: u64 = 0;
    let mut v___x_2308_: usize = 0;
    let mut v___x_2309_: usize = 0;
    let mut v___x_2310_: usize = 0;
    let mut v___x_2311_: usize = 0;
    let mut v___x_2312_: usize = 0;
    let mut v_bkt_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    let mut v_val_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: u64 = 0;
    let mut v_hash_2340_: u64 = 0;
    let mut v_isSharedCheck_2341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2294_ = lean_ctor_get(v_m_2291_, 0);
                v_buckets_2295_ = lean_ctor_get(v_m_2291_, 1);
                v_isSharedCheck_2341_ = (!lean_is_exclusive(v_m_2291_)) as u8;
                if v_isSharedCheck_2341_ == 0 {
                    v___x_2297_ = v_m_2291_;
                    v_isShared_2298_ = v_isSharedCheck_2341_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2295_);
                    lean_inc(v_size_2294_);
                    lean_dec(v_m_2291_);
                    v___x_2297_ = lean_box(0);
                    v_isShared_2298_ = v_isSharedCheck_2341_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2299_ = lean_array_get_size(v_buckets_2295_);
                if lean_obj_tag(v_a_2292_) == 0 {
                    v___x_2339_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0);
                    v___y_2301_ = v___x_2339_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2340_ = lean_ctor_get_uint64(
                        v_a_2292_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2301_ = v_hash_2340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2302_ = 32u64;
                v___x_2303_ = lean_uint64_shift_right(v___y_2301_, v___x_2302_);
                v_fold_2304_ = lean_uint64_xor(v___y_2301_, v___x_2303_);
                v___x_2305_ = 16u64;
                v___x_2306_ = lean_uint64_shift_right(v_fold_2304_, v___x_2305_);
                v___x_2307_ = lean_uint64_xor(v_fold_2304_, v___x_2306_);
                v___x_2308_ = lean_uint64_to_usize(v___x_2307_);
                v___x_2309_ = lean_usize_of_nat(v___x_2299_);
                v___x_2310_ = 1usize;
                v___x_2311_ = lean_usize_sub(v___x_2309_, v___x_2310_);
                v___x_2312_ = lean_usize_land(v___x_2308_, v___x_2311_);
                v_bkt_2313_ = lean_array_uget_borrowed(v_buckets_2295_, v___x_2312_);
                v___x_2314_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__0___redArg(v_a_2292_, v_bkt_2313_);
                if v___x_2314_ == 0 {
                    v___x_2315_ = lean_unsigned_to_nat(1);
                    v_size_x27_2316_ = lean_nat_add(v_size_2294_, v___x_2315_);
                    lean_dec(v_size_2294_);
                    lean_inc(v_bkt_2313_);
                    v___x_2317_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2317_, 0, v_a_2292_);
                    lean_ctor_set(v___x_2317_, 1, v_b_2293_);
                    lean_ctor_set(v___x_2317_, 2, v_bkt_2313_);
                    v_buckets_x27_2318_ =
                        lean_array_uset(v_buckets_2295_, v___x_2312_, v___x_2317_);
                    v___x_2319_ = lean_unsigned_to_nat(4);
                    v___x_2320_ = lean_nat_mul(v_size_x27_2316_, v___x_2319_);
                    v___x_2321_ = lean_unsigned_to_nat(3);
                    v___x_2322_ = lean_nat_div(v___x_2320_, v___x_2321_);
                    lean_dec(v___x_2320_);
                    v___x_2323_ = lean_array_get_size(v_buckets_x27_2318_);
                    v___x_2324_ = lean_nat_dec_le(v___x_2322_, v___x_2323_);
                    lean_dec(v___x_2322_);
                    if v___x_2324_ == 0 {
                        v_val_2325_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1___redArg(v_buckets_x27_2318_);
                        if v_isShared_2298_ == 0 {
                            lean_ctor_set(v___x_2297_, 1, v_val_2325_);
                            lean_ctor_set(v___x_2297_, 0, v_size_x27_2316_);
                            v___x_2327_ = v___x_2297_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_size_x27_2316_);
                            lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_val_2325_);
                            v___x_2327_ = v_reuseFailAlloc_2328_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_2298_ == 0 {
                            lean_ctor_set(v___x_2297_, 1, v_buckets_x27_2318_);
                            lean_ctor_set(v___x_2297_, 0, v_size_x27_2316_);
                            v___x_2330_ = v___x_2297_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_size_x27_2316_);
                            lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_buckets_x27_2318_);
                            v___x_2330_ = v_reuseFailAlloc_2331_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2313_);
                    v___x_2332_ = lean_box(0);
                    v_buckets_x27_2333_ =
                        lean_array_uset(v_buckets_2295_, v___x_2312_, v___x_2332_);
                    v___x_2334_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__2___redArg(v_a_2292_, v_b_2293_, v_bkt_2313_);
                    v___x_2335_ = lean_array_uset(v_buckets_x27_2333_, v___x_2312_, v___x_2334_);
                    if v_isShared_2298_ == 0 {
                        lean_ctor_set(v___x_2297_, 1, v___x_2335_);
                        v___x_2337_ = v___x_2297_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_size_2294_);
                        lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2335_);
                        v___x_2337_ = v_reuseFailAlloc_2338_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2327_;
            }
            4 => {
                return v___x_2330_;
            }
            5 => {
                return v___x_2337_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg(
    mut v_env_2342_: *mut LeanObject,
    mut v_a_2343_: *mut LeanObject,
    mut v_a_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
    mut v___y_2347_: *mut LeanObject,
    mut v___y_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2357_: u8 = 0;
    let mut v___x_2358_: u8 = 0;
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2374_: u8 = 0;
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut v_isSharedCheck_2379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2343_) == 0 {
                    lean_dec_ref(v_env_2342_);
                    v___x_2350_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2350_, 0, v_a_2344_);
                    v___x_2351_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2351_, 0, v___x_2350_);
                    return v___x_2351_;
                } else {
                    v_key_2352_ = lean_ctor_get(v_a_2343_, 0);
                    v_value_2353_ = lean_ctor_get(v_a_2343_, 1);
                    v_tail_2354_ = lean_ctor_get(v_a_2343_, 2);
                    v_isSharedCheck_2379_ = (!lean_is_exclusive(v_a_2343_)) as u8;
                    if v_isSharedCheck_2379_ == 0 {
                        v___x_2356_ = v_a_2343_;
                        v_isShared_2357_ = v_isSharedCheck_2379_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2354_);
                        lean_inc(v_value_2353_);
                        lean_inc(v_key_2352_);
                        lean_dec(v_a_2343_);
                        v___x_2356_ = lean_box(0);
                        v_isShared_2357_ = v_isSharedCheck_2379_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_key_2352_);
                lean_inc_ref(v_env_2342_);
                v___x_2358_ = l_Lean_Meta_allowCompletion(v_env_2342_, v_key_2352_);
                if v___x_2358_ == 0 {
                    lean_del_object(v___x_2356_);
                    lean_dec(v_value_2353_);
                    lean_dec(v_key_2352_);
                    v_a_2343_ = v_tail_2354_;
                    state = 0;
                    continue;
                } else {
                    v___x_2360_ = l_Lean_Server_Completion_getCompletionKindForDecl(
                        v_value_2353_,
                        v___y_2345_,
                        v___y_2346_,
                        v___y_2347_,
                        v___y_2348_,
                    );
                    if lean_obj_tag(v___x_2360_) == 0 {
                        v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
                        lean_inc(v_a_2361_);
                        lean_dec_ref_known(v___x_2360_, 1);
                        lean_inc(v_key_2352_);
                        v___x_2362_ = l_Lean_Server_Completion_getCompletionTagsForDecl___redArg(
                            v_key_2352_,
                            v___y_2348_,
                        );
                        v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
                        lean_inc(v_a_2363_);
                        lean_dec_ref(v___x_2362_);
                        v___f_2364_ = lean_alloc_closure(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 1);
                        lean_closure_set(v___f_2364_, 0, v_a_2361_);
                        v___f_2365_ = lean_alloc_closure(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 1);
                        lean_closure_set(v___f_2365_, 0, v_a_2363_);
                        if v_isShared_2357_ == 0 {
                            lean_ctor_set_tag(v___x_2356_, 0);
                            lean_ctor_set(v___x_2356_, 2, v___f_2365_);
                            lean_ctor_set(v___x_2356_, 1, v___f_2364_);
                            lean_ctor_set(v___x_2356_, 0, v_value_2353_);
                            v___x_2367_ = v___x_2356_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_value_2353_);
                            lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___f_2364_);
                            lean_ctor_set(v_reuseFailAlloc_2370_, 2, v___f_2365_);
                            v___x_2367_ = v_reuseFailAlloc_2370_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2356_);
                        lean_dec(v_tail_2354_);
                        lean_dec(v_value_2353_);
                        lean_dec(v_key_2352_);
                        lean_dec_ref(v_a_2344_);
                        lean_dec_ref(v_env_2342_);
                        v_a_2371_ = lean_ctor_get(v___x_2360_, 0);
                        v_isSharedCheck_2378_ = (!lean_is_exclusive(v___x_2360_)) as u8;
                        if v_isSharedCheck_2378_ == 0 {
                            v___x_2373_ = v___x_2360_;
                            v_isShared_2374_ = v_isSharedCheck_2378_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2371_);
                            lean_dec(v___x_2360_);
                            v___x_2373_ = lean_box(0);
                            v_isShared_2374_ = v_isSharedCheck_2378_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_2368_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0___redArg(v_a_2344_, v_key_2352_, v___x_2367_);
                v_a_2343_ = v_tail_2354_;
                v_a_2344_ = v___x_2368_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_2374_ == 0 {
                    v___x_2376_ = v___x_2373_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
                    v___x_2376_ = v_reuseFailAlloc_2377_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg___boxed(
    mut v_env_2380_: *mut LeanObject,
    mut v_a_2381_: *mut LeanObject,
    mut v_a_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2388_: *mut LeanObject = core::ptr::null_mut();
    v_res_2388_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg(v_env_2380_, v_a_2381_, v_a_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
    lean_dec(v___y_2386_);
    lean_dec_ref(v___y_2385_);
    lean_dec(v___y_2384_);
    lean_dec_ref(v___y_2383_);
    return v_res_2388_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__2(
    mut v_env_2389_: *mut LeanObject,
    mut v_as_2390_: *mut LeanObject,
    mut v_sz_2391_: usize,
    mut v_i_2392_: usize,
    mut v_b_2393_: *mut LeanObject,
    mut v___y_2394_: *mut LeanObject,
    mut v___y_2395_: *mut LeanObject,
    mut v___y_2396_: *mut LeanObject,
    mut v___y_2397_: *mut LeanObject,
    mut v___y_2398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2400_: u8 = 0;
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v_a_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: usize = 0;
    let mut v___x_2414_: usize = 0;
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut v_a_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2420_: u8 = 0;
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2400_ = lean_usize_dec_lt(v_i_2392_, v_sz_2391_);
                if v___x_2400_ == 0 {
                    lean_dec_ref(v_env_2389_);
                    v___x_2401_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2401_, 0, v_b_2393_);
                    return v___x_2401_;
                } else {
                    v_a_2402_ = lean_array_uget_borrowed(v_as_2390_, v_i_2392_);
                    lean_inc(v_a_2402_);
                    lean_inc_ref(v_env_2389_);
                    v___x_2403_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg(v_env_2389_, v_a_2402_, v_b_2393_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
                    if lean_obj_tag(v___x_2403_) == 0 {
                        v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
                        v_isSharedCheck_2416_ = (!lean_is_exclusive(v___x_2403_)) as u8;
                        if v_isSharedCheck_2416_ == 0 {
                            v___x_2406_ = v___x_2403_;
                            v_isShared_2407_ = v_isSharedCheck_2416_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2404_);
                            lean_dec(v___x_2403_);
                            v___x_2406_ = lean_box(0);
                            v_isShared_2407_ = v_isSharedCheck_2416_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_env_2389_);
                        v_a_2417_ = lean_ctor_get(v___x_2403_, 0);
                        v_isSharedCheck_2424_ = (!lean_is_exclusive(v___x_2403_)) as u8;
                        if v_isSharedCheck_2424_ == 0 {
                            v___x_2419_ = v___x_2403_;
                            v_isShared_2420_ = v_isSharedCheck_2424_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2417_);
                            lean_dec(v___x_2403_);
                            v___x_2419_ = lean_box(0);
                            v_isShared_2420_ = v_isSharedCheck_2424_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2404_) == 0 {
                    lean_dec_ref(v_env_2389_);
                    v_a_2408_ = lean_ctor_get(v_a_2404_, 0);
                    lean_inc(v_a_2408_);
                    lean_dec_ref_known(v_a_2404_, 1);
                    if v_isShared_2407_ == 0 {
                        lean_ctor_set(v___x_2406_, 0, v_a_2408_);
                        v___x_2410_ = v___x_2406_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2408_);
                        v___x_2410_ = v_reuseFailAlloc_2411_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2406_);
                    v_a_2412_ = lean_ctor_get(v_a_2404_, 0);
                    lean_inc(v_a_2412_);
                    lean_dec_ref_known(v_a_2404_, 1);
                    v___x_2413_ = 1usize;
                    v___x_2414_ = lean_usize_add(v_i_2392_, v___x_2413_);
                    v_i_2392_ = v___x_2414_;
                    v_b_2393_ = v_a_2412_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_2410_;
            }
            3 => {
                if v_isShared_2420_ == 0 {
                    v___x_2422_ = v___x_2419_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
                    v___x_2422_ = v_reuseFailAlloc_2423_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__2___boxed(
    mut v_env_2425_: *mut LeanObject,
    mut v_as_2426_: *mut LeanObject,
    mut v_sz_2427_: *mut LeanObject,
    mut v_i_2428_: *mut LeanObject,
    mut v_b_2429_: *mut LeanObject,
    mut v___y_2430_: *mut LeanObject,
    mut v___y_2431_: *mut LeanObject,
    mut v___y_2432_: *mut LeanObject,
    mut v___y_2433_: *mut LeanObject,
    mut v___y_2434_: *mut LeanObject,
    mut v___y_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2436_: usize = 0;
    let mut v_i_boxed_2437_: usize = 0;
    let mut v_res_2438_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2436_ = lean_unbox_usize(v_sz_2427_);
    lean_dec(v_sz_2427_);
    v_i_boxed_2437_ = lean_unbox_usize(v_i_2428_);
    lean_dec(v_i_2428_);
    v_res_2438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__2(v_env_2425_, v_as_2426_, v_sz_boxed_2436_, v_i_boxed_2437_, v_b_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
    lean_dec(v___y_2434_);
    lean_dec_ref(v___y_2433_);
    lean_dec(v___y_2432_);
    lean_dec_ref(v___y_2431_);
    lean_dec(v___y_2430_);
    lean_dec_ref(v_as_2426_);
    return v_res_2438_;
}
pub unsafe fn _init_l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    v___x_2439_ = lean_box(0);
    v___x_2440_ = lean_unsigned_to_nat(16);
    v___x_2441_ = lean_mk_array(v___x_2440_, v___x_2439_);
    return v___x_2441_;
}
pub unsafe fn _init_l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eligibleHeaderDecls_2444_: *mut LeanObject = core::ptr::null_mut();
    v___x_2442_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___closed__0_once
        ),
        _init_l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___closed__0,
    );
    v___x_2443_ = lean_unsigned_to_nat(0);
    v_eligibleHeaderDecls_2444_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_eligibleHeaderDecls_2444_, 0, v___x_2443_);
    lean_ctor_set(v_eligibleHeaderDecls_2444_, 1, v___x_2442_);
    return v_eligibleHeaderDecls_2444_;
}
pub unsafe fn l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0(
    mut v_env_2445_: *mut LeanObject,
    mut v___y_2446_: *mut LeanObject,
    mut v___y_2447_: *mut LeanObject,
    mut v___y_2448_: *mut LeanObject,
    mut v___y_2449_: *mut LeanObject,
    mut v___y_2450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2081_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eligibleHeaderDecls_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2457_: usize = 0;
    let mut v___x_2458_: usize = 0;
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2469_: u8 = 0;
    let mut v_val_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2473_: u8 = 0;
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2452_ = lean_st_ref_get(v___y_2446_);
                if lean_obj_tag(v___x_2452_) == 0 {
                    lean_inc_ref(v_env_2445_);
                    v___x_2453_ = l_Lean_Environment_constants(v_env_2445_);
                    v_map_u2081_2454_ = lean_ctor_get(v___x_2453_, 0);
                    lean_inc_ref(v_map_u2081_2454_);
                    lean_dec_ref(v___x_2453_);
                    v_buckets_2455_ = lean_ctor_get(v_map_u2081_2454_, 1);
                    lean_inc_ref(v_buckets_2455_);
                    lean_dec_ref(v_map_u2081_2454_);
                    v_eligibleHeaderDecls_2456_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___closed__1_once), _init_l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___closed__1);
                    v_sz_2457_ = lean_array_size(v_buckets_2455_);
                    v___x_2458_ = 0usize;
                    v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__2(v_env_2445_, v_buckets_2455_, v_sz_2457_, v___x_2458_, v_eligibleHeaderDecls_2456_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
                    lean_dec_ref(v_buckets_2455_);
                    if lean_obj_tag(v___x_2459_) == 0 {
                        v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
                        v_isSharedCheck_2469_ = (!lean_is_exclusive(v___x_2459_)) as u8;
                        if v_isSharedCheck_2469_ == 0 {
                            v___x_2462_ = v___x_2459_;
                            v_isShared_2463_ = v_isSharedCheck_2469_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2460_);
                            lean_dec(v___x_2459_);
                            v___x_2462_ = lean_box(0);
                            v_isShared_2463_ = v_isSharedCheck_2469_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_2459_;
                    }
                } else {
                    lean_dec_ref(v_env_2445_);
                    v_val_2470_ = lean_ctor_get(v___x_2452_, 0);
                    v_isSharedCheck_2477_ = (!lean_is_exclusive(v___x_2452_)) as u8;
                    if v_isSharedCheck_2477_ == 0 {
                        v___x_2472_ = v___x_2452_;
                        v_isShared_2473_ = v_isSharedCheck_2477_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_2470_);
                        lean_dec(v___x_2452_);
                        v___x_2472_ = lean_box(0);
                        v_isShared_2473_ = v_isSharedCheck_2477_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_2460_);
                v___x_2464_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2464_, 0, v_a_2460_);
                v___x_2465_ = lean_st_ref_set(v___y_2446_, v___x_2464_);
                if v_isShared_2463_ == 0 {
                    v___x_2467_ = v___x_2462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2460_);
                    v___x_2467_ = v_reuseFailAlloc_2468_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2467_;
            }
            3 => {
                if v_isShared_2473_ == 0 {
                    lean_ctor_set_tag(v___x_2472_, 0);
                    v___x_2475_ = v___x_2472_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_val_2470_);
                    v___x_2475_ = v_reuseFailAlloc_2476_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___boxed(
    mut v_env_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
    mut v___y_2481_: *mut LeanObject,
    mut v___y_2482_: *mut LeanObject,
    mut v___y_2483_: *mut LeanObject,
    mut v___y_2484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2485_: *mut LeanObject = core::ptr::null_mut();
    v_res_2485_ = l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0(
        v_env_2478_,
        v___y_2479_,
        v___y_2480_,
        v___y_2481_,
        v___y_2482_,
        v___y_2483_,
    );
    lean_dec(v___y_2483_);
    lean_dec_ref(v___y_2482_);
    lean_dec(v___y_2481_);
    lean_dec_ref(v___y_2480_);
    lean_dec(v___y_2479_);
    return v_res_2485_;
}
pub unsafe fn l_Lean_Server_Completion_getEligibleHeaderDecls(
    mut v_env_2486_: *mut LeanObject,
    mut v_a_2487_: *mut LeanObject,
    mut v_a_2488_: *mut LeanObject,
    mut v_a_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    v___f_2492_ = lean_alloc_closure(
        l_Lean_Server_Completion_getEligibleHeaderDecls___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_2492_, 0, v_env_2486_);
    v___x_2493_ = l_Lean_Server_Completion_eligibleHeaderDeclsMutex;
    v___x_2494_ = l_Std_Mutex_atomically___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__3___redArg(v___x_2493_, v___f_2492_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
    return v___x_2494_;
}
pub unsafe fn l_Lean_Server_Completion_getEligibleHeaderDecls___boxed(
    mut v_env_2495_: *mut LeanObject,
    mut v_a_2496_: *mut LeanObject,
    mut v_a_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
    mut v_a_2499_: *mut LeanObject,
    mut v_a_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2501_: *mut LeanObject = core::ptr::null_mut();
    v_res_2501_ = l_Lean_Server_Completion_getEligibleHeaderDecls(
        v_env_2495_,
        v_a_2496_,
        v_a_2497_,
        v_a_2498_,
        v_a_2499_,
    );
    lean_dec(v_a_2499_);
    lean_dec_ref(v_a_2498_);
    lean_dec(v_a_2497_);
    lean_dec_ref(v_a_2496_);
    return v_res_2501_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0(
    mut v_00_u03b2_2502_: *mut LeanObject,
    mut v_m_2503_: *mut LeanObject,
    mut v_a_2504_: *mut LeanObject,
    mut v_b_2505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    v___x_2506_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0___redArg(v_m_2503_, v_a_2504_, v_b_2505_);
    return v___x_2506_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1(
    mut v_env_2507_: *mut LeanObject,
    mut v_a_2508_: *mut LeanObject,
    mut v_a_2509_: *mut LeanObject,
    mut v___y_2510_: *mut LeanObject,
    mut v___y_2511_: *mut LeanObject,
    mut v___y_2512_: *mut LeanObject,
    mut v___y_2513_: *mut LeanObject,
    mut v___y_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    v___x_2516_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___redArg(v_env_2507_, v_a_2508_, v_a_2509_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
    return v___x_2516_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1___boxed(
    mut v_env_2517_: *mut LeanObject,
    mut v_a_2518_: *mut LeanObject,
    mut v_a_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
    mut v___y_2521_: *mut LeanObject,
    mut v___y_2522_: *mut LeanObject,
    mut v___y_2523_: *mut LeanObject,
    mut v___y_2524_: *mut LeanObject,
    mut v___y_2525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2526_: *mut LeanObject = core::ptr::null_mut();
    v_res_2526_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__1(v_env_2517_, v_a_2518_, v_a_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
    lean_dec(v___y_2524_);
    lean_dec_ref(v___y_2523_);
    lean_dec(v___y_2522_);
    lean_dec_ref(v___y_2521_);
    lean_dec(v___y_2520_);
    return v_res_2526_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__0(
    mut v_00_u03b2_2527_: *mut LeanObject,
    mut v_a_2528_: *mut LeanObject,
    mut v_x_2529_: *mut LeanObject,
) -> u8 {
    let mut v___x_2530_: u8 = 0;
    v___x_2530_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__0___redArg(v_a_2528_, v_x_2529_);
    return v___x_2530_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__0___boxed(
    mut v_00_u03b2_2531_: *mut LeanObject,
    mut v_a_2532_: *mut LeanObject,
    mut v_x_2533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2534_: u8 = 0;
    let mut v_r_2535_: *mut LeanObject = core::ptr::null_mut();
    v_res_2534_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__0(v_00_u03b2_2531_, v_a_2532_, v_x_2533_);
    lean_dec(v_x_2533_);
    lean_dec(v_a_2532_);
    v_r_2535_ = lean_box((v_res_2534_) as usize);
    return v_r_2535_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1(
    mut v_00_u03b2_2536_: *mut LeanObject,
    mut v_data_2537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    v___x_2538_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1___redArg(v_data_2537_);
    return v___x_2538_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__2(
    mut v_00_u03b2_2539_: *mut LeanObject,
    mut v_a_2540_: *mut LeanObject,
    mut v_b_2541_: *mut LeanObject,
    mut v_x_2542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    v___x_2543_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__2___redArg(v_a_2540_, v_b_2541_, v_x_2542_);
    return v___x_2543_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2544_: *mut LeanObject,
    mut v_i_2545_: *mut LeanObject,
    mut v_source_2546_: *mut LeanObject,
    mut v_target_2547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    v___x_2548_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3___redArg(v_i_2545_, v_source_2546_, v_target_2547_);
    return v___x_2548_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_2549_: *mut LeanObject,
    mut v_x_2550_: *mut LeanObject,
    mut v_x_2551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    v___x_2552_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg(v_x_2550_, v_x_2551_);
    return v___x_2552_;
}
pub unsafe fn l_Lean_Server_Completion_forEligibleDeclsM___redArg___lam__0(
    mut v_f_2553_: *mut LeanObject,
    mut v_x_2554_: *mut LeanObject,
    mut v___y_2555_: *mut LeanObject,
    mut v___y_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    v___x_2557_ = lean_apply_2(v_f_2553_, v___y_2555_, v___y_2556_);
    return v___x_2557_;
}
pub unsafe fn l_Lean_Server_Completion_forEligibleDeclsM___redArg___lam__1(
    mut v_inst_2558_: *mut LeanObject,
    mut v___f_2559_: *mut LeanObject,
    mut v_x_2560_: *mut LeanObject,
    mut v___y_2561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    v___x_2562_ = lean_box(0);
    v___x_2563_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_2558_,
        v___f_2559_,
        v___x_2562_,
        v___y_2561_,
    );
    return v___x_2563_;
}
pub unsafe fn l_Lean_Server_Completion_forEligibleDeclsM___redArg___lam__2(
    mut v_env_2564_: *mut LeanObject,
    mut v_toApplicative_2565_: *mut LeanObject,
    mut v_f_2566_: *mut LeanObject,
    mut v_name_2567_: *mut LeanObject,
    mut v_c_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2569_: u8 = 0;
    lean_inc(v_name_2567_);
    v___x_2569_ = l_Lean_Meta_allowCompletion(v_env_2564_, v_name_2567_);
    if v___x_2569_ == 0 {
        let mut v_toPure_2570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_c_2568_);
        lean_dec(v_name_2567_);
        lean_dec(v_f_2566_);
        v_toPure_2570_ = lean_ctor_get(v_toApplicative_2565_, 1);
        lean_inc(v_toPure_2570_);
        lean_dec_ref(v_toApplicative_2565_);
        v___x_2571_ = lean_box(0);
        v___x_2572_ = lean_apply_2(v_toPure_2570_, lean_box(0), v___x_2571_);
        return v___x_2572_;
    } else {
        let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_2565_);
        lean_inc_ref(v_c_2568_);
        v___x_2573_ = lean_alloc_closure(
            l_Lean_Server_Completion_getCompletionKindForDecl___boxed as *mut core::ffi::c_void,
            6,
            1,
        );
        lean_closure_set(v___x_2573_, 0, v_c_2568_);
        lean_inc(v_name_2567_);
        v___x_2574_ = lean_alloc_closure(
            l_Lean_Server_Completion_getCompletionTagsForDecl___boxed as *mut core::ffi::c_void,
            6,
            1,
        );
        lean_closure_set(v___x_2574_, 0, v_name_2567_);
        v___x_2575_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_2575_, 0, v_c_2568_);
        lean_ctor_set(v___x_2575_, 1, v___x_2573_);
        lean_ctor_set(v___x_2575_, 2, v___x_2574_);
        v___x_2576_ = lean_apply_2(v_f_2566_, v_name_2567_, v___x_2575_);
        return v___x_2576_;
    }
}
pub unsafe fn l_Lean_Server_Completion_forEligibleDeclsM___redArg___lam__3(
    mut v_env_2577_: *mut LeanObject,
    mut v_inst_2578_: *mut LeanObject,
    mut v___f_2579_: *mut LeanObject,
    mut v_____r_2580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    v___x_2581_ = l_Lean_Environment_constants(v_env_2577_);
    v_map_u2082_2582_ = lean_ctor_get(v___x_2581_, 1);
    lean_inc_ref(v_map_u2082_2582_);
    lean_dec_ref(v___x_2581_);
    v___x_2583_ =
        l_Lean_PersistentHashMap_forM___redArg(v_inst_2578_, v_map_u2082_2582_, v___f_2579_);
    return v___x_2583_;
}
pub unsafe fn l_Lean_Server_Completion_forEligibleDeclsM___redArg___lam__4(
    mut v_toApplicative_2584_: *mut LeanObject,
    mut v_toBind_2585_: *mut LeanObject,
    mut v___f_2586_: *mut LeanObject,
    mut v_inst_2587_: *mut LeanObject,
    mut v___f_2588_: *mut LeanObject,
    mut v_____do__lift_2589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: u8 = 0;
    v_buckets_2590_ = lean_ctor_get(v_____do__lift_2589_, 1);
    lean_inc_ref(v_buckets_2590_);
    lean_dec_ref(v_____do__lift_2589_);
    v___x_2591_ = lean_unsigned_to_nat(0);
    v___x_2592_ = lean_array_get_size(v_buckets_2590_);
    v___x_2593_ = lean_box(0);
    v___x_2594_ = lean_nat_dec_lt(v___x_2591_, v___x_2592_);
    if v___x_2594_ == 0 {
        let mut v_toPure_2595_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_buckets_2590_);
        lean_dec(v___f_2588_);
        lean_dec_ref(v_inst_2587_);
        v_toPure_2595_ = lean_ctor_get(v_toApplicative_2584_, 1);
        lean_inc(v_toPure_2595_);
        lean_dec_ref(v_toApplicative_2584_);
        v___x_2596_ = lean_apply_2(v_toPure_2595_, lean_box(0), v___x_2593_);
        v___x_2597_ = lean_apply_4(
            v_toBind_2585_,
            lean_box(0),
            lean_box(0),
            v___x_2596_,
            v___f_2586_,
        );
        return v___x_2597_;
    } else {
        let mut v___x_2598_: u8 = 0;
        v___x_2598_ = lean_nat_dec_le(v___x_2592_, v___x_2592_);
        if v___x_2598_ == 0 {
            if v___x_2594_ == 0 {
                let mut v_toPure_2599_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_buckets_2590_);
                lean_dec(v___f_2588_);
                lean_dec_ref(v_inst_2587_);
                v_toPure_2599_ = lean_ctor_get(v_toApplicative_2584_, 1);
                lean_inc(v_toPure_2599_);
                lean_dec_ref(v_toApplicative_2584_);
                v___x_2600_ = lean_apply_2(v_toPure_2599_, lean_box(0), v___x_2593_);
                v___x_2601_ = lean_apply_4(
                    v_toBind_2585_,
                    lean_box(0),
                    lean_box(0),
                    v___x_2600_,
                    v___f_2586_,
                );
                return v___x_2601_;
            } else {
                let mut v___x_2602_: usize = 0;
                let mut v___x_2603_: usize = 0;
                let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toApplicative_2584_);
                v___x_2602_ = 0usize;
                v___x_2603_ = lean_usize_of_nat(v___x_2592_);
                v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_2587_,
                    v___f_2588_,
                    v_buckets_2590_,
                    v___x_2602_,
                    v___x_2603_,
                    v___x_2593_,
                );
                v___x_2605_ = lean_apply_4(
                    v_toBind_2585_,
                    lean_box(0),
                    lean_box(0),
                    v___x_2604_,
                    v___f_2586_,
                );
                return v___x_2605_;
            }
        } else {
            let mut v___x_2606_: usize = 0;
            let mut v___x_2607_: usize = 0;
            let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toApplicative_2584_);
            v___x_2606_ = 0usize;
            v___x_2607_ = lean_usize_of_nat(v___x_2592_);
            v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_2587_,
                v___f_2588_,
                v_buckets_2590_,
                v___x_2606_,
                v___x_2607_,
                v___x_2593_,
            );
            v___x_2609_ = lean_apply_4(
                v_toBind_2585_,
                lean_box(0),
                lean_box(0),
                v___x_2608_,
                v___f_2586_,
            );
            return v___x_2609_;
        }
    }
}
pub unsafe fn l_Lean_Server_Completion_forEligibleDeclsM___redArg___lam__5(
    mut v_toApplicative_2610_: *mut LeanObject,
    mut v_f_2611_: *mut LeanObject,
    mut v_inst_2612_: *mut LeanObject,
    mut v_toBind_2613_: *mut LeanObject,
    mut v___f_2614_: *mut LeanObject,
    mut v_inst_2615_: *mut LeanObject,
    mut v_env_2616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_toApplicative_2610_);
    lean_inc_ref_n(v_env_2616_, 2);
    v___f_2617_ = lean_alloc_closure(
        l_Lean_Server_Completion_forEligibleDeclsM___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2617_, 0, v_env_2616_);
    lean_closure_set(v___f_2617_, 1, v_toApplicative_2610_);
    lean_closure_set(v___f_2617_, 2, v_f_2611_);
    lean_inc_ref(v_inst_2612_);
    v___f_2618_ = lean_alloc_closure(
        l_Lean_Server_Completion_forEligibleDeclsM___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2618_, 0, v_env_2616_);
    lean_closure_set(v___f_2618_, 1, v_inst_2612_);
    lean_closure_set(v___f_2618_, 2, v___f_2617_);
    lean_inc(v_toBind_2613_);
    v___f_2619_ = lean_alloc_closure(
        l_Lean_Server_Completion_forEligibleDeclsM___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2619_, 0, v_toApplicative_2610_);
    lean_closure_set(v___f_2619_, 1, v_toBind_2613_);
    lean_closure_set(v___f_2619_, 2, v___f_2618_);
    lean_closure_set(v___f_2619_, 3, v_inst_2612_);
    lean_closure_set(v___f_2619_, 4, v___f_2614_);
    v___x_2620_ = lean_alloc_closure(
        l_Lean_Server_Completion_getEligibleHeaderDecls___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_2620_, 0, v_env_2616_);
    v___x_2621_ = lean_apply_2(v_inst_2615_, lean_box(0), v___x_2620_);
    v___x_2622_ = lean_apply_4(
        v_toBind_2613_,
        lean_box(0),
        lean_box(0),
        v___x_2621_,
        v___f_2619_,
    );
    return v___x_2622_;
}
pub unsafe fn l_Lean_Server_Completion_forEligibleDeclsM___redArg(
    mut v_inst_2623_: *mut LeanObject,
    mut v_inst_2624_: *mut LeanObject,
    mut v_inst_2625_: *mut LeanObject,
    mut v_f_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2627_ = lean_ctor_get(v_inst_2623_, 0);
    lean_inc_ref(v_toApplicative_2627_);
    v_toBind_2628_ = lean_ctor_get(v_inst_2623_, 1);
    lean_inc_n(v_toBind_2628_, 2);
    v_getEnv_2629_ = lean_ctor_get(v_inst_2624_, 0);
    lean_inc(v_getEnv_2629_);
    lean_dec_ref(v_inst_2624_);
    lean_inc(v_f_2626_);
    v___f_2630_ = lean_alloc_closure(
        l_Lean_Server_Completion_forEligibleDeclsM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2630_, 0, v_f_2626_);
    lean_inc_ref(v_inst_2623_);
    v___f_2631_ = lean_alloc_closure(
        l_Lean_Server_Completion_forEligibleDeclsM___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2631_, 0, v_inst_2623_);
    lean_closure_set(v___f_2631_, 1, v___f_2630_);
    v___f_2632_ = lean_alloc_closure(
        l_Lean_Server_Completion_forEligibleDeclsM___redArg___lam__5 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_2632_, 0, v_toApplicative_2627_);
    lean_closure_set(v___f_2632_, 1, v_f_2626_);
    lean_closure_set(v___f_2632_, 2, v_inst_2623_);
    lean_closure_set(v___f_2632_, 3, v_toBind_2628_);
    lean_closure_set(v___f_2632_, 4, v___f_2631_);
    lean_closure_set(v___f_2632_, 5, v_inst_2625_);
    v___x_2633_ = lean_apply_4(
        v_toBind_2628_,
        lean_box(0),
        lean_box(0),
        v_getEnv_2629_,
        v___f_2632_,
    );
    return v___x_2633_;
}
pub unsafe fn l_Lean_Server_Completion_forEligibleDeclsM(
    mut v_m_2634_: *mut LeanObject,
    mut v_inst_2635_: *mut LeanObject,
    mut v_inst_2636_: *mut LeanObject,
    mut v_inst_2637_: *mut LeanObject,
    mut v_f_2638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    v___x_2639_ = l_Lean_Server_Completion_forEligibleDeclsM___redArg(
        v_inst_2635_,
        v_inst_2636_,
        v_inst_2637_,
        v_f_2638_,
    );
    return v___x_2639_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1_spec__2___redArg(
    mut v_keys_2640_: *mut LeanObject,
    mut v_i_2641_: *mut LeanObject,
    mut v_k_2642_: *mut LeanObject,
) -> u8 {
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: u8 = 0;
    let mut v_k_x27_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: u8 = 0;
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2643_ = lean_array_get_size(v_keys_2640_);
                v___x_2644_ = lean_nat_dec_lt(v_i_2641_, v___x_2643_);
                if v___x_2644_ == 0 {
                    lean_dec(v_i_2641_);
                    return v___x_2644_;
                } else {
                    v_k_x27_2645_ = lean_array_fget_borrowed(v_keys_2640_, v_i_2641_);
                    v___x_2646_ = lean_name_eq(v_k_2642_, v_k_x27_2645_);
                    if v___x_2646_ == 0 {
                        v___x_2647_ = lean_unsigned_to_nat(1);
                        v___x_2648_ = lean_nat_add(v_i_2641_, v___x_2647_);
                        lean_dec(v_i_2641_);
                        v_i_2641_ = v___x_2648_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_2641_);
                        return v___x_2646_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_keys_2650_: *mut LeanObject,
    mut v_i_2651_: *mut LeanObject,
    mut v_k_2652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2653_: u8 = 0;
    let mut v_r_2654_: *mut LeanObject = core::ptr::null_mut();
    v_res_2653_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1_spec__2___redArg(v_keys_2650_, v_i_2651_, v_k_2652_);
    lean_dec(v_k_2652_);
    lean_dec_ref(v_keys_2650_);
    v_r_2654_ = lean_box((v_res_2653_) as usize);
    return v_r_2654_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_2655_: usize = 0;
    let mut v___x_2656_: usize = 0;
    let mut v___x_2657_: usize = 0;
    v___x_2655_ = 5usize;
    v___x_2656_ = 1usize;
    v___x_2657_ = lean_usize_shift_left(v___x_2656_, v___x_2655_);
    return v___x_2657_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_2658_: usize = 0;
    let mut v___x_2659_: usize = 0;
    let mut v___x_2660_: usize = 0;
    v___x_2658_ = 1usize;
    v___x_2659_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___closed__0);
    v___x_2660_ = lean_usize_sub(v___x_2659_, v___x_2658_);
    return v___x_2660_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg(
    mut v_x_2661_: *mut LeanObject,
    mut v_x_2662_: usize,
    mut v_x_2663_: *mut LeanObject,
) -> u8 {
    let mut v_es_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: usize = 0;
    let mut v___x_2667_: usize = 0;
    let mut v___x_2668_: usize = 0;
    let mut v_j_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    let mut v_node_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: usize = 0;
    let mut v___x_2676_: u8 = 0;
    let mut v_ks_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2661_) == 0 {
                    v_es_2664_ = lean_ctor_get(v_x_2661_, 0);
                    v___x_2665_ = lean_box(2);
                    v___x_2666_ = 5usize;
                    v___x_2667_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___closed__1);
                    v___x_2668_ = lean_usize_land(v_x_2662_, v___x_2667_);
                    v_j_2669_ = lean_usize_to_nat(v___x_2668_);
                    v___x_2670_ = lean_array_get_borrowed(v___x_2665_, v_es_2664_, v_j_2669_);
                    lean_dec(v_j_2669_);
                    match lean_obj_tag(v___x_2670_) {
                        0 => {
                            v_key_2671_ = lean_ctor_get(v___x_2670_, 0);
                            v___x_2672_ = lean_name_eq(v_x_2663_, v_key_2671_);
                            return v___x_2672_;
                        }
                        1 => {
                            v_node_2673_ = lean_ctor_get(v___x_2670_, 0);
                            v___x_2674_ = lean_usize_shift_right(v_x_2662_, v___x_2666_);
                            v_x_2661_ = v_node_2673_;
                            v_x_2662_ = v___x_2674_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2676_ = 0;
                            return v___x_2676_;
                        }
                    }
                } else {
                    v_ks_2677_ = lean_ctor_get(v_x_2661_, 0);
                    v___x_2678_ = lean_unsigned_to_nat(0);
                    v___x_2679_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1_spec__2___redArg(v_ks_2677_, v___x_2678_, v_x_2663_);
                    return v___x_2679_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg___boxed(
    mut v_x_2680_: *mut LeanObject,
    mut v_x_2681_: *mut LeanObject,
    mut v_x_2682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_231__boxed_2683_: usize = 0;
    let mut v_res_2684_: u8 = 0;
    let mut v_r_2685_: *mut LeanObject = core::ptr::null_mut();
    v_x_231__boxed_2683_ = lean_unbox_usize(v_x_2681_);
    lean_dec(v_x_2681_);
    v_res_2684_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg(v_x_2680_, v_x_231__boxed_2683_, v_x_2682_);
    lean_dec(v_x_2682_);
    lean_dec_ref(v_x_2680_);
    v_r_2685_ = lean_box((v_res_2684_) as usize);
    return v_r_2685_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1___redArg(
    mut v_x_2686_: *mut LeanObject,
    mut v_x_2687_: *mut LeanObject,
) -> u8 {
    let mut v___y_2689_: u64 = 0;
    let mut v___x_2690_: usize = 0;
    let mut v___x_2691_: u8 = 0;
    let mut v___x_2692_: u64 = 0;
    let mut v_hash_2693_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2687_) == 0 {
                    v___x_2692_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0);
                    v___y_2689_ = v___x_2692_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2693_ = lean_ctor_get_uint64(
                        v_x_2687_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2689_ = v_hash_2693_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2690_ = lean_uint64_to_usize(v___y_2689_);
                v___x_2691_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg(v_x_2686_, v___x_2690_, v_x_2687_);
                return v___x_2691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1___redArg___boxed(
    mut v_x_2694_: *mut LeanObject,
    mut v_x_2695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2696_: u8 = 0;
    let mut v_r_2697_: *mut LeanObject = core::ptr::null_mut();
    v_res_2696_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1___redArg(v_x_2694_, v_x_2695_);
    lean_dec(v_x_2695_);
    lean_dec_ref(v_x_2694_);
    v_r_2697_ = lean_box((v_res_2696_) as usize);
    return v_r_2697_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Completion_allowCompletion_spec__0___redArg(
    mut v_m_2698_: *mut LeanObject,
    mut v_a_2699_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2703_: u64 = 0;
    let mut v___x_2704_: u64 = 0;
    let mut v___x_2705_: u64 = 0;
    let mut v_fold_2706_: u64 = 0;
    let mut v___x_2707_: u64 = 0;
    let mut v___x_2708_: u64 = 0;
    let mut v___x_2709_: u64 = 0;
    let mut v___x_2710_: usize = 0;
    let mut v___x_2711_: usize = 0;
    let mut v___x_2712_: usize = 0;
    let mut v___x_2713_: usize = 0;
    let mut v___x_2714_: usize = 0;
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: u8 = 0;
    let mut v___x_2717_: u64 = 0;
    let mut v_hash_2718_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2700_ = lean_ctor_get(v_m_2698_, 1);
                v___x_2701_ = lean_array_get_size(v_buckets_2700_);
                if lean_obj_tag(v_a_2699_) == 0 {
                    v___x_2717_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__1_spec__3_spec__6___redArg___closed__0);
                    v___y_2703_ = v___x_2717_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2718_ = lean_ctor_get_uint64(
                        v_a_2699_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2703_ = v_hash_2718_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2704_ = 32u64;
                v___x_2705_ = lean_uint64_shift_right(v___y_2703_, v___x_2704_);
                v_fold_2706_ = lean_uint64_xor(v___y_2703_, v___x_2705_);
                v___x_2707_ = 16u64;
                v___x_2708_ = lean_uint64_shift_right(v_fold_2706_, v___x_2707_);
                v___x_2709_ = lean_uint64_xor(v_fold_2706_, v___x_2708_);
                v___x_2710_ = lean_uint64_to_usize(v___x_2709_);
                v___x_2711_ = lean_usize_of_nat(v___x_2701_);
                v___x_2712_ = 1usize;
                v___x_2713_ = lean_usize_sub(v___x_2711_, v___x_2712_);
                v___x_2714_ = lean_usize_land(v___x_2710_, v___x_2713_);
                v___x_2715_ = lean_array_uget_borrowed(v_buckets_2700_, v___x_2714_);
                v___x_2716_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Completion_getEligibleHeaderDecls_spec__0_spec__0___redArg(v_a_2699_, v___x_2715_);
                return v___x_2716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Completion_allowCompletion_spec__0___redArg___boxed(
    mut v_m_2719_: *mut LeanObject,
    mut v_a_2720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2721_: u8 = 0;
    let mut v_r_2722_: *mut LeanObject = core::ptr::null_mut();
    v_res_2721_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Completion_allowCompletion_spec__0___redArg(v_m_2719_, v_a_2720_);
    lean_dec(v_a_2720_);
    lean_dec_ref(v_m_2719_);
    v_r_2722_ = lean_box((v_res_2721_) as usize);
    return v_r_2722_;
}
pub unsafe fn l_Lean_Server_Completion_allowCompletion(
    mut v_eligibleHeaderDecls_2723_: *mut LeanObject,
    mut v_env_2724_: *mut LeanObject,
    mut v_declName_2725_: *mut LeanObject,
) -> u8 {
    let mut v___x_2726_: u8 = 0;
    v___x_2726_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Completion_allowCompletion_spec__0___redArg(v_eligibleHeaderDecls_2723_, v_declName_2725_);
    if v___x_2726_ == 0 {
        let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_2728_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2729_: u8 = 0;
        lean_inc_ref(v_env_2724_);
        v___x_2727_ = l_Lean_Environment_constants(v_env_2724_);
        v_map_u2082_2728_ = lean_ctor_get(v___x_2727_, 1);
        lean_inc_ref(v_map_u2082_2728_);
        lean_dec_ref(v___x_2727_);
        v___x_2729_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1___redArg(v_map_u2082_2728_, v_declName_2725_);
        lean_dec_ref(v_map_u2082_2728_);
        if v___x_2729_ == 0 {
            lean_dec(v_declName_2725_);
            lean_dec_ref(v_env_2724_);
            return v___x_2729_;
        } else {
            let mut v___x_2730_: u8 = 0;
            v___x_2730_ = l_Lean_Meta_allowCompletion(v_env_2724_, v_declName_2725_);
            return v___x_2730_;
        }
    } else {
        lean_dec(v_declName_2725_);
        lean_dec_ref(v_env_2724_);
        return v___x_2726_;
    }
}
pub unsafe fn l_Lean_Server_Completion_allowCompletion___boxed(
    mut v_eligibleHeaderDecls_2731_: *mut LeanObject,
    mut v_env_2732_: *mut LeanObject,
    mut v_declName_2733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2734_: u8 = 0;
    let mut v_r_2735_: *mut LeanObject = core::ptr::null_mut();
    v_res_2734_ = l_Lean_Server_Completion_allowCompletion(
        v_eligibleHeaderDecls_2731_,
        v_env_2732_,
        v_declName_2733_,
    );
    lean_dec_ref(v_eligibleHeaderDecls_2731_);
    v_r_2735_ = lean_box((v_res_2734_) as usize);
    return v_r_2735_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Completion_allowCompletion_spec__0(
    mut v_00_u03b2_2736_: *mut LeanObject,
    mut v_m_2737_: *mut LeanObject,
    mut v_a_2738_: *mut LeanObject,
) -> u8 {
    let mut v___x_2739_: u8 = 0;
    v___x_2739_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Completion_allowCompletion_spec__0___redArg(v_m_2737_, v_a_2738_);
    return v___x_2739_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Completion_allowCompletion_spec__0___boxed(
    mut v_00_u03b2_2740_: *mut LeanObject,
    mut v_m_2741_: *mut LeanObject,
    mut v_a_2742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2743_: u8 = 0;
    let mut v_r_2744_: *mut LeanObject = core::ptr::null_mut();
    v_res_2743_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Completion_allowCompletion_spec__0(v_00_u03b2_2740_, v_m_2741_, v_a_2742_);
    lean_dec(v_a_2742_);
    lean_dec_ref(v_m_2741_);
    v_r_2744_ = lean_box((v_res_2743_) as usize);
    return v_r_2744_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1(
    mut v_00_u03b2_2745_: *mut LeanObject,
    mut v_x_2746_: *mut LeanObject,
    mut v_x_2747_: *mut LeanObject,
) -> u8 {
    let mut v___x_2748_: u8 = 0;
    v___x_2748_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1___redArg(v_x_2746_, v_x_2747_);
    return v___x_2748_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1___boxed(
    mut v_00_u03b2_2749_: *mut LeanObject,
    mut v_x_2750_: *mut LeanObject,
    mut v_x_2751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2752_: u8 = 0;
    let mut v_r_2753_: *mut LeanObject = core::ptr::null_mut();
    v_res_2752_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1(
            v_00_u03b2_2749_,
            v_x_2750_,
            v_x_2751_,
        );
    lean_dec(v_x_2751_);
    lean_dec_ref(v_x_2750_);
    v_r_2753_ = lean_box((v_res_2752_) as usize);
    return v_r_2753_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1(
    mut v_00_u03b2_2754_: *mut LeanObject,
    mut v_x_2755_: *mut LeanObject,
    mut v_x_2756_: usize,
    mut v_x_2757_: *mut LeanObject,
) -> u8 {
    let mut v___x_2758_: u8 = 0;
    v___x_2758_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___redArg(v_x_2755_, v_x_2756_, v_x_2757_);
    return v___x_2758_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1___boxed(
    mut v_00_u03b2_2759_: *mut LeanObject,
    mut v_x_2760_: *mut LeanObject,
    mut v_x_2761_: *mut LeanObject,
    mut v_x_2762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_353__boxed_2763_: usize = 0;
    let mut v_res_2764_: u8 = 0;
    let mut v_r_2765_: *mut LeanObject = core::ptr::null_mut();
    v_x_353__boxed_2763_ = lean_unbox_usize(v_x_2761_);
    lean_dec(v_x_2761_);
    v_res_2764_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1(v_00_u03b2_2759_, v_x_2760_, v_x_353__boxed_2763_, v_x_2762_);
    lean_dec(v_x_2762_);
    lean_dec_ref(v_x_2760_);
    v_r_2765_ = lean_box((v_res_2764_) as usize);
    return v_r_2765_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1_spec__2(
    mut v_00_u03b2_2766_: *mut LeanObject,
    mut v_keys_2767_: *mut LeanObject,
    mut v_vals_2768_: *mut LeanObject,
    mut v_heq_2769_: *mut LeanObject,
    mut v_i_2770_: *mut LeanObject,
    mut v_k_2771_: *mut LeanObject,
) -> u8 {
    let mut v___x_2772_: u8 = 0;
    v___x_2772_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1_spec__2___redArg(v_keys_2767_, v_i_2770_, v_k_2771_);
    return v___x_2772_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_2773_: *mut LeanObject,
    mut v_keys_2774_: *mut LeanObject,
    mut v_vals_2775_: *mut LeanObject,
    mut v_heq_2776_: *mut LeanObject,
    mut v_i_2777_: *mut LeanObject,
    mut v_k_2778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2779_: u8 = 0;
    let mut v_r_2780_: *mut LeanObject = core::ptr::null_mut();
    v_res_2779_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_Completion_allowCompletion_spec__1_spec__1_spec__2(v_00_u03b2_2773_, v_keys_2774_, v_vals_2775_, v_heq_2776_, v_i_2777_, v_k_2778_);
    lean_dec(v_k_2778_);
    lean_dec_ref(v_vals_2775_);
    lean_dec_ref(v_keys_2774_);
    v_r_2780_ = lean_box((v_res_2779_) as usize);
    return v_r_2780_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Completion_EligibleHeaderDecls(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_CompletionName(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ProjFns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Mutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Deprecated(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Server_Completion_EligibleHeaderDecls_0__Lean_Server_Completion_initFn_00___x40_Lean_Server_Completion_EligibleHeaderDecls_1911833064____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Server_Completion_eligibleHeaderDeclsMutex = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Server_Completion_eligibleHeaderDeclsMutex);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Completion_EligibleHeaderDecls(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Completion_EligibleHeaderDecls(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_CompletionName(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ProjFns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_Mutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Deprecated(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion_EligibleHeaderDecls(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Completion_EligibleHeaderDecls(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_Completion_EligibleHeaderDecls(builtin);
}
