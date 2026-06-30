// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.FieldNotation
// Imports: Lean.Meta.WHNF Lean.PrettyPrinter.Delaborator.Attributes Lean.PrettyPrinter.Delaborator.Options Init.Data.Range.Polymorphic.Iterators
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_uget_borrowed, lean_infer_type,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq,
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_usize_add,
    lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_str___override, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_replaceRef,
};
use crate::r#gen::Lean::Class::lean_is_class;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getPrefix, l_Lean_Name_isAnonymous};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isExplicit, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_constName_x3f,
    l_Lean_Expr_consumeMData, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasMVar, l_Lean_Expr_isApp, l_Lean_Expr_isAppOf,
    l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName, l_Lean_MessageLog_add,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l_Lean_FVarId_getBinderInfo___redArg, l_Lean_FVarId_getType___redArg,
    l_Lean_FVarId_getUserName___redArg, l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProof;
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_unfoldDefinition_x3f, l_Lean_Meta_whnfCore,
    runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore_x3f;
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Attributes::{
    initialize_Lean_PrettyPrinter_Delaborator_Attributes, l_Lean_hasPPNoDotAttribute,
    runtime_initialize_Lean_PrettyPrinter_Delaborator_Attributes,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Options::{
    initialize_Lean_PrettyPrinter_Delaborator_Options,
    runtime_initialize_Lean_PrettyPrinter_Delaborator_Options,
};
use crate::r#gen::Lean::PrivateName::{l_Lean_isPrivateName, l_Lean_privateToUserName};
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_backward_privateInPublic, l_Lean_ResolveName_backward_privateInPublic_warn,
};
use crate::r#gen::Lean::Structure::{l_Lean_getFieldInfo_x3f, l_Lean_getStructureInfo_x3f};
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__2_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [80, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__2_value: leanh::LeanStringObject<167> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 167, m_capacity: 167, m_length: 166, m_data: [96, 32, 97, 99, 99, 101, 115, 115, 101, 100, 32, 112, 117, 98, 108, 105, 99, 108, 121, 59, 32, 116, 104, 105, 115, 32, 105, 115, 32, 97, 108, 108, 111, 119, 101, 100, 32, 111, 110, 108, 121, 32, 98, 101, 99, 97, 117, 115, 101, 32, 116, 104, 101, 32, 96, 98, 97, 99, 107, 119, 97, 114, 100, 46, 112, 114, 105, 118, 97, 116, 101, 73, 110, 80, 117, 98, 108, 105, 99, 96, 32, 111, 112, 116, 105, 111, 110, 32, 105, 115, 32, 101, 110, 97, 98, 108, 101, 100, 46, 32, 10, 10, 68, 105, 115, 97, 98, 108, 101, 32, 96, 98, 97, 99, 107, 119, 97, 114, 100, 46, 112, 114, 105, 118, 97, 116, 101, 73, 110, 80, 117, 98, 108, 105, 99, 46, 119, 97, 114, 110, 96, 32, 116, 111, 32, 115, 105, 108, 101, 110, 99, 101, 32, 116, 104, 105, 115, 32, 119, 97, 114, 110, 105, 110, 103, 46, 0]};
static mut l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName___closed__0: u64 = 0;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 111, 116, 105, 118, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,16911948307605359233 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [70, 117, 110, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___closed__0_value) as *mut leanh::LeanObject,920240211420121313 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0_spec__1(
    mut v_msgData_1905_: *mut leanh::LeanObject,
    mut v___y_1906_: *mut leanh::LeanObject,
    mut v___y_1907_: *mut leanh::LeanObject,
    mut v___y_1908_: *mut leanh::LeanObject,
    mut v___y_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1911_ = lean_st_ref_get(v___y_1909_);
    v_env_1912_ = leanh::lean_ctor_get(v___x_1911_, 0);
    leanh::lean_inc_ref(v_env_1912_);
    leanh::lean_dec(v___x_1911_);
    v___x_1913_ = lean_st_ref_get(v___y_1907_);
    v_mctx_1914_ = leanh::lean_ctor_get(v___x_1913_, 0);
    leanh::lean_inc_ref(v_mctx_1914_);
    leanh::lean_dec(v___x_1913_);
    v_lctx_1915_ = leanh::lean_ctor_get(v___y_1906_, 2);
    v_options_1916_ = leanh::lean_ctor_get(v___y_1908_, 2);
    leanh::lean_inc_ref(v_options_1916_);
    leanh::lean_inc_ref(v_lctx_1915_);
    v___x_1917_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1917_, 0, v_env_1912_);
    leanh::lean_ctor_set(v___x_1917_, 1, v_mctx_1914_);
    leanh::lean_ctor_set(v___x_1917_, 2, v_lctx_1915_);
    leanh::lean_ctor_set(v___x_1917_, 3, v_options_1916_);
    v___x_1918_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1918_, 0, v___x_1917_);
    leanh::lean_ctor_set(v___x_1918_, 1, v_msgData_1905_);
    v___x_1919_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1919_, 0, v___x_1918_);
    return v___x_1919_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1920_: *mut leanh::LeanObject,
    mut v___y_1921_: *mut leanh::LeanObject,
    mut v___y_1922_: *mut leanh::LeanObject,
    mut v___y_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1926_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0_spec__1(v_msgData_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
    leanh::lean_dec(v___y_1924_);
    leanh::lean_dec_ref(v___y_1923_);
    leanh::lean_dec(v___y_1922_);
    leanh::lean_dec_ref(v___y_1921_);
    return v_res_1926_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(
    mut v_msg_1927_: *mut leanh::LeanObject,
    mut v___y_1928_: *mut leanh::LeanObject,
    mut v___y_1929_: *mut leanh::LeanObject,
    mut v___y_1930_: *mut leanh::LeanObject,
    mut v___y_1931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1938_: u8 = 0;
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1933_ = leanh::lean_ctor_get(v___y_1930_, 5);
                v___x_1934_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0_spec__1(v_msg_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
                v_a_1935_ = leanh::lean_ctor_get(v___x_1934_, 0);
                v_isSharedCheck_1943_ = (!leanh::lean_is_exclusive(v___x_1934_)) as u8;
                if v_isSharedCheck_1943_ == 0 {
                    v___x_1937_ = v___x_1934_;
                    v_isShared_1938_ = v_isSharedCheck_1943_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1935_);
                    leanh::lean_dec(v___x_1934_);
                    v___x_1937_ = leanh::lean_box(0);
                    v_isShared_1938_ = v_isSharedCheck_1943_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1933_);
                v___x_1939_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1939_, 0, v_ref_1933_);
                leanh::lean_ctor_set(v___x_1939_, 1, v_a_1935_);
                if v_isShared_1938_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1937_, 1);
                    leanh::lean_ctor_set(v___x_1937_, 0, v___x_1939_);
                    v___x_1941_ = v___x_1937_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1942_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
                    v___x_1941_ = v_reuseFailAlloc_1942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg___boxed(
    mut v_msg_1944_: *mut leanh::LeanObject,
    mut v___y_1945_: *mut leanh::LeanObject,
    mut v___y_1946_: *mut leanh::LeanObject,
    mut v___y_1947_: *mut leanh::LeanObject,
    mut v___y_1948_: *mut leanh::LeanObject,
    mut v___y_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v_msg_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
    leanh::lean_dec(v___y_1948_);
    leanh::lean_dec_ref(v___y_1947_);
    leanh::lean_dec(v___y_1946_);
    leanh::lean_dec_ref(v___y_1945_);
    return v_res_1950_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__0;
    v___x_1953_ = l_Lean_stringToMessageData(v___x_1952_);
    return v___x_1953_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1955_ = l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__2;
    v___x_1956_ = l_Lean_stringToMessageData(v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0(
    mut v_constName_1957_: *mut leanh::LeanObject,
    mut v___y_1958_: *mut leanh::LeanObject,
    mut v___y_1959_: *mut leanh::LeanObject,
    mut v___y_1960_: *mut leanh::LeanObject,
    mut v___y_1961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: u8 = 0;
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1963_ = lean_st_ref_get(v___y_1961_);
                v_env_1964_ = leanh::lean_ctor_get(v___x_1963_, 0);
                leanh::lean_inc_ref(v_env_1964_);
                leanh::lean_dec(v___x_1963_);
                leanh::lean_inc(v_constName_1957_);
                v___x_1965_ = l_Lean_isInductiveCore_x3f(v_env_1964_, v_constName_1957_);
                if leanh::lean_obj_tag(v___x_1965_) == 0 {
                    v___x_1966_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__1);
                    v___x_1967_ = 0;
                    v___x_1968_ = l_Lean_MessageData_ofConstName(v_constName_1957_, v___x_1967_);
                    v___x_1969_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1969_, 0, v___x_1966_);
                    leanh::lean_ctor_set(v___x_1969_, 1, v___x_1968_);
                    v___x_1970_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__3_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__3);
                    v___x_1971_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1971_, 0, v___x_1969_);
                    leanh::lean_ctor_set(v___x_1971_, 1, v___x_1970_);
                    v___x_1972_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v___x_1971_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
                    return v___x_1972_;
                } else {
                    leanh::lean_dec(v_constName_1957_);
                    v_val_1973_ = leanh::lean_ctor_get(v___x_1965_, 0);
                    v_isSharedCheck_1980_ = (!leanh::lean_is_exclusive(v___x_1965_)) as u8;
                    if v_isSharedCheck_1980_ == 0 {
                        v___x_1975_ = v___x_1965_;
                        v_isShared_1976_ = v_isSharedCheck_1980_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1973_);
                        leanh::lean_dec(v___x_1965_);
                        v___x_1975_ = leanh::lean_box(0);
                        v_isShared_1976_ = v_isSharedCheck_1980_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1976_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1975_, 0);
                    v___x_1978_ = v___x_1975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1979_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_val_1973_);
                    v___x_1978_ = v_reuseFailAlloc_1979_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___boxed(
    mut v_constName_1981_: *mut leanh::LeanObject,
    mut v___y_1982_: *mut leanh::LeanObject,
    mut v___y_1983_: *mut leanh::LeanObject,
    mut v___y_1984_: *mut leanh::LeanObject,
    mut v___y_1985_: *mut leanh::LeanObject,
    mut v___y_1986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1987_ = l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0(v_constName_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
    leanh::lean_dec(v___y_1985_);
    leanh::lean_dec_ref(v___y_1984_);
    leanh::lean_dec(v___y_1983_);
    leanh::lean_dec_ref(v___y_1982_);
    return v_res_1987_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__1(
    mut v_c_1988_: *mut leanh::LeanObject,
    mut v_as_1989_: *mut leanh::LeanObject,
    mut v_i_1990_: usize,
    mut v_stop_1991_: usize,
) -> u8 {
    let mut v___x_1992_: u8 = 0;
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_projFn_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: u8 = 0;
    let mut v___x_1996_: usize = 0;
    let mut v___x_1997_: usize = 0;
    let mut v___x_1999_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1992_ = lean_usize_dec_eq(v_i_1990_, v_stop_1991_);
                if v___x_1992_ == 0 {
                    v___x_1993_ = lean_array_uget_borrowed(v_as_1989_, v_i_1990_);
                    v_projFn_1994_ = leanh::lean_ctor_get(v___x_1993_, 1);
                    v___x_1995_ = lean_name_eq(v_projFn_1994_, v_c_1988_);
                    if v___x_1995_ == 0 {
                        v___x_1996_ = 1usize;
                        v___x_1997_ = lean_usize_add(v_i_1990_, v___x_1996_);
                        v_i_1990_ = v___x_1997_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1995_;
                    }
                } else {
                    v___x_1999_ = 0;
                    return v___x_1999_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__1___boxed(
    mut v_c_2000_: *mut leanh::LeanObject,
    mut v_as_2001_: *mut leanh::LeanObject,
    mut v_i_2002_: *mut leanh::LeanObject,
    mut v_stop_2003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2004_: usize = 0;
    let mut v_stop_boxed_2005_: usize = 0;
    let mut v_res_2006_: u8 = 0;
    let mut v_r_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2004_ = leanh::lean_unbox_usize(v_i_2002_);
    leanh::lean_dec(v_i_2002_);
    v_stop_boxed_2005_ = leanh::lean_unbox_usize(v_stop_2003_);
    leanh::lean_dec(v_stop_2003_);
    v_res_2006_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__1(v_c_2000_, v_as_2001_, v_i_boxed_2004_, v_stop_boxed_2005_);
    leanh::lean_dec_ref(v_as_2001_);
    leanh::lean_dec(v_c_2000_);
    v_r_2007_ = leanh::lean_box((v_res_2006_) as usize);
    return v_r_2007_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo(
    mut v_c_2008_: *mut leanh::LeanObject,
    mut v_a_2009_: *mut leanh::LeanObject,
    mut v_a_2010_: *mut leanh::LeanObject,
    mut v_a_2011_: *mut leanh::LeanObject,
    mut v_a_2012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2022_: u8 = 0;
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2040_: u8 = 0;
    let mut v_numParams_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subobject_x3f_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: u8 = 0;
    let mut v___y_2045_: u8 = 0;
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_parentInfo_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v___x_2063_: usize = 0;
    let mut v___x_2064_: usize = 0;
    let mut v___x_2065_: u8 = 0;
    let mut v_numParams_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2079_: u8 = 0;
    let mut v_a_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2083_: u8 = 0;
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2087_: u8 = 0;
    let mut v_isSharedCheck_2088_: u8 = 0;
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2014_ = lean_st_ref_get(v_a_2012_);
                if leanh::lean_obj_tag(v_c_2008_) == 1 {
                    v_pre_2015_ = leanh::lean_ctor_get(v_c_2008_, 0);
                    v_str_2016_ = leanh::lean_ctor_get(v_c_2008_, 1);
                    v_env_2017_ = leanh::lean_ctor_get(v___x_2014_, 0);
                    leanh::lean_inc_ref_n(v_env_2017_, 2);
                    leanh::lean_dec(v___x_2014_);
                    leanh::lean_inc(v_pre_2015_);
                    v___x_2018_ = l_Lean_getStructureInfo_x3f(v_env_2017_, v_pre_2015_);
                    if leanh::lean_obj_tag(v___x_2018_) == 1 {
                        v_val_2019_ = leanh::lean_ctor_get(v___x_2018_, 0);
                        v_isSharedCheck_2088_ =
                            (!leanh::lean_is_exclusive(v___x_2018_)) as u8;
                        if v_isSharedCheck_2088_ == 0 {
                            v___x_2021_ = v___x_2018_;
                            v_isShared_2022_ = v_isSharedCheck_2088_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2019_);
                            leanh::lean_dec(v___x_2018_);
                            v___x_2021_ = leanh::lean_box(0);
                            v_isShared_2022_ = v_isSharedCheck_2088_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2018_);
                        leanh::lean_dec_ref(v_env_2017_);
                        leanh::lean_dec_ref_known(v_c_2008_, 2);
                        v___x_2089_ = leanh::lean_box(0);
                        v___x_2090_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2090_, 0, v___x_2089_);
                        return v___x_2090_;
                    }
                } else {
                    leanh::lean_dec(v___x_2014_);
                    leanh::lean_dec(v_c_2008_);
                    v___x_2091_ = leanh::lean_box(0);
                    v___x_2092_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2092_, 0, v___x_2091_);
                    return v___x_2092_;
                }
            }
            1 => {
                leanh::lean_inc_n(v_pre_2015_, 2);
                leanh::lean_inc_ref(v_env_2017_);
                v___x_2023_ = lean_is_class(v_env_2017_, v_pre_2015_);
                v___x_2024_ = l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0(v_pre_2015_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
                if leanh::lean_obj_tag(v___x_2024_) == 0 {
                    v_a_2025_ = leanh::lean_ctor_get(v___x_2024_, 0);
                    v_isSharedCheck_2079_ = (!leanh::lean_is_exclusive(v___x_2024_)) as u8;
                    if v_isSharedCheck_2079_ == 0 {
                        v___x_2027_ = v___x_2024_;
                        v_isShared_2028_ = v_isSharedCheck_2079_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2025_);
                        leanh::lean_dec(v___x_2024_);
                        v___x_2027_ = leanh::lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2079_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2021_);
                    leanh::lean_dec(v_val_2019_);
                    leanh::lean_dec_ref(v_env_2017_);
                    leanh::lean_dec_ref_known(v_c_2008_, 2);
                    v_a_2080_ = leanh::lean_ctor_get(v___x_2024_, 0);
                    v_isSharedCheck_2087_ = (!leanh::lean_is_exclusive(v___x_2024_)) as u8;
                    if v_isSharedCheck_2087_ == 0 {
                        v___x_2082_ = v___x_2024_;
                        v_isShared_2083_ = v_isSharedCheck_2087_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2080_);
                        leanh::lean_dec(v___x_2024_);
                        v___x_2082_ = leanh::lean_box(0);
                        v_isShared_2083_ = v_isSharedCheck_2087_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2034_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_str_2016_);
                v___x_2035_ = l_Lean_Name_str___override(v___x_2034_, v_str_2016_);
                leanh::lean_inc(v___x_2035_);
                leanh::lean_inc(v_pre_2015_);
                v___x_2036_ = l_Lean_getFieldInfo_x3f(v_env_2017_, v_pre_2015_, v___x_2035_);
                if leanh::lean_obj_tag(v___x_2036_) == 1 {
                    leanh::lean_del_object(v___x_2027_);
                    leanh::lean_del_object(v___x_2021_);
                    leanh::lean_dec(v_val_2019_);
                    leanh::lean_dec_ref_known(v_c_2008_, 2);
                    v_val_2037_ = leanh::lean_ctor_get(v___x_2036_, 0);
                    v_isSharedCheck_2058_ = (!leanh::lean_is_exclusive(v___x_2036_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v___x_2039_ = v___x_2036_;
                        v_isShared_2040_ = v_isSharedCheck_2058_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2037_);
                        leanh::lean_dec(v___x_2036_);
                        v___x_2039_ = leanh::lean_box(0);
                        v_isShared_2040_ = v_isSharedCheck_2058_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2036_);
                    v_parentInfo_2059_ = leanh::lean_ctor_get(v_val_2019_, 3);
                    leanh::lean_inc_ref(v_parentInfo_2059_);
                    leanh::lean_dec(v_val_2019_);
                    v___x_2060_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2061_ = lean_array_get_size(v_parentInfo_2059_);
                    v___x_2062_ = lean_nat_dec_lt(v___x_2060_, v___x_2061_);
                    if v___x_2062_ == 0 {
                        leanh::lean_dec_ref(v_parentInfo_2059_);
                        leanh::lean_dec(v___x_2035_);
                        leanh::lean_dec(v_a_2025_);
                        leanh::lean_del_object(v___x_2021_);
                        leanh::lean_dec_ref_known(v_c_2008_, 2);
                        state = 3;
                        continue;
                    } else {
                        if v___x_2062_ == 0 {
                            leanh::lean_dec_ref(v_parentInfo_2059_);
                            leanh::lean_dec(v___x_2035_);
                            leanh::lean_dec(v_a_2025_);
                            leanh::lean_del_object(v___x_2021_);
                            leanh::lean_dec_ref_known(v_c_2008_, 2);
                            state = 3;
                            continue;
                        } else {
                            v___x_2063_ = 0usize;
                            v___x_2064_ = lean_usize_of_nat(v___x_2061_);
                            v___x_2065_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__1(v_c_2008_, v_parentInfo_2059_, v___x_2063_, v___x_2064_);
                            leanh::lean_dec_ref(v_parentInfo_2059_);
                            leanh::lean_dec_ref_known(v_c_2008_, 2);
                            if v___x_2065_ == 0 {
                                leanh::lean_dec(v___x_2035_);
                                leanh::lean_dec(v_a_2025_);
                                leanh::lean_del_object(v___x_2021_);
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_2027_);
                                v_numParams_2066_ = leanh::lean_ctor_get(v_a_2025_, 1);
                                leanh::lean_inc(v_numParams_2066_);
                                leanh::lean_dec(v_a_2025_);
                                v___x_2067_ = 0;
                                v___x_2068_ = leanh::lean_box((v___x_2065_) as usize);
                                v___x_2069_ = leanh::lean_box((v___x_2023_) as usize);
                                v___x_2070_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2070_, 0, v___x_2068_);
                                leanh::lean_ctor_set(v___x_2070_, 1, v___x_2069_);
                                v___x_2071_ = leanh::lean_box((v___x_2067_) as usize);
                                v___x_2072_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2072_, 0, v___x_2071_);
                                leanh::lean_ctor_set(v___x_2072_, 1, v___x_2070_);
                                v___x_2073_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2073_, 0, v_numParams_2066_);
                                leanh::lean_ctor_set(v___x_2073_, 1, v___x_2072_);
                                v___x_2074_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2074_, 0, v___x_2035_);
                                leanh::lean_ctor_set(v___x_2074_, 1, v___x_2073_);
                                if v_isShared_2022_ == 0 {
                                    leanh::lean_ctor_set(v___x_2021_, 0, v___x_2074_);
                                    v___x_2076_ = v___x_2021_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2078_ =
                                        leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2078_,
                                        0,
                                        v___x_2074_,
                                    );
                                    v___x_2076_ = v_reuseFailAlloc_2078_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_2030_ = leanh::lean_box(0);
                if v_isShared_2028_ == 0 {
                    leanh::lean_ctor_set(v___x_2027_, 0, v___x_2030_);
                    v___x_2032_ = v___x_2027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2033_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
                    v___x_2032_ = v_reuseFailAlloc_2033_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2032_;
            }
            5 => {
                v_numParams_2041_ = leanh::lean_ctor_get(v_a_2025_, 1);
                leanh::lean_inc(v_numParams_2041_);
                leanh::lean_dec(v_a_2025_);
                v_subobject_x3f_2042_ = leanh::lean_ctor_get(v_val_2037_, 2);
                leanh::lean_inc(v_subobject_x3f_2042_);
                leanh::lean_dec(v_val_2037_);
                v___x_2043_ = 1;
                if leanh::lean_obj_tag(v_subobject_x3f_2042_) == 0 {
                    v___x_2057_ = 0;
                    v___y_2045_ = v___x_2057_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_subobject_x3f_2042_, 1);
                    v___y_2045_ = v___x_2043_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2046_ = leanh::lean_box((v___y_2045_) as usize);
                v___x_2047_ = leanh::lean_box((v___x_2023_) as usize);
                v___x_2048_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2048_, 0, v___x_2046_);
                leanh::lean_ctor_set(v___x_2048_, 1, v___x_2047_);
                v___x_2049_ = leanh::lean_box((v___x_2043_) as usize);
                v___x_2050_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2050_, 0, v___x_2049_);
                leanh::lean_ctor_set(v___x_2050_, 1, v___x_2048_);
                v___x_2051_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2051_, 0, v_numParams_2041_);
                leanh::lean_ctor_set(v___x_2051_, 1, v___x_2050_);
                v___x_2052_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2052_, 0, v___x_2035_);
                leanh::lean_ctor_set(v___x_2052_, 1, v___x_2051_);
                if v_isShared_2040_ == 0 {
                    leanh::lean_ctor_set(v___x_2039_, 0, v___x_2052_);
                    v___x_2054_ = v___x_2039_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2056_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2052_);
                    v___x_2054_ = v_reuseFailAlloc_2056_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2055_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2055_, 0, v___x_2054_);
                return v___x_2055_;
            }
            8 => {
                v___x_2077_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2077_, 0, v___x_2076_);
                return v___x_2077_;
            }
            9 => {
                if v_isShared_2083_ == 0 {
                    v___x_2085_ = v___x_2082_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2086_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
                    v___x_2085_ = v_reuseFailAlloc_2086_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo___boxed(
    mut v_c_2093_: *mut leanh::LeanObject,
    mut v_a_2094_: *mut leanh::LeanObject,
    mut v_a_2095_: *mut leanh::LeanObject,
    mut v_a_2096_: *mut leanh::LeanObject,
    mut v_a_2097_: *mut leanh::LeanObject,
    mut v_a_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2099_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo(v_c_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
    leanh::lean_dec(v_a_2097_);
    leanh::lean_dec_ref(v_a_2096_);
    leanh::lean_dec(v_a_2095_);
    leanh::lean_dec_ref(v_a_2094_);
    return v_res_2099_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0(
    mut v_00_u03b1_2100_: *mut leanh::LeanObject,
    mut v_msg_2101_: *mut leanh::LeanObject,
    mut v___y_2102_: *mut leanh::LeanObject,
    mut v___y_2103_: *mut leanh::LeanObject,
    mut v___y_2104_: *mut leanh::LeanObject,
    mut v___y_2105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2107_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v_msg_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
    return v___x_2107_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___boxed(
    mut v_00_u03b1_2108_: *mut leanh::LeanObject,
    mut v_msg_2109_: *mut leanh::LeanObject,
    mut v___y_2110_: *mut leanh::LeanObject,
    mut v___y_2111_: *mut leanh::LeanObject,
    mut v___y_2112_: *mut leanh::LeanObject,
    mut v___y_2113_: *mut leanh::LeanObject,
    mut v___y_2114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2115_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0(v_00_u03b1_2108_, v_msg_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
    leanh::lean_dec(v___y_2113_);
    leanh::lean_dec_ref(v___y_2112_);
    leanh::lean_dec(v___y_2111_);
    leanh::lean_dec_ref(v___y_2110_);
    return v_res_2115_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0_spec__1(
    mut v_opts_2116_: *mut leanh::LeanObject,
    mut v_opt_2117_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2118_ = leanh::lean_ctor_get(v_opt_2117_, 0);
    v_defValue_2119_ = leanh::lean_ctor_get(v_opt_2117_, 1);
    v_map_2120_ = leanh::lean_ctor_get(v_opts_2116_, 0);
    v___x_2121_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2120_,
            v_name_2118_,
        );
    if leanh::lean_obj_tag(v___x_2121_) == 0 {
        let mut v___x_2122_: u8 = 0;
        v___x_2122_ = (leanh::lean_unbox(v_defValue_2119_) as u8);
        return v___x_2122_;
    } else {
        let mut v_val_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2123_ = leanh::lean_ctor_get(v___x_2121_, 0);
        leanh::lean_inc(v_val_2123_);
        leanh::lean_dec_ref_known(v___x_2121_, 1);
        if leanh::lean_obj_tag(v_val_2123_) == 1 {
            let mut v_v_2124_: u8 = 0;
            v_v_2124_ = leanh::lean_ctor_get_uint8(v_val_2123_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2123_, 0);
            return v_v_2124_;
        } else {
            let mut v___x_2125_: u8 = 0;
            leanh::lean_dec(v_val_2123_);
            v___x_2125_ = (leanh::lean_unbox(v_defValue_2119_) as u8);
            return v___x_2125_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0_spec__1___boxed(
    mut v_opts_2126_: *mut leanh::LeanObject,
    mut v_opt_2127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2128_: u8 = 0;
    let mut v_r_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2128_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0_spec__1(v_opts_2126_, v_opt_2127_);
    leanh::lean_dec_ref(v_opt_2127_);
    leanh::lean_dec_ref(v_opts_2126_);
    v_r_2129_ = leanh::lean_box((v_res_2128_) as usize);
    return v_r_2129_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0___redArg(
    mut v_opt_2130_: *mut leanh::LeanObject,
    mut v___y_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: u8 = 0;
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_options_2133_ = leanh::lean_ctor_get(v___y_2131_, 2);
    v___x_2134_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0_spec__1(v_options_2133_, v_opt_2130_);
    v___x_2135_ = leanh::lean_box((v___x_2134_) as usize);
    v___x_2136_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2136_, 0, v___x_2135_);
    return v___x_2136_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0___redArg___boxed(
    mut v_opt_2137_: *mut leanh::LeanObject,
    mut v___y_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0___redArg(v_opt_2137_, v___y_2138_);
    leanh::lean_dec_ref(v___y_2138_);
    leanh::lean_dec_ref(v_opt_2137_);
    return v_res_2140_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0(
    mut v___y_2149_: u8,
    mut v_suppressElabErrors_2150_: u8,
    mut v_x_2151_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2151_) == 1 {
        let mut v_pre_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_2152_ = leanh::lean_ctor_get(v_x_2151_, 0);
        match leanh::lean_obj_tag(v_pre_2152_) {
            1 => {
                let mut v_pre_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_2153_ = leanh::lean_ctor_get(v_pre_2152_, 0);
                match leanh::lean_obj_tag(v_pre_2153_) {
                    0 => {
                        let mut v_str_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2157_: u8 = 0;
                        v_str_2154_ = leanh::lean_ctor_get(v_x_2151_, 1);
                        v_str_2155_ = leanh::lean_ctor_get(v_pre_2152_, 1);
                        v___x_2156_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__0;
                        v___x_2157_ = lean_string_dec_eq(v_str_2155_, v___x_2156_);
                        if v___x_2157_ == 0 {
                            let mut v___x_2158_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2159_: u8 = 0;
                            v___x_2158_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__1;
                            v___x_2159_ = lean_string_dec_eq(v_str_2155_, v___x_2158_);
                            if v___x_2159_ == 0 {
                                return v___y_2149_;
                            } else {
                                let mut v___x_2160_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2161_: u8 = 0;
                                v___x_2160_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__2;
                                v___x_2161_ = lean_string_dec_eq(v_str_2154_, v___x_2160_);
                                if v___x_2161_ == 0 {
                                    return v___y_2149_;
                                } else {
                                    return v_suppressElabErrors_2150_;
                                }
                            }
                        } else {
                            let mut v___x_2162_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2163_: u8 = 0;
                            v___x_2162_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__3;
                            v___x_2163_ = lean_string_dec_eq(v_str_2154_, v___x_2162_);
                            if v___x_2163_ == 0 {
                                return v___y_2149_;
                            } else {
                                return v_suppressElabErrors_2150_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_2164_ = leanh::lean_ctor_get(v_pre_2153_, 0);
                        if leanh::lean_obj_tag(v_pre_2164_) == 0 {
                            let mut v_str_2165_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2166_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2167_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2168_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2169_: u8 = 0;
                            v_str_2165_ = leanh::lean_ctor_get(v_x_2151_, 1);
                            v_str_2166_ = leanh::lean_ctor_get(v_pre_2152_, 1);
                            v_str_2167_ = leanh::lean_ctor_get(v_pre_2153_, 1);
                            v___x_2168_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__4;
                            v___x_2169_ = lean_string_dec_eq(v_str_2167_, v___x_2168_);
                            if v___x_2169_ == 0 {
                                return v___y_2149_;
                            } else {
                                let mut v___x_2170_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2171_: u8 = 0;
                                v___x_2170_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__5;
                                v___x_2171_ = lean_string_dec_eq(v_str_2166_, v___x_2170_);
                                if v___x_2171_ == 0 {
                                    return v___y_2149_;
                                } else {
                                    let mut v___x_2172_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2173_: u8 = 0;
                                    v___x_2172_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__6;
                                    v___x_2173_ = lean_string_dec_eq(v_str_2165_, v___x_2172_);
                                    if v___x_2173_ == 0 {
                                        return v___y_2149_;
                                    } else {
                                        return v_suppressElabErrors_2150_;
                                    }
                                }
                            }
                        } else {
                            return v___y_2149_;
                        }
                    }
                    _ => {
                        return v___y_2149_;
                    }
                }
            }
            0 => {
                let mut v_str_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2176_: u8 = 0;
                v_str_2174_ = leanh::lean_ctor_get(v_x_2151_, 1);
                v___x_2175_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___closed__7;
                v___x_2176_ = lean_string_dec_eq(v_str_2174_, v___x_2175_);
                if v___x_2176_ == 0 {
                    return v___y_2149_;
                } else {
                    return v_suppressElabErrors_2150_;
                }
            }
            _ => {
                return v___y_2149_;
            }
        }
    } else {
        return v___y_2149_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___boxed(
    mut v___y_2177_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_2178_: *mut leanh::LeanObject,
    mut v_x_2179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4350__boxed_2180_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2181_: u8 = 0;
    let mut v_res_2182_: u8 = 0;
    let mut v_r_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_4350__boxed_2180_ = (leanh::lean_unbox(v___y_2177_) as u8);
    v_suppressElabErrors_boxed_2181_ = (leanh::lean_unbox(v_suppressElabErrors_2178_) as u8);
    v_res_2182_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0(v___y_4350__boxed_2180_, v_suppressElabErrors_boxed_2181_, v_x_2179_);
    leanh::lean_dec(v_x_2179_);
    v_r_2183_ = leanh::lean_box((v_res_2182_) as usize);
    return v_r_2183_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5(
    mut v_ref_2185_: *mut leanh::LeanObject,
    mut v_msgData_2186_: *mut leanh::LeanObject,
    mut v_severity_2187_: u8,
    mut v_isSilent_2188_: u8,
    mut v___y_2189_: *mut leanh::LeanObject,
    mut v___y_2190_: *mut leanh::LeanObject,
    mut v___y_2191_: *mut leanh::LeanObject,
    mut v___y_2192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2195_: u8 = 0;
    let mut v___y_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2201_: u8 = 0;
    let mut v___y_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2229_: u8 = 0;
    let mut v___y_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2232_: u8 = 0;
    let mut v___y_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2234_: u8 = 0;
    let mut v___y_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2237_: u8 = 0;
    let mut v___y_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2244_: u8 = 0;
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2254_: u8 = 0;
    let mut v___y_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2257_: u8 = 0;
    let mut v___y_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2259_: u8 = 0;
    let mut v___y_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2262_: u8 = 0;
    let mut v___y_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2268_: u8 = 0;
    let mut v___y_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2270_: u8 = 0;
    let mut v___y_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2273_: u8 = 0;
    let mut v_ref_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: u8 = 0;
    let mut v___y_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2281_: u8 = 0;
    let mut v___y_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: u8 = 0;
    let mut v___y_2286_: u8 = 0;
    let mut v___y_2288_: u8 = 0;
    let mut v_fileName_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2293_: u8 = 0;
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: u8 = 0;
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: u8 = 0;
    let mut v___x_2304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2278_ = 2;
                v___x_2303_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2187_, v___x_2278_);
                if v___x_2303_ == 0 {
                    v___y_2288_ = v___x_2303_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_2186_);
                    v___x_2304_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2186_);
                    v___y_2288_ = v___x_2304_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2204_ = lean_st_ref_take(v___y_2203_);
                v_currNamespace_2205_ = leanh::lean_ctor_get(v___y_2202_, 6);
                v_openDecls_2206_ = leanh::lean_ctor_get(v___y_2202_, 7);
                v_env_2207_ = leanh::lean_ctor_get(v___x_2204_, 0);
                v_nextMacroScope_2208_ = leanh::lean_ctor_get(v___x_2204_, 1);
                v_ngen_2209_ = leanh::lean_ctor_get(v___x_2204_, 2);
                v_auxDeclNGen_2210_ = leanh::lean_ctor_get(v___x_2204_, 3);
                v_traceState_2211_ = leanh::lean_ctor_get(v___x_2204_, 4);
                v_cache_2212_ = leanh::lean_ctor_get(v___x_2204_, 5);
                v_messages_2213_ = leanh::lean_ctor_get(v___x_2204_, 6);
                v_infoState_2214_ = leanh::lean_ctor_get(v___x_2204_, 7);
                v_snapshotTasks_2215_ = leanh::lean_ctor_get(v___x_2204_, 8);
                v_isSharedCheck_2229_ = (!leanh::lean_is_exclusive(v___x_2204_)) as u8;
                if v_isSharedCheck_2229_ == 0 {
                    v___x_2217_ = v___x_2204_;
                    v_isShared_2218_ = v_isSharedCheck_2229_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2215_);
                    leanh::lean_inc(v_infoState_2214_);
                    leanh::lean_inc(v_messages_2213_);
                    leanh::lean_inc(v_cache_2212_);
                    leanh::lean_inc(v_traceState_2211_);
                    leanh::lean_inc(v_auxDeclNGen_2210_);
                    leanh::lean_inc(v_ngen_2209_);
                    leanh::lean_inc(v_nextMacroScope_2208_);
                    leanh::lean_inc(v_env_2207_);
                    leanh::lean_dec(v___x_2204_);
                    v___x_2217_ = leanh::lean_box(0);
                    v_isShared_2218_ = v_isSharedCheck_2229_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_2206_);
                leanh::lean_inc(v_currNamespace_2205_);
                v___x_2219_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2219_, 0, v_currNamespace_2205_);
                leanh::lean_ctor_set(v___x_2219_, 1, v_openDecls_2206_);
                v___x_2220_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2220_, 0, v___x_2219_);
                leanh::lean_ctor_set(v___x_2220_, 1, v___y_2200_);
                leanh::lean_inc_ref(v___y_2197_);
                leanh::lean_inc_ref(v___y_2199_);
                v___x_2221_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_2221_, 0, v___y_2199_);
                leanh::lean_ctor_set(v___x_2221_, 1, v___y_2198_);
                leanh::lean_ctor_set(v___x_2221_, 2, v___y_2196_);
                leanh::lean_ctor_set(v___x_2221_, 3, v___y_2197_);
                leanh::lean_ctor_set(v___x_2221_, 4, v___x_2220_);
                leanh::lean_ctor_set_uint8(
                    v___x_2221_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_2195_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2221_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2201_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2221_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2188_,
                );
                v___x_2222_ = l_Lean_MessageLog_add(v___x_2221_, v_messages_2213_);
                if v_isShared_2218_ == 0 {
                    leanh::lean_ctor_set(v___x_2217_, 6, v___x_2222_);
                    v___x_2224_ = v___x_2217_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2228_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_env_2207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_nextMacroScope_2208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_ngen_2209_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_auxDeclNGen_2210_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 4, v_traceState_2211_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 5, v_cache_2212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 6, v___x_2222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 7, v_infoState_2214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 8, v_snapshotTasks_2215_);
                    v___x_2224_ = v_reuseFailAlloc_2228_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2225_ = lean_st_ref_set(v___y_2203_, v___x_2224_);
                v___x_2226_ = leanh::lean_box(0);
                v___x_2227_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2227_, 0, v___x_2226_);
                return v___x_2227_;
            }
            4 => {
                v___x_2239_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2186_,
                    );
                v___x_2240_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0_spec__1(v___x_2239_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
                v_a_2241_ = leanh::lean_ctor_get(v___x_2240_, 0);
                v_isSharedCheck_2254_ = (!leanh::lean_is_exclusive(v___x_2240_)) as u8;
                if v_isSharedCheck_2254_ == 0 {
                    v___x_2243_ = v___x_2240_;
                    v_isShared_2244_ = v_isSharedCheck_2254_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2241_);
                    leanh::lean_dec(v___x_2240_);
                    v___x_2243_ = leanh::lean_box(0);
                    v_isShared_2244_ = v_isSharedCheck_2254_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_2233_, 2);
                v___x_2245_ = l_Lean_FileMap_toPosition(v___y_2233_, v___y_2236_);
                leanh::lean_dec(v___y_2236_);
                v___x_2246_ = l_Lean_FileMap_toPosition(v___y_2233_, v___y_2238_);
                leanh::lean_dec(v___y_2238_);
                v___x_2247_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2247_, 0, v___x_2246_);
                v___x_2248_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___closed__0;
                if v___y_2234_ == 0 {
                    leanh::lean_del_object(v___x_2243_);
                    leanh::lean_dec_ref(v___y_2231_);
                    v___y_2195_ = v___y_2232_;
                    v___y_2196_ = v___x_2247_;
                    v___y_2197_ = v___x_2248_;
                    v___y_2198_ = v___x_2245_;
                    v___y_2199_ = v___y_2235_;
                    v___y_2200_ = v_a_2241_;
                    v___y_2201_ = v___y_2237_;
                    v___y_2202_ = v___y_2191_;
                    v___y_2203_ = v___y_2192_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2241_);
                    v___x_2249_ = l_Lean_MessageData_hasTag(v___y_2231_, v_a_2241_);
                    if v___x_2249_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2247_, 1);
                        leanh::lean_dec_ref(v___x_2245_);
                        leanh::lean_dec(v_a_2241_);
                        v___x_2250_ = leanh::lean_box(0);
                        if v_isShared_2244_ == 0 {
                            leanh::lean_ctor_set(v___x_2243_, 0, v___x_2250_);
                            v___x_2252_ = v___x_2243_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2253_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
                            v___x_2252_ = v_reuseFailAlloc_2253_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2243_);
                        v___y_2195_ = v___y_2232_;
                        v___y_2196_ = v___x_2247_;
                        v___y_2197_ = v___x_2248_;
                        v___y_2198_ = v___x_2245_;
                        v___y_2199_ = v___y_2235_;
                        v___y_2200_ = v_a_2241_;
                        v___y_2201_ = v___y_2237_;
                        v___y_2202_ = v___y_2191_;
                        v___y_2203_ = v___y_2192_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2252_;
            }
            7 => {
                v___x_2264_ = l_Lean_Syntax_getTailPos_x3f(v___y_2261_, v___y_2257_);
                leanh::lean_dec(v___y_2261_);
                if leanh::lean_obj_tag(v___x_2264_) == 0 {
                    leanh::lean_inc(v___y_2263_);
                    v___y_2231_ = v___y_2256_;
                    v___y_2232_ = v___y_2257_;
                    v___y_2233_ = v___y_2258_;
                    v___y_2234_ = v___y_2259_;
                    v___y_2235_ = v___y_2260_;
                    v___y_2236_ = v___y_2263_;
                    v___y_2237_ = v___y_2262_;
                    v___y_2238_ = v___y_2263_;
                    state = 4;
                    continue;
                } else {
                    v_val_2265_ = leanh::lean_ctor_get(v___x_2264_, 0);
                    leanh::lean_inc(v_val_2265_);
                    leanh::lean_dec_ref_known(v___x_2264_, 1);
                    v___y_2231_ = v___y_2256_;
                    v___y_2232_ = v___y_2257_;
                    v___y_2233_ = v___y_2258_;
                    v___y_2234_ = v___y_2259_;
                    v___y_2235_ = v___y_2260_;
                    v___y_2236_ = v___y_2263_;
                    v___y_2237_ = v___y_2262_;
                    v___y_2238_ = v_val_2265_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2274_ = l_Lean_replaceRef(v_ref_2185_, v___y_2271_);
                v___x_2275_ = l_Lean_Syntax_getPos_x3f(v_ref_2274_, v___y_2268_);
                if leanh::lean_obj_tag(v___x_2275_) == 0 {
                    v___x_2276_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2256_ = v___y_2267_;
                    v___y_2257_ = v___y_2268_;
                    v___y_2258_ = v___y_2269_;
                    v___y_2259_ = v___y_2270_;
                    v___y_2260_ = v___y_2272_;
                    v___y_2261_ = v_ref_2274_;
                    v___y_2262_ = v___y_2273_;
                    v___y_2263_ = v___x_2276_;
                    state = 7;
                    continue;
                } else {
                    v_val_2277_ = leanh::lean_ctor_get(v___x_2275_, 0);
                    leanh::lean_inc(v_val_2277_);
                    leanh::lean_dec_ref_known(v___x_2275_, 1);
                    v___y_2256_ = v___y_2267_;
                    v___y_2257_ = v___y_2268_;
                    v___y_2258_ = v___y_2269_;
                    v___y_2259_ = v___y_2270_;
                    v___y_2260_ = v___y_2272_;
                    v___y_2261_ = v_ref_2274_;
                    v___y_2262_ = v___y_2273_;
                    v___y_2263_ = v_val_2277_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2286_ == 0 {
                    v___y_2267_ = v___y_2284_;
                    v___y_2268_ = v___y_2285_;
                    v___y_2269_ = v___y_2280_;
                    v___y_2270_ = v___y_2281_;
                    v___y_2271_ = v___y_2282_;
                    v___y_2272_ = v___y_2283_;
                    v___y_2273_ = v_severity_2187_;
                    state = 8;
                    continue;
                } else {
                    v___y_2267_ = v___y_2284_;
                    v___y_2268_ = v___y_2285_;
                    v___y_2269_ = v___y_2280_;
                    v___y_2270_ = v___y_2281_;
                    v___y_2271_ = v___y_2282_;
                    v___y_2272_ = v___y_2283_;
                    v___y_2273_ = v___x_2278_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2288_ == 0 {
                    v_fileName_2289_ = leanh::lean_ctor_get(v___y_2191_, 0);
                    v_fileMap_2290_ = leanh::lean_ctor_get(v___y_2191_, 1);
                    v_options_2291_ = leanh::lean_ctor_get(v___y_2191_, 2);
                    v_ref_2292_ = leanh::lean_ctor_get(v___y_2191_, 5);
                    v_suppressElabErrors_2293_ = leanh::lean_ctor_get_uint8(
                        v___y_2191_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2294_ = leanh::lean_box((v___y_2288_) as usize);
                    v___x_2295_ = leanh::lean_box((v_suppressElabErrors_2293_) as usize);
                    v___f_2296_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_2296_, 0, v___x_2294_);
                    leanh::lean_closure_set(v___f_2296_, 1, v___x_2295_);
                    v___x_2297_ = 1;
                    v___x_2298_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2187_, v___x_2297_);
                    if v___x_2298_ == 0 {
                        v___y_2280_ = v_fileMap_2290_;
                        v___y_2281_ = v_suppressElabErrors_2293_;
                        v___y_2282_ = v_ref_2292_;
                        v___y_2283_ = v_fileName_2289_;
                        v___y_2284_ = v___f_2296_;
                        v___y_2285_ = v___y_2288_;
                        v___y_2286_ = v___x_2298_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2299_ = l_Lean_warningAsError;
                        v___x_2300_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0_spec__1(v_options_2291_, v___x_2299_);
                        v___y_2280_ = v_fileMap_2290_;
                        v___y_2281_ = v_suppressElabErrors_2293_;
                        v___y_2282_ = v_ref_2292_;
                        v___y_2283_ = v_fileName_2289_;
                        v___y_2284_ = v___f_2296_;
                        v___y_2285_ = v___y_2288_;
                        v___y_2286_ = v___x_2300_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_2186_);
                    v___x_2301_ = leanh::lean_box(0);
                    v___x_2302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2302_, 0, v___x_2301_);
                    return v___x_2302_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(
    mut v_ref_2305_: *mut leanh::LeanObject,
    mut v_msgData_2306_: *mut leanh::LeanObject,
    mut v_severity_2307_: *mut leanh::LeanObject,
    mut v_isSilent_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
    mut v___y_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
    mut v___y_2312_: *mut leanh::LeanObject,
    mut v___y_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2314_: u8 = 0;
    let mut v_isSilent_boxed_2315_: u8 = 0;
    let mut v_res_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2314_ = (leanh::lean_unbox(v_severity_2307_) as u8);
    v_isSilent_boxed_2315_ = (leanh::lean_unbox(v_isSilent_2308_) as u8);
    v_res_2316_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5(v_ref_2305_, v_msgData_2306_, v_severity_boxed_2314_, v_isSilent_boxed_2315_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
    leanh::lean_dec(v___y_2312_);
    leanh::lean_dec_ref(v___y_2311_);
    leanh::lean_dec(v___y_2310_);
    leanh::lean_dec_ref(v___y_2309_);
    leanh::lean_dec(v_ref_2305_);
    return v_res_2316_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4(
    mut v_msgData_2317_: *mut leanh::LeanObject,
    mut v_severity_2318_: u8,
    mut v_isSilent_2319_: u8,
    mut v___y_2320_: *mut leanh::LeanObject,
    mut v___y_2321_: *mut leanh::LeanObject,
    mut v___y_2322_: *mut leanh::LeanObject,
    mut v___y_2323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2325_ = leanh::lean_ctor_get(v___y_2322_, 5);
    v___x_2326_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4_spec__5(v_ref_2325_, v_msgData_2317_, v_severity_2318_, v_isSilent_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
    return v___x_2326_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4___boxed(
    mut v_msgData_2327_: *mut leanh::LeanObject,
    mut v_severity_2328_: *mut leanh::LeanObject,
    mut v_isSilent_2329_: *mut leanh::LeanObject,
    mut v___y_2330_: *mut leanh::LeanObject,
    mut v___y_2331_: *mut leanh::LeanObject,
    mut v___y_2332_: *mut leanh::LeanObject,
    mut v___y_2333_: *mut leanh::LeanObject,
    mut v___y_2334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2335_: u8 = 0;
    let mut v_isSilent_boxed_2336_: u8 = 0;
    let mut v_res_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2335_ = (leanh::lean_unbox(v_severity_2328_) as u8);
    v_isSilent_boxed_2336_ = (leanh::lean_unbox(v_isSilent_2329_) as u8);
    v_res_2337_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4(v_msgData_2327_, v_severity_boxed_2335_, v_isSilent_boxed_2336_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
    leanh::lean_dec(v___y_2333_);
    leanh::lean_dec_ref(v___y_2332_);
    leanh::lean_dec(v___y_2331_);
    leanh::lean_dec_ref(v___y_2330_);
    return v_res_2337_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3(
    mut v_msgData_2338_: *mut leanh::LeanObject,
    mut v___y_2339_: *mut leanh::LeanObject,
    mut v___y_2340_: *mut leanh::LeanObject,
    mut v___y_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2344_: u8 = 0;
    let mut v___x_2345_: u8 = 0;
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2344_ = 1;
    v___x_2345_ = 0;
    v___x_2346_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3_spec__4(v_msgData_2338_, v___x_2344_, v___x_2345_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
    return v___x_2346_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3___boxed(
    mut v_msgData_2347_: *mut leanh::LeanObject,
    mut v___y_2348_: *mut leanh::LeanObject,
    mut v___y_2349_: *mut leanh::LeanObject,
    mut v___y_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: *mut leanh::LeanObject,
    mut v___y_2352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2353_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3(v_msgData_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
    leanh::lean_dec(v___y_2351_);
    leanh::lean_dec_ref(v___y_2350_);
    leanh::lean_dec(v___y_2349_);
    leanh::lean_dec_ref(v___y_2348_);
    return v_res_2353_;
}
pub unsafe fn _init_l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__0;
    v___x_2356_ = l_Lean_stringToMessageData(v___x_2355_);
    return v___x_2356_;
}
pub unsafe fn _init_l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ = l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__2;
    v___x_2359_ = l_Lean_stringToMessageData(v___x_2358_);
    return v___x_2359_;
}
pub unsafe fn l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1(
    mut v_id_2360_: *mut leanh::LeanObject,
    mut v___y_2361_: *mut leanh::LeanObject,
    mut v___y_2362_: *mut leanh::LeanObject,
    mut v___y_2363_: *mut leanh::LeanObject,
    mut v___y_2364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2373_: u8 = 0;
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2379_: u8 = 0;
    let mut v___x_2380_: u8 = 0;
    let mut v___x_2381_: u8 = 0;
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: u8 = 0;
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2366_ = lean_st_ref_get(v___y_2364_);
                v_env_2367_ = leanh::lean_ctor_get(v___x_2366_, 0);
                leanh::lean_inc_ref(v_env_2367_);
                leanh::lean_dec(v___x_2366_);
                v___x_2368_ = l_Lean_ResolveName_backward_privateInPublic_warn;
                v___x_2369_ = l_Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0___redArg(v___x_2368_, v___y_2363_);
                v_a_2370_ = leanh::lean_ctor_get(v___x_2369_, 0);
                v_isSharedCheck_2389_ = (!leanh::lean_is_exclusive(v___x_2369_)) as u8;
                if v_isSharedCheck_2389_ == 0 {
                    v___x_2372_ = v___x_2369_;
                    v_isShared_2373_ = v_isSharedCheck_2389_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2370_);
                    leanh::lean_dec(v___x_2369_);
                    v___x_2372_ = leanh::lean_box(0);
                    v_isShared_2373_ = v_isSharedCheck_2389_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_isExporting_2379_ = leanh::lean_ctor_get_uint8(
                    v_env_2367_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_2367_);
                if v_isExporting_2379_ == 0 {
                    leanh::lean_dec(v_a_2370_);
                    leanh::lean_dec(v_id_2360_);
                    state = 2;
                    continue;
                } else {
                    v___x_2380_ = l_Lean_isPrivateName(v_id_2360_);
                    if v___x_2380_ == 0 {
                        leanh::lean_dec(v_a_2370_);
                        leanh::lean_dec(v_id_2360_);
                        state = 2;
                        continue;
                    } else {
                        v___x_2381_ = (leanh::lean_unbox(v_a_2370_) as u8);
                        leanh::lean_dec(v_a_2370_);
                        if v___x_2381_ == 0 {
                            leanh::lean_dec(v_id_2360_);
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_2372_);
                            v___x_2382_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__1_once), _init_l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__1);
                            v___x_2383_ = 0;
                            v___x_2384_ = l_Lean_MessageData_ofConstName(v_id_2360_, v___x_2383_);
                            v___x_2385_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2385_, 0, v___x_2382_);
                            leanh::lean_ctor_set(v___x_2385_, 1, v___x_2384_);
                            v___x_2386_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__3_once), _init_l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___closed__3);
                            v___x_2387_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2387_, 0, v___x_2385_);
                            leanh::lean_ctor_set(v___x_2387_, 1, v___x_2386_);
                            v___x_2388_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1_spec__3(v___x_2387_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
                            return v___x_2388_;
                        }
                    }
                }
            }
            2 => {
                v___x_2375_ = leanh::lean_box(0);
                if v_isShared_2373_ == 0 {
                    leanh::lean_ctor_set(v___x_2372_, 0, v___x_2375_);
                    v___x_2377_ = v___x_2372_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2378_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
                    v___x_2377_ = v_reuseFailAlloc_2378_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1___boxed(
    mut v_id_2390_: *mut leanh::LeanObject,
    mut v___y_2391_: *mut leanh::LeanObject,
    mut v___y_2392_: *mut leanh::LeanObject,
    mut v___y_2393_: *mut leanh::LeanObject,
    mut v___y_2394_: *mut leanh::LeanObject,
    mut v___y_2395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2396_ = l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1(v_id_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
    leanh::lean_dec(v___y_2394_);
    leanh::lean_dec_ref(v___y_2393_);
    leanh::lean_dec(v___y_2392_);
    leanh::lean_dec_ref(v___y_2391_);
    return v_res_2396_;
}
pub unsafe fn l_Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0(
    mut v_n_2397_: *mut leanh::LeanObject,
    mut v___y_2398_: *mut leanh::LeanObject,
    mut v___y_2399_: *mut leanh::LeanObject,
    mut v___y_2400_: *mut leanh::LeanObject,
    mut v___y_2401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2403_: u8 = 0;
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2413_: u8 = 0;
    let mut v___y_2415_: u8 = 0;
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_2427_: u8 = 0;
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: u8 = 0;
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importAll_2441_: u8 = 0;
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2450_: u8 = 0;
    let mut v_unused_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut v_isExporting_2460_: u8 = 0;
    let mut v___x_2461_: u8 = 0;
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: u8 = 0;
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2403_ = l_Lean_isPrivateName(v_n_2397_);
                if v___x_2403_ == 0 {
                    leanh::lean_dec(v_n_2397_);
                    v___x_2404_ = leanh::lean_box((v___x_2403_) as usize);
                    v___x_2405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2405_, 0, v___x_2404_);
                    return v___x_2405_;
                } else {
                    v___x_2406_ = lean_st_ref_get(v___y_2401_);
                    v_env_2407_ = leanh::lean_ctor_get(v___x_2406_, 0);
                    leanh::lean_inc_ref(v_env_2407_);
                    leanh::lean_dec(v___x_2406_);
                    v___x_2408_ = l_Lean_ResolveName_backward_privateInPublic;
                    v___x_2409_ = l_Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0___redArg(v___x_2408_, v___y_2400_);
                    v_a_2410_ = leanh::lean_ctor_get(v___x_2409_, 0);
                    v_isSharedCheck_2467_ = (!leanh::lean_is_exclusive(v___x_2409_)) as u8;
                    if v_isSharedCheck_2467_ == 0 {
                        v___x_2412_ = v___x_2409_;
                        v_isShared_2413_ = v_isSharedCheck_2467_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2410_);
                        leanh::lean_dec(v___x_2409_);
                        v___x_2412_ = leanh::lean_box(0);
                        v_isShared_2413_ = v_isSharedCheck_2467_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_isExporting_2460_ = leanh::lean_ctor_get_uint8(
                    v_env_2407_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                if v_isExporting_2460_ == 0 {
                    leanh::lean_del_object(v___x_2412_);
                    leanh::lean_dec(v_a_2410_);
                    v___y_2415_ = v_isExporting_2460_;
                    state = 2;
                    continue;
                } else {
                    v___x_2461_ = (leanh::lean_unbox(v_a_2410_) as u8);
                    leanh::lean_dec(v_a_2410_);
                    if v___x_2461_ == 0 {
                        leanh::lean_dec_ref(v_env_2407_);
                        leanh::lean_dec(v_n_2397_);
                        v___x_2462_ = leanh::lean_box((v___x_2403_) as usize);
                        if v_isShared_2413_ == 0 {
                            leanh::lean_ctor_set(v___x_2412_, 0, v___x_2462_);
                            v___x_2464_ = v___x_2412_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_2465_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
                            v___x_2464_ = v_reuseFailAlloc_2465_;
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2412_);
                        v___x_2466_ = 0;
                        v___y_2415_ = v___x_2466_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_n_2397_);
                v___x_2416_ = l_Lean_checkPrivateInPublic___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__1(v_n_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
                if leanh::lean_obj_tag(v___x_2416_) == 0 {
                    v_isSharedCheck_2450_ = (!leanh::lean_is_exclusive(v___x_2416_)) as u8;
                    if v_isSharedCheck_2450_ == 0 {
                        v_unused_2451_ = leanh::lean_ctor_get(v___x_2416_, 0);
                        leanh::lean_dec(v_unused_2451_);
                        v___x_2418_ = v___x_2416_;
                        v_isShared_2419_ = v_isSharedCheck_2450_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2416_);
                        v___x_2418_ = leanh::lean_box(0);
                        v_isShared_2419_ = v_isSharedCheck_2450_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_2407_);
                    leanh::lean_dec(v_n_2397_);
                    v_a_2452_ = leanh::lean_ctor_get(v___x_2416_, 0);
                    v_isSharedCheck_2459_ = (!leanh::lean_is_exclusive(v___x_2416_)) as u8;
                    if v_isSharedCheck_2459_ == 0 {
                        v___x_2454_ = v___x_2416_;
                        v_isShared_2455_ = v_isSharedCheck_2459_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2452_);
                        leanh::lean_dec(v___x_2416_);
                        v___x_2454_ = leanh::lean_box(0);
                        v_isShared_2455_ = v_isSharedCheck_2459_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2420_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2407_, v_n_2397_);
                leanh::lean_dec(v_n_2397_);
                if leanh::lean_obj_tag(v___x_2420_) == 0 {
                    leanh::lean_dec_ref(v_env_2407_);
                    v___x_2421_ = leanh::lean_box((v___y_2415_) as usize);
                    if v_isShared_2419_ == 0 {
                        leanh::lean_ctor_set(v___x_2418_, 0, v___x_2421_);
                        v___x_2423_ = v___x_2418_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2424_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
                        v___x_2423_ = v_reuseFailAlloc_2424_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_val_2425_ = leanh::lean_ctor_get(v___x_2420_, 0);
                    leanh::lean_inc(v_val_2425_);
                    leanh::lean_dec_ref_known(v___x_2420_, 1);
                    v___x_2426_ = l_Lean_Environment_header(v_env_2407_);
                    leanh::lean_dec_ref(v_env_2407_);
                    v_isModule_2427_ = leanh::lean_ctor_get_uint8(
                        v___x_2426_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                    );
                    if v_isModule_2427_ == 0 {
                        leanh::lean_dec_ref(v___x_2426_);
                        leanh::lean_dec(v_val_2425_);
                        v___x_2428_ = leanh::lean_box((v___x_2403_) as usize);
                        if v_isShared_2419_ == 0 {
                            leanh::lean_ctor_set(v___x_2418_, 0, v___x_2428_);
                            v___x_2430_ = v___x_2418_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2431_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
                            v___x_2430_ = v_reuseFailAlloc_2431_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_modules_2432_ = leanh::lean_ctor_get(v___x_2426_, 3);
                        leanh::lean_inc_ref(v_modules_2432_);
                        leanh::lean_dec_ref(v___x_2426_);
                        v___x_2433_ = lean_array_get_size(v_modules_2432_);
                        v___x_2434_ = lean_nat_dec_lt(v_val_2425_, v___x_2433_);
                        if v___x_2434_ == 0 {
                            leanh::lean_dec_ref(v_modules_2432_);
                            leanh::lean_dec(v_val_2425_);
                            v___x_2435_ = leanh::lean_box((v_isModule_2427_) as usize);
                            if v_isShared_2419_ == 0 {
                                leanh::lean_ctor_set(v___x_2418_, 0, v___x_2435_);
                                v___x_2437_ = v___x_2418_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2438_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
                                v___x_2437_ = v_reuseFailAlloc_2438_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v___x_2439_ = lean_array_fget(v_modules_2432_, v_val_2425_);
                            leanh::lean_dec(v_val_2425_);
                            leanh::lean_dec_ref(v_modules_2432_);
                            v_toImport_2440_ = leanh::lean_ctor_get(v___x_2439_, 0);
                            leanh::lean_inc_ref(v_toImport_2440_);
                            leanh::lean_dec(v___x_2439_);
                            v_importAll_2441_ = leanh::lean_ctor_get_uint8(
                                v_toImport_2440_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            );
                            leanh::lean_dec_ref(v_toImport_2440_);
                            if v_importAll_2441_ == 0 {
                                v___x_2442_ = leanh::lean_box((v_isModule_2427_) as usize);
                                if v_isShared_2419_ == 0 {
                                    leanh::lean_ctor_set(v___x_2418_, 0, v___x_2442_);
                                    v___x_2444_ = v___x_2418_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2445_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2445_,
                                        0,
                                        v___x_2442_,
                                    );
                                    v___x_2444_ = v_reuseFailAlloc_2445_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v___x_2446_ = leanh::lean_box((v___y_2415_) as usize);
                                if v_isShared_2419_ == 0 {
                                    leanh::lean_ctor_set(v___x_2418_, 0, v___x_2446_);
                                    v___x_2448_ = v___x_2418_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2449_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2449_,
                                        0,
                                        v___x_2446_,
                                    );
                                    v___x_2448_ = v_reuseFailAlloc_2449_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            4 => {
                return v___x_2423_;
            }
            5 => {
                return v___x_2430_;
            }
            6 => {
                return v___x_2437_;
            }
            7 => {
                return v___x_2444_;
            }
            8 => {
                return v___x_2448_;
            }
            9 => {
                if v_isShared_2455_ == 0 {
                    v___x_2457_ = v___x_2454_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
                    v___x_2457_ = v_reuseFailAlloc_2458_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2457_;
            }
            11 => {
                return v___x_2464_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0___boxed(
    mut v_n_2468_: *mut leanh::LeanObject,
    mut v___y_2469_: *mut leanh::LeanObject,
    mut v___y_2470_: *mut leanh::LeanObject,
    mut v___y_2471_: *mut leanh::LeanObject,
    mut v___y_2472_: *mut leanh::LeanObject,
    mut v___y_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2474_ = l_Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0(v_n_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
    leanh::lean_dec(v___y_2472_);
    leanh::lean_dec_ref(v___y_2471_);
    leanh::lean_dec(v___y_2470_);
    leanh::lean_dec_ref(v___y_2469_);
    return v_res_2474_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName(
    mut v_e_2475_: *mut leanh::LeanObject,
    mut v_baseName_2476_: *mut leanh::LeanObject,
    mut v_a_2477_: *mut leanh::LeanObject,
    mut v_a_2478_: *mut leanh::LeanObject,
    mut v_a_2479_: *mut leanh::LeanObject,
    mut v_a_2480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2490_: u8 = 0;
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: u8 = 0;
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: u8 = 0;
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2507_: u8 = 0;
    let mut v___x_2508_: u8 = 0;
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2482_ = l_Lean_Expr_cleanupAnnotations(v_e_2475_);
                v___x_2483_ = l_Lean_Expr_getAppFn(v___x_2482_);
                leanh::lean_dec_ref(v___x_2482_);
                v___x_2484_ = l_Lean_Expr_constName_x3f(v___x_2483_);
                leanh::lean_dec_ref(v___x_2483_);
                if leanh::lean_obj_tag(v___x_2484_) == 1 {
                    v_val_2485_ = leanh::lean_ctor_get(v___x_2484_, 0);
                    leanh::lean_inc_n(v_val_2485_, 2);
                    leanh::lean_dec_ref_known(v___x_2484_, 1);
                    v___x_2486_ = l_Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0(v_val_2485_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_);
                    if leanh::lean_obj_tag(v___x_2486_) == 0 {
                        v_a_2487_ = leanh::lean_ctor_get(v___x_2486_, 0);
                        v_isSharedCheck_2507_ =
                            (!leanh::lean_is_exclusive(v___x_2486_)) as u8;
                        if v_isSharedCheck_2507_ == 0 {
                            v___x_2489_ = v___x_2486_;
                            v_isShared_2490_ = v_isSharedCheck_2507_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2487_);
                            leanh::lean_dec(v___x_2486_);
                            v___x_2489_ = leanh::lean_box(0);
                            v_isShared_2490_ = v_isSharedCheck_2507_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_2485_);
                        return v___x_2486_;
                    }
                } else {
                    leanh::lean_dec(v___x_2484_);
                    v___x_2508_ = 0;
                    v___x_2509_ = leanh::lean_box((v___x_2508_) as usize);
                    v___x_2510_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2510_, 0, v___x_2509_);
                    return v___x_2510_;
                }
            }
            1 => {
                v___x_2491_ = l_Lean_privateToUserName(v_val_2485_);
                v___x_2492_ = lean_name_eq(v___x_2491_, v_baseName_2476_);
                leanh::lean_dec(v___x_2491_);
                if v___x_2492_ == 0 {
                    leanh::lean_dec(v_a_2487_);
                    v___x_2493_ = leanh::lean_box((v___x_2492_) as usize);
                    if v_isShared_2490_ == 0 {
                        leanh::lean_ctor_set(v___x_2489_, 0, v___x_2493_);
                        v___x_2495_ = v___x_2489_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2496_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
                        v___x_2495_ = v_reuseFailAlloc_2496_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2497_ = (leanh::lean_unbox(v_a_2487_) as u8);
                    leanh::lean_dec(v_a_2487_);
                    if v___x_2497_ == 0 {
                        v___x_2498_ = leanh::lean_box((v___x_2492_) as usize);
                        if v_isShared_2490_ == 0 {
                            leanh::lean_ctor_set(v___x_2489_, 0, v___x_2498_);
                            v___x_2500_ = v___x_2489_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2501_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
                            v___x_2500_ = v_reuseFailAlloc_2501_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2502_ = 0;
                        v___x_2503_ = leanh::lean_box((v___x_2502_) as usize);
                        if v_isShared_2490_ == 0 {
                            leanh::lean_ctor_set(v___x_2489_, 0, v___x_2503_);
                            v___x_2505_ = v___x_2489_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2506_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
                            v___x_2505_ = v_reuseFailAlloc_2506_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2495_;
            }
            3 => {
                return v___x_2500_;
            }
            4 => {
                return v___x_2505_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName___boxed(
    mut v_e_2511_: *mut leanh::LeanObject,
    mut v_baseName_2512_: *mut leanh::LeanObject,
    mut v_a_2513_: *mut leanh::LeanObject,
    mut v_a_2514_: *mut leanh::LeanObject,
    mut v_a_2515_: *mut leanh::LeanObject,
    mut v_a_2516_: *mut leanh::LeanObject,
    mut v_a_2517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2518_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName(v_e_2511_, v_baseName_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
    leanh::lean_dec(v_a_2516_);
    leanh::lean_dec_ref(v_a_2515_);
    leanh::lean_dec(v_a_2514_);
    leanh::lean_dec_ref(v_a_2513_);
    leanh::lean_dec(v_baseName_2512_);
    return v_res_2518_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0(
    mut v_opt_2519_: *mut leanh::LeanObject,
    mut v___y_2520_: *mut leanh::LeanObject,
    mut v___y_2521_: *mut leanh::LeanObject,
    mut v___y_2522_: *mut leanh::LeanObject,
    mut v___y_2523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2525_ = l_Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0___redArg(v_opt_2519_, v___y_2522_);
    return v___x_2525_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0___boxed(
    mut v_opt_2526_: *mut leanh::LeanObject,
    mut v___y_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
    mut v___y_2529_: *mut leanh::LeanObject,
    mut v___y_2530_: *mut leanh::LeanObject,
    mut v___y_2531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2532_ = l_Lean_Option_getM___at___00Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0_spec__0(v_opt_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
    leanh::lean_dec(v___y_2530_);
    leanh::lean_dec_ref(v___y_2529_);
    leanh::lean_dec(v___y_2528_);
    leanh::lean_dec_ref(v___y_2527_);
    leanh::lean_dec_ref(v_opt_2526_);
    return v_res_2532_;
}
pub unsafe fn _init_l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName___closed__0()
-> u64 {
    let mut v___x_2533_: u8 = 0;
    let mut v___x_2534_: u64 = 0;
    v___x_2533_ = 3;
    v___x_2534_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2533_);
    return v___x_2534_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName(
    mut v_type_2535_: *mut leanh::LeanObject,
    mut v_baseName_2536_: *mut leanh::LeanObject,
    mut v_a_2537_: *mut leanh::LeanObject,
    mut v_a_2538_: *mut leanh::LeanObject,
    mut v_a_2539_: *mut leanh::LeanObject,
    mut v_a_2540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2543_: u8 = 0;
    let mut v_ctxApprox_2544_: u8 = 0;
    let mut v_quasiPatternApprox_2545_: u8 = 0;
    let mut v_constApprox_2546_: u8 = 0;
    let mut v_isDefEqStuckEx_2547_: u8 = 0;
    let mut v_unificationHints_2548_: u8 = 0;
    let mut v_proofIrrelevance_2549_: u8 = 0;
    let mut v_assignSyntheticOpaque_2550_: u8 = 0;
    let mut v_offsetCnstrs_2551_: u8 = 0;
    let mut v_etaStruct_2552_: u8 = 0;
    let mut v_univApprox_2553_: u8 = 0;
    let mut v_iota_2554_: u8 = 0;
    let mut v_beta_2555_: u8 = 0;
    let mut v_proj_2556_: u8 = 0;
    let mut v_zeta_2557_: u8 = 0;
    let mut v_zetaDelta_2558_: u8 = 0;
    let mut v_zetaUnused_2559_: u8 = 0;
    let mut v_zetaHave_2560_: u8 = 0;
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2563_: u8 = 0;
    let mut v_trackZetaDelta_2564_: u8 = 0;
    let mut v_zetaDeltaSet_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2571_: u8 = 0;
    let mut v_inTypeClassResolution_2572_: u8 = 0;
    let mut v_cacheInferType_2573_: u8 = 0;
    let mut v___x_2574_: u8 = 0;
    let mut v_config_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: u64 = 0;
    let mut v___x_2578_: u64 = 0;
    let mut v___x_2579_: u64 = 0;
    let mut v___x_2580_: u64 = 0;
    let mut v___x_2581_: u64 = 0;
    let mut v_key_2582_: u64 = 0;
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2589_: u8 = 0;
    let mut v___x_2590_: u8 = 0;
    let mut v___x_2591_: u8 = 0;
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2599_: u8 = 0;
    let mut v___x_2600_: u8 = 0;
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2605_: u8 = 0;
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2611_: u8 = 0;
    let mut v_a_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2615_: u8 = 0;
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2619_: u8 = 0;
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2624_: u8 = 0;
    let mut v_a_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2628_: u8 = 0;
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2632_: u8 = 0;
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2637_: u8 = 0;
    let mut v_reuseFailAlloc_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2639_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2542_ = l_Lean_Meta_Context_config(v_a_2537_);
                v_foApprox_2543_ = leanh::lean_ctor_get_uint8(v___x_2542_, 0 as u32);
                v_ctxApprox_2544_ = leanh::lean_ctor_get_uint8(v___x_2542_, 1 as u32);
                v_quasiPatternApprox_2545_ =
                    leanh::lean_ctor_get_uint8(v___x_2542_, 2 as u32);
                v_constApprox_2546_ = leanh::lean_ctor_get_uint8(v___x_2542_, 3 as u32);
                v_isDefEqStuckEx_2547_ = leanh::lean_ctor_get_uint8(v___x_2542_, 4 as u32);
                v_unificationHints_2548_ = leanh::lean_ctor_get_uint8(v___x_2542_, 5 as u32);
                v_proofIrrelevance_2549_ = leanh::lean_ctor_get_uint8(v___x_2542_, 6 as u32);
                v_assignSyntheticOpaque_2550_ =
                    leanh::lean_ctor_get_uint8(v___x_2542_, 7 as u32);
                v_offsetCnstrs_2551_ = leanh::lean_ctor_get_uint8(v___x_2542_, 8 as u32);
                v_etaStruct_2552_ = leanh::lean_ctor_get_uint8(v___x_2542_, 10 as u32);
                v_univApprox_2553_ = leanh::lean_ctor_get_uint8(v___x_2542_, 11 as u32);
                v_iota_2554_ = leanh::lean_ctor_get_uint8(v___x_2542_, 12 as u32);
                v_beta_2555_ = leanh::lean_ctor_get_uint8(v___x_2542_, 13 as u32);
                v_proj_2556_ = leanh::lean_ctor_get_uint8(v___x_2542_, 14 as u32);
                v_zeta_2557_ = leanh::lean_ctor_get_uint8(v___x_2542_, 15 as u32);
                v_zetaDelta_2558_ = leanh::lean_ctor_get_uint8(v___x_2542_, 16 as u32);
                v_zetaUnused_2559_ = leanh::lean_ctor_get_uint8(v___x_2542_, 17 as u32);
                v_zetaHave_2560_ = leanh::lean_ctor_get_uint8(v___x_2542_, 18 as u32);
                v_isSharedCheck_2639_ = (!leanh::lean_is_exclusive(v___x_2542_)) as u8;
                if v_isSharedCheck_2639_ == 0 {
                    v___x_2562_ = v___x_2542_;
                    v_isShared_2563_ = v_isSharedCheck_2639_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2542_);
                    v___x_2562_ = leanh::lean_box(0);
                    v_isShared_2563_ = v_isSharedCheck_2639_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_2564_ = leanh::lean_ctor_get_uint8(
                    v_a_2537_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2565_ = leanh::lean_ctor_get(v_a_2537_, 1);
                leanh::lean_inc(v_zetaDeltaSet_2565_);
                v_lctx_2566_ = leanh::lean_ctor_get(v_a_2537_, 2);
                leanh::lean_inc_ref(v_lctx_2566_);
                v_localInstances_2567_ = leanh::lean_ctor_get(v_a_2537_, 3);
                leanh::lean_inc_ref(v_localInstances_2567_);
                v_defEqCtx_x3f_2568_ = leanh::lean_ctor_get(v_a_2537_, 4);
                leanh::lean_inc(v_defEqCtx_x3f_2568_);
                v_synthPendingDepth_2569_ = leanh::lean_ctor_get(v_a_2537_, 5);
                leanh::lean_inc(v_synthPendingDepth_2569_);
                v_canUnfold_x3f_2570_ = leanh::lean_ctor_get(v_a_2537_, 6);
                leanh::lean_inc(v_canUnfold_x3f_2570_);
                v_univApprox_2571_ = leanh::lean_ctor_get_uint8(
                    v_a_2537_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2572_ = leanh::lean_ctor_get_uint8(
                    v_a_2537_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2573_ = leanh::lean_ctor_get_uint8(
                    v_a_2537_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2574_ = 3;
                if v_isShared_2563_ == 0 {
                    v_config_2576_ = v___x_2562_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2638_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        0 as u32,
                        v_foApprox_2543_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        1 as u32,
                        v_ctxApprox_2544_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        2 as u32,
                        v_quasiPatternApprox_2545_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        3 as u32,
                        v_constApprox_2546_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        4 as u32,
                        v_isDefEqStuckEx_2547_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        5 as u32,
                        v_unificationHints_2548_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        6 as u32,
                        v_proofIrrelevance_2549_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        7 as u32,
                        v_assignSyntheticOpaque_2550_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        8 as u32,
                        v_offsetCnstrs_2551_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        10 as u32,
                        v_etaStruct_2552_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        11 as u32,
                        v_univApprox_2553_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        12 as u32,
                        v_iota_2554_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        13 as u32,
                        v_beta_2555_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        14 as u32,
                        v_proj_2556_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        15 as u32,
                        v_zeta_2557_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        16 as u32,
                        v_zetaDelta_2558_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        17 as u32,
                        v_zetaUnused_2559_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2638_,
                        18 as u32,
                        v_zetaHave_2560_,
                    );
                    v_config_2576_ = v_reuseFailAlloc_2638_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_2576_, 9 as u32, v___x_2574_);
                v___x_2577_ = l_Lean_Meta_Context_configKey(v_a_2537_);
                leanh::lean_dec_ref(v_a_2537_);
                v___x_2578_ = 3u64;
                v___x_2579_ = lean_uint64_shift_right(v___x_2577_, v___x_2578_);
                v___x_2580_ = lean_uint64_shift_left(v___x_2579_, v___x_2578_);
                v___x_2581_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName___closed__0), core::ptr::addr_of_mut!(l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName___closed__0_once), _init_l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName___closed__0);
                v_key_2582_ = lean_uint64_lor(v___x_2580_, v___x_2581_);
                v___x_2583_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_2583_, 0, v_config_2576_);
                leanh::lean_ctor_set_uint64(
                    v___x_2583_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_2582_,
                );
                v___x_2584_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2584_, 0, v___x_2583_);
                leanh::lean_ctor_set(v___x_2584_, 1, v_zetaDeltaSet_2565_);
                leanh::lean_ctor_set(v___x_2584_, 2, v_lctx_2566_);
                leanh::lean_ctor_set(v___x_2584_, 3, v_localInstances_2567_);
                leanh::lean_ctor_set(v___x_2584_, 4, v_defEqCtx_x3f_2568_);
                leanh::lean_ctor_set(v___x_2584_, 5, v_synthPendingDepth_2569_);
                leanh::lean_ctor_set(v___x_2584_, 6, v_canUnfold_x3f_2570_);
                leanh::lean_ctor_set_uint8(
                    v___x_2584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2564_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2571_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2572_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2584_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2573_,
                );
                leanh::lean_inc_ref(v_type_2535_);
                v___x_2585_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName(v_type_2535_, v_baseName_2536_, v___x_2584_, v_a_2538_, v_a_2539_, v_a_2540_);
                if leanh::lean_obj_tag(v___x_2585_) == 0 {
                    v_a_2586_ = leanh::lean_ctor_get(v___x_2585_, 0);
                    v_isSharedCheck_2637_ = (!leanh::lean_is_exclusive(v___x_2585_)) as u8;
                    if v_isSharedCheck_2637_ == 0 {
                        v___x_2588_ = v___x_2585_;
                        v_isShared_2589_ = v_isSharedCheck_2637_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2586_);
                        leanh::lean_dec(v___x_2585_);
                        v___x_2588_ = leanh::lean_box(0);
                        v_isShared_2589_ = v_isSharedCheck_2637_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2584_, 7);
                    leanh::lean_dec_ref(v_type_2535_);
                    return v___x_2585_;
                }
            }
            3 => {
                v___x_2590_ = 1;
                v___x_2591_ = (leanh::lean_unbox(v_a_2586_) as u8);
                leanh::lean_dec(v_a_2586_);
                if v___x_2591_ == 0 {
                    leanh::lean_del_object(v___x_2588_);
                    v___x_2592_ = l_Lean_Meta_whnfCore(
                        v_type_2535_,
                        v___x_2584_,
                        v_a_2538_,
                        v_a_2539_,
                        v_a_2540_,
                    );
                    if leanh::lean_obj_tag(v___x_2592_) == 0 {
                        v_a_2593_ = leanh::lean_ctor_get(v___x_2592_, 0);
                        leanh::lean_inc_n(v_a_2593_, 2);
                        leanh::lean_dec_ref_known(v___x_2592_, 1);
                        v___x_2594_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName(v_a_2593_, v_baseName_2536_, v___x_2584_, v_a_2538_, v_a_2539_, v_a_2540_);
                        if leanh::lean_obj_tag(v___x_2594_) == 0 {
                            v_a_2595_ = leanh::lean_ctor_get(v___x_2594_, 0);
                            v_isSharedCheck_2624_ =
                                (!leanh::lean_is_exclusive(v___x_2594_)) as u8;
                            if v_isSharedCheck_2624_ == 0 {
                                v___x_2597_ = v___x_2594_;
                                v_isShared_2598_ = v_isSharedCheck_2624_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2595_);
                                leanh::lean_dec(v___x_2594_);
                                v___x_2597_ = leanh::lean_box(0);
                                v_isShared_2598_ = v_isSharedCheck_2624_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2593_);
                            leanh::lean_dec_ref_known(v___x_2584_, 7);
                            return v___x_2594_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_2584_, 7);
                        v_a_2625_ = leanh::lean_ctor_get(v___x_2592_, 0);
                        v_isSharedCheck_2632_ =
                            (!leanh::lean_is_exclusive(v___x_2592_)) as u8;
                        if v_isSharedCheck_2632_ == 0 {
                            v___x_2627_ = v___x_2592_;
                            v_isShared_2628_ = v_isSharedCheck_2632_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2625_);
                            leanh::lean_dec(v___x_2592_);
                            v___x_2627_ = leanh::lean_box(0);
                            v_isShared_2628_ = v_isSharedCheck_2632_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2584_, 7);
                    leanh::lean_dec_ref(v_type_2535_);
                    v___x_2633_ = leanh::lean_box((v___x_2590_) as usize);
                    if v_isShared_2589_ == 0 {
                        leanh::lean_ctor_set(v___x_2588_, 0, v___x_2633_);
                        v___x_2635_ = v___x_2588_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2636_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
                        v___x_2635_ = v_reuseFailAlloc_2636_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2599_ = (leanh::lean_unbox(v_a_2595_) as u8);
                if v___x_2599_ == 0 {
                    leanh::lean_del_object(v___x_2597_);
                    v___x_2600_ = (leanh::lean_unbox(v_a_2595_) as u8);
                    v___x_2601_ = l_Lean_Meta_unfoldDefinition_x3f(
                        v_a_2593_,
                        v___x_2600_,
                        v___x_2584_,
                        v_a_2538_,
                        v_a_2539_,
                        v_a_2540_,
                    );
                    if leanh::lean_obj_tag(v___x_2601_) == 0 {
                        v_a_2602_ = leanh::lean_ctor_get(v___x_2601_, 0);
                        v_isSharedCheck_2611_ =
                            (!leanh::lean_is_exclusive(v___x_2601_)) as u8;
                        if v_isSharedCheck_2611_ == 0 {
                            v___x_2604_ = v___x_2601_;
                            v_isShared_2605_ = v_isSharedCheck_2611_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2602_);
                            leanh::lean_dec(v___x_2601_);
                            v___x_2604_ = leanh::lean_box(0);
                            v_isShared_2605_ = v_isSharedCheck_2611_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2595_);
                        leanh::lean_dec_ref_known(v___x_2584_, 7);
                        v_a_2612_ = leanh::lean_ctor_get(v___x_2601_, 0);
                        v_isSharedCheck_2619_ =
                            (!leanh::lean_is_exclusive(v___x_2601_)) as u8;
                        if v_isSharedCheck_2619_ == 0 {
                            v___x_2614_ = v___x_2601_;
                            v_isShared_2615_ = v_isSharedCheck_2619_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2612_);
                            leanh::lean_dec(v___x_2601_);
                            v___x_2614_ = leanh::lean_box(0);
                            v_isShared_2615_ = v_isSharedCheck_2619_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2595_);
                    leanh::lean_dec(v_a_2593_);
                    leanh::lean_dec_ref_known(v___x_2584_, 7);
                    v___x_2620_ = leanh::lean_box((v___x_2590_) as usize);
                    if v_isShared_2598_ == 0 {
                        leanh::lean_ctor_set(v___x_2597_, 0, v___x_2620_);
                        v___x_2622_ = v___x_2597_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2623_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
                        v___x_2622_ = v_reuseFailAlloc_2623_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_2602_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2584_, 7);
                    if v_isShared_2605_ == 0 {
                        leanh::lean_ctor_set(v___x_2604_, 0, v_a_2595_);
                        v___x_2607_ = v___x_2604_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2608_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2595_);
                        v___x_2607_ = v_reuseFailAlloc_2608_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2604_);
                    leanh::lean_dec(v_a_2595_);
                    v_val_2609_ = leanh::lean_ctor_get(v_a_2602_, 0);
                    leanh::lean_inc(v_val_2609_);
                    leanh::lean_dec_ref_known(v_a_2602_, 1);
                    v_type_2535_ = v_val_2609_;
                    v_a_2537_ = v___x_2584_;
                    state = 0;
                    continue;
                }
            }
            6 => {
                return v___x_2607_;
            }
            7 => {
                if v_isShared_2615_ == 0 {
                    v___x_2617_ = v___x_2614_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2618_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
                    v___x_2617_ = v_reuseFailAlloc_2618_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2617_;
            }
            9 => {
                return v___x_2622_;
            }
            10 => {
                if v_isShared_2628_ == 0 {
                    v___x_2630_ = v___x_2627_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2631_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
                    v___x_2630_ = v_reuseFailAlloc_2631_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2630_;
            }
            12 => {
                return v___x_2635_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName___boxed(
    mut v_type_2640_: *mut leanh::LeanObject,
    mut v_baseName_2641_: *mut leanh::LeanObject,
    mut v_a_2642_: *mut leanh::LeanObject,
    mut v_a_2643_: *mut leanh::LeanObject,
    mut v_a_2644_: *mut leanh::LeanObject,
    mut v_a_2645_: *mut leanh::LeanObject,
    mut v_a_2646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2647_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName(v_type_2640_, v_baseName_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
    leanh::lean_dec(v_a_2645_);
    leanh::lean_dec_ref(v_a_2644_);
    leanh::lean_dec(v_a_2643_);
    leanh::lean_dec(v_baseName_2641_);
    return v_res_2647_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___redArg(
    mut v_e_2648_: *mut leanh::LeanObject,
    mut v___y_2649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2651_: u8 = 0;
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2665_: u8 = 0;
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2671_: u8 = 0;
    let mut v_unused_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2651_ = l_Lean_Expr_hasMVar(v_e_2648_);
                if v___x_2651_ == 0 {
                    v___x_2652_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2652_, 0, v_e_2648_);
                    return v___x_2652_;
                } else {
                    v___x_2653_ = lean_st_ref_get(v___y_2649_);
                    v_mctx_2654_ = leanh::lean_ctor_get(v___x_2653_, 0);
                    leanh::lean_inc_ref(v_mctx_2654_);
                    leanh::lean_dec(v___x_2653_);
                    v___x_2655_ = l_Lean_instantiateMVarsCore(v_mctx_2654_, v_e_2648_);
                    v_fst_2656_ = leanh::lean_ctor_get(v___x_2655_, 0);
                    leanh::lean_inc(v_fst_2656_);
                    v_snd_2657_ = leanh::lean_ctor_get(v___x_2655_, 1);
                    leanh::lean_inc(v_snd_2657_);
                    leanh::lean_dec_ref(v___x_2655_);
                    v___x_2658_ = lean_st_ref_take(v___y_2649_);
                    v_cache_2659_ = leanh::lean_ctor_get(v___x_2658_, 1);
                    v_zetaDeltaFVarIds_2660_ = leanh::lean_ctor_get(v___x_2658_, 2);
                    v_postponed_2661_ = leanh::lean_ctor_get(v___x_2658_, 3);
                    v_diag_2662_ = leanh::lean_ctor_get(v___x_2658_, 4);
                    v_isSharedCheck_2671_ = (!leanh::lean_is_exclusive(v___x_2658_)) as u8;
                    if v_isSharedCheck_2671_ == 0 {
                        v_unused_2672_ = leanh::lean_ctor_get(v___x_2658_, 0);
                        leanh::lean_dec(v_unused_2672_);
                        v___x_2664_ = v___x_2658_;
                        v_isShared_2665_ = v_isSharedCheck_2671_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_2662_);
                        leanh::lean_inc(v_postponed_2661_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_2660_);
                        leanh::lean_inc(v_cache_2659_);
                        leanh::lean_dec(v___x_2658_);
                        v___x_2664_ = leanh::lean_box(0);
                        v_isShared_2665_ = v_isSharedCheck_2671_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2665_ == 0 {
                    leanh::lean_ctor_set(v___x_2664_, 0, v_snd_2657_);
                    v___x_2667_ = v___x_2664_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2670_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_snd_2657_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_cache_2659_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2670_,
                        2,
                        v_zetaDeltaFVarIds_2660_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 3, v_postponed_2661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 4, v_diag_2662_);
                    v___x_2667_ = v_reuseFailAlloc_2670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2668_ = lean_st_ref_set(v___y_2649_, v___x_2667_);
                v___x_2669_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2669_, 0, v_fst_2656_);
                return v___x_2669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___redArg___boxed(
    mut v_e_2673_: *mut leanh::LeanObject,
    mut v___y_2674_: *mut leanh::LeanObject,
    mut v___y_2675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Lean_instantiateMVars___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___redArg(v_e_2673_, v___y_2674_);
    leanh::lean_dec(v___y_2674_);
    return v_res_2676_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0(
    mut v_e_2677_: *mut leanh::LeanObject,
    mut v___y_2678_: *mut leanh::LeanObject,
    mut v___y_2679_: *mut leanh::LeanObject,
    mut v___y_2680_: *mut leanh::LeanObject,
    mut v___y_2681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2683_ = l_Lean_instantiateMVars___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___redArg(v_e_2677_, v___y_2679_);
    return v___x_2683_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___boxed(
    mut v_e_2684_: *mut leanh::LeanObject,
    mut v___y_2685_: *mut leanh::LeanObject,
    mut v___y_2686_: *mut leanh::LeanObject,
    mut v___y_2687_: *mut leanh::LeanObject,
    mut v___y_2688_: *mut leanh::LeanObject,
    mut v___y_2689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2690_ = l_Lean_instantiateMVars___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0(v_e_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
    leanh::lean_dec(v___y_2688_);
    leanh::lean_dec_ref(v___y_2687_);
    leanh::lean_dec(v___y_2686_);
    leanh::lean_dec_ref(v___y_2685_);
    return v_res_2690_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__3___redArg___lam__0(
    mut v_k_2691_: *mut leanh::LeanObject,
    mut v_b_2692_: *mut leanh::LeanObject,
    mut v_c_2693_: *mut leanh::LeanObject,
    mut v___y_2694_: *mut leanh::LeanObject,
    mut v___y_2695_: *mut leanh::LeanObject,
    mut v___y_2696_: *mut leanh::LeanObject,
    mut v___y_2697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2697_);
    leanh::lean_inc_ref(v___y_2696_);
    leanh::lean_inc(v___y_2695_);
    leanh::lean_inc_ref(v___y_2694_);
    v___x_2699_ = leanh::lean_apply_7(
        v_k_2691_,
        v_b_2692_,
        v_c_2693_,
        v___y_2694_,
        v___y_2695_,
        v___y_2696_,
        v___y_2697_,
        leanh::lean_box(0),
    );
    return v___x_2699_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__3___redArg___lam__0___boxed(
    mut v_k_2700_: *mut leanh::LeanObject,
    mut v_b_2701_: *mut leanh::LeanObject,
    mut v_c_2702_: *mut leanh::LeanObject,
    mut v___y_2703_: *mut leanh::LeanObject,
    mut v___y_2704_: *mut leanh::LeanObject,
    mut v___y_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
    mut v___y_2707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2708_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__3___redArg___lam__0(v_k_2700_, v_b_2701_, v_c_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
    leanh::lean_dec(v___y_2706_);
    leanh::lean_dec_ref(v___y_2705_);
    leanh::lean_dec(v___y_2704_);
    leanh::lean_dec_ref(v___y_2703_);
    return v_res_2708_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__3___redArg(
    mut v_type_2709_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_2710_: *mut leanh::LeanObject,
    mut v_k_2711_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2712_: u8,
    mut v_whnfType_2713_: u8,
    mut v___y_2714_: *mut leanh::LeanObject,
    mut v___y_2715_: *mut leanh::LeanObject,
    mut v___y_2716_: *mut leanh::LeanObject,
    mut v___y_2717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2724_: u8 = 0;
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut v_a_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2732_: u8 = 0;
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2719_ = leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_2719_, 0, v_k_2711_);
                v___x_2720_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    leanh::lean_box(0),
                    v_type_2709_,
                    v_maxFVars_x3f_2710_,
                    v___f_2719_,
                    v_cleanupAnnotations_2712_,
                    v_whnfType_2713_,
                    v___y_2714_,
                    v___y_2715_,
                    v___y_2716_,
                    v___y_2717_,
                );
                if leanh::lean_obj_tag(v___x_2720_) == 0 {
                    v_a_2721_ = leanh::lean_ctor_get(v___x_2720_, 0);
                    v_isSharedCheck_2728_ = (!leanh::lean_is_exclusive(v___x_2720_)) as u8;
                    if v_isSharedCheck_2728_ == 0 {
                        v___x_2723_ = v___x_2720_;
                        v_isShared_2724_ = v_isSharedCheck_2728_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2721_);
                        leanh::lean_dec(v___x_2720_);
                        v___x_2723_ = leanh::lean_box(0);
                        v_isShared_2724_ = v_isSharedCheck_2728_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2729_ = leanh::lean_ctor_get(v___x_2720_, 0);
                    v_isSharedCheck_2736_ = (!leanh::lean_is_exclusive(v___x_2720_)) as u8;
                    if v_isSharedCheck_2736_ == 0 {
                        v___x_2731_ = v___x_2720_;
                        v_isShared_2732_ = v_isSharedCheck_2736_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2729_);
                        leanh::lean_dec(v___x_2720_);
                        v___x_2731_ = leanh::lean_box(0);
                        v_isShared_2732_ = v_isSharedCheck_2736_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2724_ == 0 {
                    v___x_2726_ = v___x_2723_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
                    v___x_2726_ = v_reuseFailAlloc_2727_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2726_;
            }
            3 => {
                if v_isShared_2732_ == 0 {
                    v___x_2734_ = v___x_2731_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2735_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
                    v___x_2734_ = v_reuseFailAlloc_2735_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__3___redArg___boxed(
    mut v_type_2737_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_2738_: *mut leanh::LeanObject,
    mut v_k_2739_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2740_: *mut leanh::LeanObject,
    mut v_whnfType_2741_: *mut leanh::LeanObject,
    mut v___y_2742_: *mut leanh::LeanObject,
    mut v___y_2743_: *mut leanh::LeanObject,
    mut v___y_2744_: *mut leanh::LeanObject,
    mut v___y_2745_: *mut leanh::LeanObject,
    mut v___y_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2747_: u8 = 0;
    let mut v_whnfType_boxed_2748_: u8 = 0;
    let mut v_res_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2747_ = (leanh::lean_unbox(v_cleanupAnnotations_2740_) as u8);
    v_whnfType_boxed_2748_ = (leanh::lean_unbox(v_whnfType_2741_) as u8);
    v_res_2749_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__3___redArg(v_type_2737_, v_maxFVars_x3f_2738_, v_k_2739_, v_cleanupAnnotations_boxed_2747_, v_whnfType_boxed_2748_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
    leanh::lean_dec(v___y_2745_);
    leanh::lean_dec_ref(v___y_2744_);
    leanh::lean_dec(v___y_2743_);
    leanh::lean_dec_ref(v___y_2742_);
    return v_res_2749_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__3(
    mut v_00_u03b1_2750_: *mut leanh::LeanObject,
    mut v_type_2751_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_2752_: *mut leanh::LeanObject,
    mut v_k_2753_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2754_: u8,
    mut v_whnfType_2755_: u8,
    mut v___y_2756_: *mut leanh::LeanObject,
    mut v___y_2757_: *mut leanh::LeanObject,
    mut v___y_2758_: *mut leanh::LeanObject,
    mut v___y_2759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2761_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__3___redArg(v_type_2751_, v_maxFVars_x3f_2752_, v_k_2753_, v_cleanupAnnotations_2754_, v_whnfType_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
    return v___x_2761_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__3___boxed(
    mut v_00_u03b1_2762_: *mut leanh::LeanObject,
    mut v_type_2763_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_2764_: *mut leanh::LeanObject,
    mut v_k_2765_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2766_: *mut leanh::LeanObject,
    mut v_whnfType_2767_: *mut leanh::LeanObject,
    mut v___y_2768_: *mut leanh::LeanObject,
    mut v___y_2769_: *mut leanh::LeanObject,
    mut v___y_2770_: *mut leanh::LeanObject,
    mut v___y_2771_: *mut leanh::LeanObject,
    mut v___y_2772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2773_: u8 = 0;
    let mut v_whnfType_boxed_2774_: u8 = 0;
    let mut v_res_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2773_ = (leanh::lean_unbox(v_cleanupAnnotations_2766_) as u8);
    v_whnfType_boxed_2774_ = (leanh::lean_unbox(v_whnfType_2767_) as u8);
    v_res_2775_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__3(v_00_u03b1_2762_, v_type_2763_, v_maxFVars_x3f_2764_, v_k_2765_, v_cleanupAnnotations_boxed_2773_, v_whnfType_boxed_2774_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
    leanh::lean_dec(v___y_2771_);
    leanh::lean_dec_ref(v___y_2770_);
    leanh::lean_dec(v___y_2769_);
    leanh::lean_dec_ref(v___y_2768_);
    return v_res_2775_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2777_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__0;
    v___x_2778_ = l_Lean_stringToMessageData(v___x_2777_);
    return v___x_2778_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0(
    mut v___x_2779_: *mut leanh::LeanObject,
    mut v_baseName_2780_: *mut leanh::LeanObject,
    mut v___x_2781_: *mut leanh::LeanObject,
    mut v___x_2782_: *mut leanh::LeanObject,
    mut v_a_2783_: *mut leanh::LeanObject,
    mut v___x_2784_: *mut leanh::LeanObject,
    mut v_args_2785_: *mut leanh::LeanObject,
    mut v_____r_2786_: *mut leanh::LeanObject,
    mut v___y_2787_: *mut leanh::LeanObject,
    mut v___y_2788_: *mut leanh::LeanObject,
    mut v___y_2789_: *mut leanh::LeanObject,
    mut v___y_2790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: u8 = 0;
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2816_: u8 = 0;
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut v_a_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut v_a_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2832_: u8 = 0;
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut v_a_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2840_: u8 = 0;
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: u8 = 0;
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: u8 = 0;
    let mut v___x_2853_: u8 = 0;
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2859_: u8 = 0;
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2863_: u8 = 0;
    let mut v_a_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2867_: u8 = 0;
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2871_: u8 = 0;
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: u8 = 0;
    let mut v___x_2875_: u8 = 0;
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2885_: u8 = 0;
    let mut v_a_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2893_: u8 = 0;
    let mut v_a_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut v_a_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___x_2779_);
                v___x_2845_ = l_Lean_FVarId_getType___redArg(
                    v___x_2779_,
                    v___y_2787_,
                    v___y_2789_,
                    v___y_2790_,
                );
                if leanh::lean_obj_tag(v___x_2845_) == 0 {
                    v_a_2846_ = leanh::lean_ctor_get(v___x_2845_, 0);
                    leanh::lean_inc(v_a_2846_);
                    leanh::lean_dec_ref_known(v___x_2845_, 1);
                    leanh::lean_inc_ref(v___y_2787_);
                    v___x_2847_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_typeMatchesBaseName(v_a_2846_, v_baseName_2780_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
                    if leanh::lean_obj_tag(v___x_2847_) == 0 {
                        v_a_2848_ = leanh::lean_ctor_get(v___x_2847_, 0);
                        leanh::lean_inc(v_a_2848_);
                        leanh::lean_dec_ref_known(v___x_2847_, 1);
                        v___x_2849_ = (leanh::lean_unbox(v_a_2848_) as u8);
                        leanh::lean_dec(v_a_2848_);
                        if v___x_2849_ == 0 {
                            leanh::lean_dec(v_a_2783_);
                            leanh::lean_dec(v___x_2782_);
                            v___x_2850_ = l_Lean_FVarId_getBinderInfo___redArg(
                                v___x_2779_,
                                v___y_2787_,
                                v___y_2789_,
                                v___y_2790_,
                            );
                            if leanh::lean_obj_tag(v___x_2850_) == 0 {
                                v_a_2851_ = leanh::lean_ctor_get(v___x_2850_, 0);
                                leanh::lean_inc(v_a_2851_);
                                leanh::lean_dec_ref_known(v___x_2850_, 1);
                                v___x_2852_ = (leanh::lean_unbox(v_a_2851_) as u8);
                                leanh::lean_dec(v_a_2851_);
                                v___x_2853_ = l_Lean_BinderInfo_isExplicit(v___x_2852_);
                                if v___x_2853_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2854_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1);
                                    v___x_2855_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v___x_2854_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
                                    if leanh::lean_obj_tag(v___x_2855_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_2855_, 1);
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec_ref(v___x_2781_);
                                        v_a_2856_ = leanh::lean_ctor_get(v___x_2855_, 0);
                                        v_isSharedCheck_2863_ =
                                            (!leanh::lean_is_exclusive(v___x_2855_)) as u8;
                                        if v_isSharedCheck_2863_ == 0 {
                                            v___x_2858_ = v___x_2855_;
                                            v_isShared_2859_ = v_isSharedCheck_2863_;
                                            state = 12;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2856_);
                                            leanh::lean_dec(v___x_2855_);
                                            v___x_2858_ = leanh::lean_box(0);
                                            v_isShared_2859_ = v_isSharedCheck_2863_;
                                            state = 12;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_2781_);
                                v_a_2864_ = leanh::lean_ctor_get(v___x_2850_, 0);
                                v_isSharedCheck_2871_ =
                                    (!leanh::lean_is_exclusive(v___x_2850_)) as u8;
                                if v_isSharedCheck_2871_ == 0 {
                                    v___x_2866_ = v___x_2850_;
                                    v_isShared_2867_ = v_isSharedCheck_2871_;
                                    state = 14;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2864_);
                                    leanh::lean_dec(v___x_2850_);
                                    v___x_2866_ = leanh::lean_box(0);
                                    v_isShared_2867_ = v_isSharedCheck_2871_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_2781_);
                            v___x_2872_ = l_Lean_FVarId_getBinderInfo___redArg(
                                v___x_2779_,
                                v___y_2787_,
                                v___y_2789_,
                                v___y_2790_,
                            );
                            if leanh::lean_obj_tag(v___x_2872_) == 0 {
                                v_a_2873_ = leanh::lean_ctor_get(v___x_2872_, 0);
                                leanh::lean_inc(v_a_2873_);
                                leanh::lean_dec_ref_known(v___x_2872_, 1);
                                v___x_2874_ = (leanh::lean_unbox(v_a_2873_) as u8);
                                leanh::lean_dec(v_a_2873_);
                                v___x_2875_ = l_Lean_BinderInfo_isExplicit(v___x_2874_);
                                if v___x_2875_ == 0 {
                                    v___x_2876_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1);
                                    v___x_2877_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v___x_2876_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
                                    if leanh::lean_obj_tag(v___x_2877_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_2877_, 1);
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_2783_);
                                        leanh::lean_dec(v___x_2782_);
                                        v_a_2878_ = leanh::lean_ctor_get(v___x_2877_, 0);
                                        v_isSharedCheck_2885_ =
                                            (!leanh::lean_is_exclusive(v___x_2877_)) as u8;
                                        if v_isSharedCheck_2885_ == 0 {
                                            v___x_2880_ = v___x_2877_;
                                            v_isShared_2881_ = v_isSharedCheck_2885_;
                                            state = 16;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2878_);
                                            leanh::lean_dec(v___x_2877_);
                                            v___x_2880_ = leanh::lean_box(0);
                                            v_isShared_2881_ = v_isSharedCheck_2885_;
                                            state = 16;
                                            continue;
                                        }
                                    }
                                } else {
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_2783_);
                                leanh::lean_dec(v___x_2782_);
                                v_a_2886_ = leanh::lean_ctor_get(v___x_2872_, 0);
                                v_isSharedCheck_2893_ =
                                    (!leanh::lean_is_exclusive(v___x_2872_)) as u8;
                                if v_isSharedCheck_2893_ == 0 {
                                    v___x_2888_ = v___x_2872_;
                                    v_isShared_2889_ = v_isSharedCheck_2893_;
                                    state = 18;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2886_);
                                    leanh::lean_dec(v___x_2872_);
                                    v___x_2888_ = leanh::lean_box(0);
                                    v_isShared_2889_ = v_isSharedCheck_2893_;
                                    state = 18;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2783_);
                        leanh::lean_dec(v___x_2782_);
                        leanh::lean_dec_ref(v___x_2781_);
                        leanh::lean_dec(v___x_2779_);
                        v_a_2894_ = leanh::lean_ctor_get(v___x_2847_, 0);
                        v_isSharedCheck_2901_ =
                            (!leanh::lean_is_exclusive(v___x_2847_)) as u8;
                        if v_isSharedCheck_2901_ == 0 {
                            v___x_2896_ = v___x_2847_;
                            v_isShared_2897_ = v_isSharedCheck_2901_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2894_);
                            leanh::lean_dec(v___x_2847_);
                            v___x_2896_ = leanh::lean_box(0);
                            v_isShared_2897_ = v_isSharedCheck_2901_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2783_);
                    leanh::lean_dec(v___x_2782_);
                    leanh::lean_dec_ref(v___x_2781_);
                    leanh::lean_dec(v___x_2779_);
                    v_a_2902_ = leanh::lean_ctor_get(v___x_2845_, 0);
                    v_isSharedCheck_2909_ = (!leanh::lean_is_exclusive(v___x_2845_)) as u8;
                    if v_isSharedCheck_2909_ == 0 {
                        v___x_2904_ = v___x_2845_;
                        v_isShared_2905_ = v_isSharedCheck_2909_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2902_);
                        leanh::lean_dec(v___x_2845_);
                        v___x_2904_ = leanh::lean_box(0);
                        v_isShared_2905_ = v_isSharedCheck_2909_;
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2793_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2793_, 0, v___x_2781_);
                v___x_2794_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2794_, 0, v___x_2793_);
                return v___x_2794_;
            }
            2 => {
                v___x_2796_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2796_, 0, v___x_2782_);
                leanh::lean_ctor_set(v___x_2796_, 1, v_a_2783_);
                v___x_2797_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2797_, 0, v___x_2796_);
                v___x_2798_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2798_, 0, v___x_2797_);
                leanh::lean_ctor_set(v___x_2798_, 1, v___x_2784_);
                v___x_2799_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2799_, 0, v___x_2798_);
                v___x_2800_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2800_, 0, v___x_2799_);
                return v___x_2800_;
            }
            3 => {
                v___x_2802_ = l_Lean_instInhabitedExpr;
                v___x_2803_ = lean_array_get_borrowed(v___x_2802_, v_args_2785_, v_a_2783_);
                leanh::lean_inc(v___y_2790_);
                leanh::lean_inc_ref(v___y_2789_);
                leanh::lean_inc(v___y_2788_);
                leanh::lean_inc_ref(v___y_2787_);
                leanh::lean_inc(v___x_2803_);
                v___x_2804_ = lean_infer_type(
                    v___x_2803_,
                    v___y_2787_,
                    v___y_2788_,
                    v___y_2789_,
                    v___y_2790_,
                );
                if leanh::lean_obj_tag(v___x_2804_) == 0 {
                    v_a_2805_ = leanh::lean_ctor_get(v___x_2804_, 0);
                    leanh::lean_inc(v_a_2805_);
                    leanh::lean_dec_ref_known(v___x_2804_, 1);
                    v___x_2806_ = l_Lean_instantiateMVars___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__0___redArg(v_a_2805_, v___y_2788_);
                    if leanh::lean_obj_tag(v___x_2806_) == 0 {
                        v_a_2807_ = leanh::lean_ctor_get(v___x_2806_, 0);
                        leanh::lean_inc(v_a_2807_);
                        leanh::lean_dec_ref_known(v___x_2806_, 1);
                        v___x_2808_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName(v_a_2807_, v_baseName_2780_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
                        if leanh::lean_obj_tag(v___x_2808_) == 0 {
                            v_a_2809_ = leanh::lean_ctor_get(v___x_2808_, 0);
                            leanh::lean_inc(v_a_2809_);
                            leanh::lean_dec_ref_known(v___x_2808_, 1);
                            v___x_2810_ = (leanh::lean_unbox(v_a_2809_) as u8);
                            leanh::lean_dec(v_a_2809_);
                            if v___x_2810_ == 0 {
                                v___x_2811_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1);
                                v___x_2812_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v___x_2811_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
                                if leanh::lean_obj_tag(v___x_2812_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_2812_, 1);
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_2783_);
                                    leanh::lean_dec(v___x_2782_);
                                    v_a_2813_ = leanh::lean_ctor_get(v___x_2812_, 0);
                                    v_isSharedCheck_2820_ =
                                        (!leanh::lean_is_exclusive(v___x_2812_)) as u8;
                                    if v_isSharedCheck_2820_ == 0 {
                                        v___x_2815_ = v___x_2812_;
                                        v_isShared_2816_ = v_isSharedCheck_2820_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2813_);
                                        leanh::lean_dec(v___x_2812_);
                                        v___x_2815_ = leanh::lean_box(0);
                                        v_isShared_2816_ = v_isSharedCheck_2820_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2783_);
                            leanh::lean_dec(v___x_2782_);
                            v_a_2821_ = leanh::lean_ctor_get(v___x_2808_, 0);
                            v_isSharedCheck_2828_ =
                                (!leanh::lean_is_exclusive(v___x_2808_)) as u8;
                            if v_isSharedCheck_2828_ == 0 {
                                v___x_2823_ = v___x_2808_;
                                v_isShared_2824_ = v_isSharedCheck_2828_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2821_);
                                leanh::lean_dec(v___x_2808_);
                                v___x_2823_ = leanh::lean_box(0);
                                v_isShared_2824_ = v_isSharedCheck_2828_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2783_);
                        leanh::lean_dec(v___x_2782_);
                        v_a_2829_ = leanh::lean_ctor_get(v___x_2806_, 0);
                        v_isSharedCheck_2836_ =
                            (!leanh::lean_is_exclusive(v___x_2806_)) as u8;
                        if v_isSharedCheck_2836_ == 0 {
                            v___x_2831_ = v___x_2806_;
                            v_isShared_2832_ = v_isSharedCheck_2836_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2829_);
                            leanh::lean_dec(v___x_2806_);
                            v___x_2831_ = leanh::lean_box(0);
                            v_isShared_2832_ = v_isSharedCheck_2836_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2783_);
                    leanh::lean_dec(v___x_2782_);
                    v_a_2837_ = leanh::lean_ctor_get(v___x_2804_, 0);
                    v_isSharedCheck_2844_ = (!leanh::lean_is_exclusive(v___x_2804_)) as u8;
                    if v_isSharedCheck_2844_ == 0 {
                        v___x_2839_ = v___x_2804_;
                        v_isShared_2840_ = v_isSharedCheck_2844_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2837_);
                        leanh::lean_dec(v___x_2804_);
                        v___x_2839_ = leanh::lean_box(0);
                        v_isShared_2840_ = v_isSharedCheck_2844_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2816_ == 0 {
                    v___x_2818_ = v___x_2815_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2819_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
                    v___x_2818_ = v_reuseFailAlloc_2819_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2818_;
            }
            6 => {
                if v_isShared_2824_ == 0 {
                    v___x_2826_ = v___x_2823_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2827_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
                    v___x_2826_ = v_reuseFailAlloc_2827_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2826_;
            }
            8 => {
                if v_isShared_2832_ == 0 {
                    v___x_2834_ = v___x_2831_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
                    v___x_2834_ = v_reuseFailAlloc_2835_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2834_;
            }
            10 => {
                if v_isShared_2840_ == 0 {
                    v___x_2842_ = v___x_2839_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
                    v___x_2842_ = v_reuseFailAlloc_2843_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2842_;
            }
            12 => {
                if v_isShared_2859_ == 0 {
                    v___x_2861_ = v___x_2858_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2862_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
                    v___x_2861_ = v_reuseFailAlloc_2862_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2861_;
            }
            14 => {
                if v_isShared_2867_ == 0 {
                    v___x_2869_ = v___x_2866_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2870_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
                    v___x_2869_ = v_reuseFailAlloc_2870_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2869_;
            }
            16 => {
                if v_isShared_2881_ == 0 {
                    v___x_2883_ = v___x_2880_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2884_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
                    v___x_2883_ = v_reuseFailAlloc_2884_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2883_;
            }
            18 => {
                if v_isShared_2889_ == 0 {
                    v___x_2891_ = v___x_2888_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2892_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
                    v___x_2891_ = v_reuseFailAlloc_2892_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2891_;
            }
            20 => {
                if v_isShared_2897_ == 0 {
                    v___x_2899_ = v___x_2896_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2900_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
                    v___x_2899_ = v_reuseFailAlloc_2900_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2899_;
            }
            22 => {
                if v_isShared_2905_ == 0 {
                    v___x_2907_ = v___x_2904_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2908_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
                    v___x_2907_ = v_reuseFailAlloc_2908_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___boxed(
    mut v___x_2910_: *mut leanh::LeanObject,
    mut v_baseName_2911_: *mut leanh::LeanObject,
    mut v___x_2912_: *mut leanh::LeanObject,
    mut v___x_2913_: *mut leanh::LeanObject,
    mut v_a_2914_: *mut leanh::LeanObject,
    mut v___x_2915_: *mut leanh::LeanObject,
    mut v_args_2916_: *mut leanh::LeanObject,
    mut v_____r_2917_: *mut leanh::LeanObject,
    mut v___y_2918_: *mut leanh::LeanObject,
    mut v___y_2919_: *mut leanh::LeanObject,
    mut v___y_2920_: *mut leanh::LeanObject,
    mut v___y_2921_: *mut leanh::LeanObject,
    mut v___y_2922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2923_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0(v___x_2910_, v_baseName_2911_, v___x_2912_, v___x_2913_, v_a_2914_, v___x_2915_, v_args_2916_, v_____r_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
    leanh::lean_dec(v___y_2921_);
    leanh::lean_dec_ref(v___y_2920_);
    leanh::lean_dec(v___y_2919_);
    leanh::lean_dec_ref(v___y_2918_);
    leanh::lean_dec_ref(v_args_2916_);
    leanh::lean_dec(v_baseName_2911_);
    return v_res_2923_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg(
    mut v_upperBound_2930_: *mut leanh::LeanObject,
    mut v_params_2931_: *mut leanh::LeanObject,
    mut v___x_2932_: *mut leanh::LeanObject,
    mut v_args_2933_: *mut leanh::LeanObject,
    mut v_baseName_2934_: *mut leanh::LeanObject,
    mut v_a_2935_: *mut leanh::LeanObject,
    mut v_b_2936_: *mut leanh::LeanObject,
    mut v___y_2937_: *mut leanh::LeanObject,
    mut v___y_2938_: *mut leanh::LeanObject,
    mut v___y_2939_: *mut leanh::LeanObject,
    mut v___y_2940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2947_: u8 = 0;
    let mut v_a_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v_a_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2960_: u8 = 0;
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: u8 = 0;
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2983_: u8 = 0;
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_a_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2991_: u8 = 0;
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2965_ = lean_nat_dec_lt(v_a_2935_, v_upperBound_2930_);
                if v___x_2965_ == 0 {
                    leanh::lean_dec(v_a_2935_);
                    leanh::lean_dec(v___x_2932_);
                    v___x_2966_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2966_, 0, v_b_2936_);
                    return v___x_2966_;
                } else {
                    leanh::lean_dec_ref(v_b_2936_);
                    v___x_2967_ = lean_array_fget_borrowed(v_params_2931_, v_a_2935_);
                    v___x_2968_ = l_Lean_Expr_fvarId_x21(v___x_2967_);
                    leanh::lean_inc(v___x_2968_);
                    v___x_2969_ = l_Lean_FVarId_getUserName___redArg(
                        v___x_2968_,
                        v___y_2937_,
                        v___y_2939_,
                        v___y_2940_,
                    );
                    if leanh::lean_obj_tag(v___x_2969_) == 0 {
                        v_a_2970_ = leanh::lean_ctor_get(v___x_2969_, 0);
                        leanh::lean_inc(v_a_2970_);
                        leanh::lean_dec_ref_known(v___x_2969_, 1);
                        v___x_2971_ = leanh::lean_box(0);
                        v___x_2972_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__0;
                        v___x_2973_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__2;
                        v___x_2974_ = lean_name_eq(v_a_2970_, v___x_2973_);
                        leanh::lean_dec(v_a_2970_);
                        if v___x_2974_ == 0 {
                            leanh::lean_inc(v_a_2935_);
                            leanh::lean_inc(v___x_2932_);
                            v___x_2975_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0(v___x_2968_, v_baseName_2934_, v___x_2972_, v___x_2932_, v_a_2935_, v___x_2971_, v_args_2933_, v___x_2971_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
                            v___y_2943_ = v___x_2975_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2976_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1);
                            v___x_2977_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v___x_2976_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
                            if leanh::lean_obj_tag(v___x_2977_) == 0 {
                                v_a_2978_ = leanh::lean_ctor_get(v___x_2977_, 0);
                                leanh::lean_inc(v_a_2978_);
                                leanh::lean_dec_ref_known(v___x_2977_, 1);
                                leanh::lean_inc(v_a_2935_);
                                leanh::lean_inc(v___x_2932_);
                                v___x_2979_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0(v___x_2968_, v_baseName_2934_, v___x_2972_, v___x_2932_, v_a_2935_, v___x_2971_, v_args_2933_, v_a_2978_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
                                v___y_2943_ = v___x_2979_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_2968_);
                                leanh::lean_dec(v_a_2935_);
                                leanh::lean_dec(v___x_2932_);
                                v_a_2980_ = leanh::lean_ctor_get(v___x_2977_, 0);
                                v_isSharedCheck_2987_ =
                                    (!leanh::lean_is_exclusive(v___x_2977_)) as u8;
                                if v_isSharedCheck_2987_ == 0 {
                                    v___x_2982_ = v___x_2977_;
                                    v_isShared_2983_ = v_isSharedCheck_2987_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2980_);
                                    leanh::lean_dec(v___x_2977_);
                                    v___x_2982_ = leanh::lean_box(0);
                                    v_isShared_2983_ = v_isSharedCheck_2987_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2968_);
                        leanh::lean_dec(v_a_2935_);
                        leanh::lean_dec(v___x_2932_);
                        v_a_2988_ = leanh::lean_ctor_get(v___x_2969_, 0);
                        v_isSharedCheck_2995_ =
                            (!leanh::lean_is_exclusive(v___x_2969_)) as u8;
                        if v_isSharedCheck_2995_ == 0 {
                            v___x_2990_ = v___x_2969_;
                            v_isShared_2991_ = v_isSharedCheck_2995_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2988_);
                            leanh::lean_dec(v___x_2969_);
                            v___x_2990_ = leanh::lean_box(0);
                            v_isShared_2991_ = v_isSharedCheck_2995_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_2943_) == 0 {
                    v_a_2944_ = leanh::lean_ctor_get(v___y_2943_, 0);
                    v_isSharedCheck_2956_ = (!leanh::lean_is_exclusive(v___y_2943_)) as u8;
                    if v_isSharedCheck_2956_ == 0 {
                        v___x_2946_ = v___y_2943_;
                        v_isShared_2947_ = v_isSharedCheck_2956_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2944_);
                        leanh::lean_dec(v___y_2943_);
                        v___x_2946_ = leanh::lean_box(0);
                        v_isShared_2947_ = v_isSharedCheck_2956_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2935_);
                    leanh::lean_dec(v___x_2932_);
                    v_a_2957_ = leanh::lean_ctor_get(v___y_2943_, 0);
                    v_isSharedCheck_2964_ = (!leanh::lean_is_exclusive(v___y_2943_)) as u8;
                    if v_isSharedCheck_2964_ == 0 {
                        v___x_2959_ = v___y_2943_;
                        v_isShared_2960_ = v_isSharedCheck_2964_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2957_);
                        leanh::lean_dec(v___y_2943_);
                        v___x_2959_ = leanh::lean_box(0);
                        v_isShared_2960_ = v_isSharedCheck_2964_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_2944_) == 0 {
                    leanh::lean_dec(v_a_2935_);
                    leanh::lean_dec(v___x_2932_);
                    v_a_2948_ = leanh::lean_ctor_get(v_a_2944_, 0);
                    leanh::lean_inc(v_a_2948_);
                    leanh::lean_dec_ref_known(v_a_2944_, 1);
                    if v_isShared_2947_ == 0 {
                        leanh::lean_ctor_set(v___x_2946_, 0, v_a_2948_);
                        v___x_2950_ = v___x_2946_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2951_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2948_);
                        v___x_2950_ = v_reuseFailAlloc_2951_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2946_);
                    v_a_2952_ = leanh::lean_ctor_get(v_a_2944_, 0);
                    leanh::lean_inc(v_a_2952_);
                    leanh::lean_dec_ref_known(v_a_2944_, 1);
                    v___x_2953_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2954_ = lean_nat_add(v_a_2935_, v___x_2953_);
                    leanh::lean_dec(v_a_2935_);
                    v_a_2935_ = v___x_2954_;
                    v_b_2936_ = v_a_2952_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_2950_;
            }
            4 => {
                if v_isShared_2960_ == 0 {
                    v___x_2962_ = v___x_2959_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
                    v___x_2962_ = v_reuseFailAlloc_2963_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2962_;
            }
            6 => {
                if v_isShared_2983_ == 0 {
                    v___x_2985_ = v___x_2982_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2986_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
                    v___x_2985_ = v_reuseFailAlloc_2986_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2985_;
            }
            8 => {
                if v_isShared_2991_ == 0 {
                    v___x_2993_ = v___x_2990_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2994_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
                    v___x_2993_ = v_reuseFailAlloc_2994_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___boxed(
    mut v_upperBound_2996_: *mut leanh::LeanObject,
    mut v_params_2997_: *mut leanh::LeanObject,
    mut v___x_2998_: *mut leanh::LeanObject,
    mut v_args_2999_: *mut leanh::LeanObject,
    mut v_baseName_3000_: *mut leanh::LeanObject,
    mut v_a_3001_: *mut leanh::LeanObject,
    mut v_b_3002_: *mut leanh::LeanObject,
    mut v___y_3003_: *mut leanh::LeanObject,
    mut v___y_3004_: *mut leanh::LeanObject,
    mut v___y_3005_: *mut leanh::LeanObject,
    mut v___y_3006_: *mut leanh::LeanObject,
    mut v___y_3007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3008_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg(v_upperBound_2996_, v_params_2997_, v___x_2998_, v_args_2999_, v_baseName_3000_, v_a_3001_, v_b_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
    leanh::lean_dec(v___y_3006_);
    leanh::lean_dec_ref(v___y_3005_);
    leanh::lean_dec(v___y_3004_);
    leanh::lean_dec_ref(v___y_3003_);
    leanh::lean_dec(v_baseName_3000_);
    leanh::lean_dec_ref(v_args_2999_);
    leanh::lean_dec_ref(v_params_2997_);
    leanh::lean_dec(v_upperBound_2996_);
    return v_res_3008_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___lam__0(
    mut v___x_3009_: *mut leanh::LeanObject,
    mut v_args_3010_: *mut leanh::LeanObject,
    mut v_baseName_3011_: *mut leanh::LeanObject,
    mut v_params_3012_: *mut leanh::LeanObject,
    mut v_x_3013_: *mut leanh::LeanObject,
    mut v___y_3014_: *mut leanh::LeanObject,
    mut v___y_3015_: *mut leanh::LeanObject,
    mut v___y_3016_: *mut leanh::LeanObject,
    mut v___y_3017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v_fst_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3034_: u8 = 0;
    let mut v_a_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3038_: u8 = 0;
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3019_ = lean_array_get_size(v_params_3012_);
                v___x_3020_ = leanh::lean_unsigned_to_nat(0);
                v___x_3021_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___closed__0;
                v___x_3022_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg(v___x_3019_, v_params_3012_, v___x_3009_, v_args_3010_, v_baseName_3011_, v___x_3020_, v___x_3021_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
                if leanh::lean_obj_tag(v___x_3022_) == 0 {
                    v_a_3023_ = leanh::lean_ctor_get(v___x_3022_, 0);
                    v_isSharedCheck_3034_ = (!leanh::lean_is_exclusive(v___x_3022_)) as u8;
                    if v_isSharedCheck_3034_ == 0 {
                        v___x_3025_ = v___x_3022_;
                        v_isShared_3026_ = v_isSharedCheck_3034_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3023_);
                        leanh::lean_dec(v___x_3022_);
                        v___x_3025_ = leanh::lean_box(0);
                        v_isShared_3026_ = v_isSharedCheck_3034_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3035_ = leanh::lean_ctor_get(v___x_3022_, 0);
                    v_isSharedCheck_3042_ = (!leanh::lean_is_exclusive(v___x_3022_)) as u8;
                    if v_isSharedCheck_3042_ == 0 {
                        v___x_3037_ = v___x_3022_;
                        v_isShared_3038_ = v_isSharedCheck_3042_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3035_);
                        leanh::lean_dec(v___x_3022_);
                        v___x_3037_ = leanh::lean_box(0);
                        v_isShared_3038_ = v_isSharedCheck_3042_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3027_ = leanh::lean_ctor_get(v_a_3023_, 0);
                leanh::lean_inc(v_fst_3027_);
                leanh::lean_dec(v_a_3023_);
                if leanh::lean_obj_tag(v_fst_3027_) == 0 {
                    leanh::lean_del_object(v___x_3025_);
                    v___x_3028_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1);
                    v___x_3029_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v___x_3028_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
                    return v___x_3029_;
                } else {
                    v_val_3030_ = leanh::lean_ctor_get(v_fst_3027_, 0);
                    leanh::lean_inc(v_val_3030_);
                    leanh::lean_dec_ref_known(v_fst_3027_, 1);
                    if v_isShared_3026_ == 0 {
                        leanh::lean_ctor_set(v___x_3025_, 0, v_val_3030_);
                        v___x_3032_ = v___x_3025_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3033_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_val_3030_);
                        v___x_3032_ = v_reuseFailAlloc_3033_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3032_;
            }
            3 => {
                if v_isShared_3038_ == 0 {
                    v___x_3040_ = v___x_3037_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3041_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
                    v___x_3040_ = v_reuseFailAlloc_3041_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___lam__0___boxed(
    mut v___x_3043_: *mut leanh::LeanObject,
    mut v_args_3044_: *mut leanh::LeanObject,
    mut v_baseName_3045_: *mut leanh::LeanObject,
    mut v_params_3046_: *mut leanh::LeanObject,
    mut v_x_3047_: *mut leanh::LeanObject,
    mut v___y_3048_: *mut leanh::LeanObject,
    mut v___y_3049_: *mut leanh::LeanObject,
    mut v___y_3050_: *mut leanh::LeanObject,
    mut v___y_3051_: *mut leanh::LeanObject,
    mut v___y_3052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3053_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___lam__0(v___x_3043_, v_args_3044_, v_baseName_3045_, v_params_3046_, v_x_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
    leanh::lean_dec(v___y_3051_);
    leanh::lean_dec_ref(v___y_3050_);
    leanh::lean_dec(v___y_3049_);
    leanh::lean_dec_ref(v___y_3048_);
    leanh::lean_dec_ref(v_x_3047_);
    leanh::lean_dec_ref(v_params_3046_);
    leanh::lean_dec(v_baseName_3045_);
    leanh::lean_dec_ref(v_args_3044_);
    return v_res_3053_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3054_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3054_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3055_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__0);
    v___x_3056_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3056_, 0, v___x_3055_);
    return v___x_3056_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3057_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
    v___x_3058_ = leanh::lean_unsigned_to_nat(0);
    v___x_3059_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3059_, 0, v___x_3058_);
    leanh::lean_ctor_set(v___x_3059_, 1, v___x_3058_);
    leanh::lean_ctor_set(v___x_3059_, 2, v___x_3058_);
    leanh::lean_ctor_set(v___x_3059_, 3, v___x_3058_);
    leanh::lean_ctor_set(v___x_3059_, 4, v___x_3057_);
    leanh::lean_ctor_set(v___x_3059_, 5, v___x_3057_);
    leanh::lean_ctor_set(v___x_3059_, 6, v___x_3057_);
    leanh::lean_ctor_set(v___x_3059_, 7, v___x_3057_);
    leanh::lean_ctor_set(v___x_3059_, 8, v___x_3057_);
    leanh::lean_ctor_set(v___x_3059_, 9, v___x_3057_);
    return v___x_3059_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3060_ = leanh::lean_unsigned_to_nat(32);
    v___x_3061_ = lean_mk_empty_array_with_capacity(v___x_3060_);
    v___x_3062_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3062_, 0, v___x_3061_);
    return v___x_3062_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3063_: usize = 0;
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3063_ = 5usize;
    v___x_3064_ = leanh::lean_unsigned_to_nat(0);
    v___x_3065_ = leanh::lean_unsigned_to_nat(32);
    v___x_3066_ = lean_mk_empty_array_with_capacity(v___x_3065_);
    v___x_3067_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__3);
    v___x_3068_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3068_, 0, v___x_3067_);
    leanh::lean_ctor_set(v___x_3068_, 1, v___x_3066_);
    leanh::lean_ctor_set(v___x_3068_, 2, v___x_3064_);
    leanh::lean_ctor_set(v___x_3068_, 3, v___x_3064_);
    leanh::lean_ctor_set_usize(v___x_3068_, 4, v___x_3063_);
    return v___x_3068_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3069_ = leanh::lean_box(1);
    v___x_3070_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__4);
    v___x_3071_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__1);
    v___x_3072_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3072_, 0, v___x_3071_);
    leanh::lean_ctor_set(v___x_3072_, 1, v___x_3070_);
    leanh::lean_ctor_set(v___x_3072_, 2, v___x_3069_);
    return v___x_3072_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3074_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__6;
    v___x_3075_ = l_Lean_stringToMessageData(v___x_3074_);
    return v___x_3075_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3077_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__8;
    v___x_3078_ = l_Lean_stringToMessageData(v___x_3077_);
    return v___x_3078_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3080_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__10;
    v___x_3081_ = l_Lean_stringToMessageData(v___x_3080_);
    return v___x_3081_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3083_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__12;
    v___x_3084_ = l_Lean_stringToMessageData(v___x_3083_);
    return v___x_3084_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3086_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__14;
    v___x_3087_ = l_Lean_stringToMessageData(v___x_3086_);
    return v___x_3087_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3089_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__16;
    v___x_3090_ = l_Lean_stringToMessageData(v___x_3089_);
    return v___x_3090_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3092_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__18;
    v___x_3093_ = l_Lean_stringToMessageData(v___x_3092_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg(
    mut v_msg_3094_: *mut leanh::LeanObject,
    mut v_declHint_3095_: *mut leanh::LeanObject,
    mut v___y_3096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: u8 = 0;
    let mut v_isExporting_3101_: u8 = 0;
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: u8 = 0;
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: u8 = 0;
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3155_: u8 = 0;
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3098_ = lean_st_ref_get(v___y_3096_);
                v_env_3099_ = leanh::lean_ctor_get(v___x_3098_, 0);
                leanh::lean_inc_ref(v_env_3099_);
                leanh::lean_dec(v___x_3098_);
                v___x_3100_ = l_Lean_Name_isAnonymous(v_declHint_3095_);
                if v___x_3100_ == 0 {
                    v_isExporting_3101_ = leanh::lean_ctor_get_uint8(
                        v_env_3099_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3101_ == 0 {
                        leanh::lean_dec_ref(v_env_3099_);
                        leanh::lean_dec(v_declHint_3095_);
                        v___x_3102_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3102_, 0, v_msg_3094_);
                        return v___x_3102_;
                    } else {
                        leanh::lean_inc_ref(v_env_3099_);
                        v___x_3103_ = l_Lean_Environment_setExporting(v_env_3099_, v___x_3100_);
                        leanh::lean_inc(v_declHint_3095_);
                        leanh::lean_inc_ref(v___x_3103_);
                        v___x_3104_ = l_Lean_Environment_contains(
                            v___x_3103_,
                            v_declHint_3095_,
                            v_isExporting_3101_,
                        );
                        if v___x_3104_ == 0 {
                            leanh::lean_dec_ref(v___x_3103_);
                            leanh::lean_dec_ref(v_env_3099_);
                            leanh::lean_dec(v_declHint_3095_);
                            v___x_3105_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3105_, 0, v_msg_3094_);
                            return v___x_3105_;
                        } else {
                            v___x_3106_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__2);
                            v___x_3107_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__5);
                            v___x_3108_ = l_Lean_Options_empty;
                            v___x_3109_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3109_, 0, v___x_3103_);
                            leanh::lean_ctor_set(v___x_3109_, 1, v___x_3106_);
                            leanh::lean_ctor_set(v___x_3109_, 2, v___x_3107_);
                            leanh::lean_ctor_set(v___x_3109_, 3, v___x_3108_);
                            leanh::lean_inc(v_declHint_3095_);
                            v___x_3110_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3095_, v___x_3100_);
                            v_c_3111_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3111_, 0, v___x_3109_);
                            leanh::lean_ctor_set(v_c_3111_, 1, v___x_3110_);
                            v___x_3112_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3099_,
                                v_declHint_3095_,
                            );
                            if leanh::lean_obj_tag(v___x_3112_) == 0 {
                                leanh::lean_dec_ref(v_env_3099_);
                                leanh::lean_dec(v_declHint_3095_);
                                v___x_3113_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
                                v___x_3114_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3114_, 0, v___x_3113_);
                                leanh::lean_ctor_set(v___x_3114_, 1, v_c_3111_);
                                v___x_3115_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__9);
                                v___x_3116_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3116_, 0, v___x_3114_);
                                leanh::lean_ctor_set(v___x_3116_, 1, v___x_3115_);
                                v___x_3117_ = l_Lean_MessageData_note(v___x_3116_);
                                v___x_3118_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3118_, 0, v_msg_3094_);
                                leanh::lean_ctor_set(v___x_3118_, 1, v___x_3117_);
                                v___x_3119_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3119_, 0, v___x_3118_);
                                return v___x_3119_;
                            } else {
                                v_val_3120_ = leanh::lean_ctor_get(v___x_3112_, 0);
                                v_isSharedCheck_3155_ =
                                    (!leanh::lean_is_exclusive(v___x_3112_)) as u8;
                                if v_isSharedCheck_3155_ == 0 {
                                    v___x_3122_ = v___x_3112_;
                                    v_isShared_3123_ = v_isSharedCheck_3155_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3120_);
                                    leanh::lean_dec(v___x_3112_);
                                    v___x_3122_ = leanh::lean_box(0);
                                    v_isShared_3123_ = v_isSharedCheck_3155_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3099_);
                    leanh::lean_dec(v_declHint_3095_);
                    v___x_3156_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3156_, 0, v_msg_3094_);
                    return v___x_3156_;
                }
            }
            1 => {
                v___x_3124_ = leanh::lean_box(0);
                v___x_3125_ = l_Lean_Environment_header(v_env_3099_);
                leanh::lean_dec_ref(v_env_3099_);
                v___x_3126_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3125_);
                v_mod_3127_ = lean_array_get(v___x_3124_, v___x_3126_, v_val_3120_);
                leanh::lean_dec(v_val_3120_);
                leanh::lean_dec_ref(v___x_3126_);
                v___x_3128_ = l_Lean_isPrivateName(v_declHint_3095_);
                leanh::lean_dec(v_declHint_3095_);
                if v___x_3128_ == 0 {
                    v___x_3129_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__11);
                    v___x_3130_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3130_, 0, v___x_3129_);
                    leanh::lean_ctor_set(v___x_3130_, 1, v_c_3111_);
                    v___x_3131_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__13);
                    v___x_3132_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3132_, 0, v___x_3130_);
                    leanh::lean_ctor_set(v___x_3132_, 1, v___x_3131_);
                    v___x_3133_ = l_Lean_MessageData_ofName(v_mod_3127_);
                    v___x_3134_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3134_, 0, v___x_3132_);
                    leanh::lean_ctor_set(v___x_3134_, 1, v___x_3133_);
                    v___x_3135_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__15);
                    v___x_3136_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3136_, 0, v___x_3134_);
                    leanh::lean_ctor_set(v___x_3136_, 1, v___x_3135_);
                    v___x_3137_ = l_Lean_MessageData_note(v___x_3136_);
                    v___x_3138_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3138_, 0, v_msg_3094_);
                    leanh::lean_ctor_set(v___x_3138_, 1, v___x_3137_);
                    if v_isShared_3123_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3122_, 0);
                        leanh::lean_ctor_set(v___x_3122_, 0, v___x_3138_);
                        v___x_3140_ = v___x_3122_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3141_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3138_);
                        v___x_3140_ = v_reuseFailAlloc_3141_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3142_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__7);
                    v___x_3143_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3143_, 0, v___x_3142_);
                    leanh::lean_ctor_set(v___x_3143_, 1, v_c_3111_);
                    v___x_3144_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__17);
                    v___x_3145_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3145_, 0, v___x_3143_);
                    leanh::lean_ctor_set(v___x_3145_, 1, v___x_3144_);
                    v___x_3146_ = l_Lean_MessageData_ofName(v_mod_3127_);
                    v___x_3147_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3147_, 0, v___x_3145_);
                    leanh::lean_ctor_set(v___x_3147_, 1, v___x_3146_);
                    v___x_3148_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___closed__19);
                    v___x_3149_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3149_, 0, v___x_3147_);
                    leanh::lean_ctor_set(v___x_3149_, 1, v___x_3148_);
                    v___x_3150_ = l_Lean_MessageData_note(v___x_3149_);
                    v___x_3151_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3151_, 0, v_msg_3094_);
                    leanh::lean_ctor_set(v___x_3151_, 1, v___x_3150_);
                    if v_isShared_3123_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3122_, 0);
                        leanh::lean_ctor_set(v___x_3122_, 0, v___x_3151_);
                        v___x_3153_ = v___x_3122_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3154_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
                        v___x_3153_ = v_reuseFailAlloc_3154_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3140_;
            }
            3 => {
                return v___x_3153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg___boxed(
    mut v_msg_3157_: *mut leanh::LeanObject,
    mut v_declHint_3158_: *mut leanh::LeanObject,
    mut v___y_3159_: *mut leanh::LeanObject,
    mut v___y_3160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3161_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3157_, v_declHint_3158_, v___y_3159_);
    leanh::lean_dec(v___y_3159_);
    return v_res_3161_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6(
    mut v_msg_3162_: *mut leanh::LeanObject,
    mut v_declHint_3163_: *mut leanh::LeanObject,
    mut v___y_3164_: *mut leanh::LeanObject,
    mut v___y_3165_: *mut leanh::LeanObject,
    mut v___y_3166_: *mut leanh::LeanObject,
    mut v___y_3167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3169_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3162_, v_declHint_3163_, v___y_3167_);
                v_a_3170_ = leanh::lean_ctor_get(v___x_3169_, 0);
                v_isSharedCheck_3179_ = (!leanh::lean_is_exclusive(v___x_3169_)) as u8;
                if v_isSharedCheck_3179_ == 0 {
                    v___x_3172_ = v___x_3169_;
                    v_isShared_3173_ = v_isSharedCheck_3179_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3170_);
                    leanh::lean_dec(v___x_3169_);
                    v___x_3172_ = leanh::lean_box(0);
                    v_isShared_3173_ = v_isSharedCheck_3179_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3174_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3175_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3175_, 0, v___x_3174_);
                leanh::lean_ctor_set(v___x_3175_, 1, v_a_3170_);
                if v_isShared_3173_ == 0 {
                    leanh::lean_ctor_set(v___x_3172_, 0, v___x_3175_);
                    v___x_3177_ = v___x_3172_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3175_);
                    v___x_3177_ = v_reuseFailAlloc_3178_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3177_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6___boxed(
    mut v_msg_3180_: *mut leanh::LeanObject,
    mut v_declHint_3181_: *mut leanh::LeanObject,
    mut v___y_3182_: *mut leanh::LeanObject,
    mut v___y_3183_: *mut leanh::LeanObject,
    mut v___y_3184_: *mut leanh::LeanObject,
    mut v___y_3185_: *mut leanh::LeanObject,
    mut v___y_3186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3187_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6(v_msg_3180_, v_declHint_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
    leanh::lean_dec(v___y_3185_);
    leanh::lean_dec_ref(v___y_3184_);
    leanh::lean_dec(v___y_3183_);
    leanh::lean_dec_ref(v___y_3182_);
    return v_res_3187_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__7___redArg(
    mut v_ref_3188_: *mut leanh::LeanObject,
    mut v_msg_3189_: *mut leanh::LeanObject,
    mut v___y_3190_: *mut leanh::LeanObject,
    mut v___y_3191_: *mut leanh::LeanObject,
    mut v___y_3192_: *mut leanh::LeanObject,
    mut v___y_3193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3207_: u8 = 0;
    let mut v_cancelTk_x3f_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3209_: u8 = 0;
    let mut v_inheritedTraceOptions_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3195_ = leanh::lean_ctor_get(v___y_3192_, 0);
    v_fileMap_3196_ = leanh::lean_ctor_get(v___y_3192_, 1);
    v_options_3197_ = leanh::lean_ctor_get(v___y_3192_, 2);
    v_currRecDepth_3198_ = leanh::lean_ctor_get(v___y_3192_, 3);
    v_maxRecDepth_3199_ = leanh::lean_ctor_get(v___y_3192_, 4);
    v_ref_3200_ = leanh::lean_ctor_get(v___y_3192_, 5);
    v_currNamespace_3201_ = leanh::lean_ctor_get(v___y_3192_, 6);
    v_openDecls_3202_ = leanh::lean_ctor_get(v___y_3192_, 7);
    v_initHeartbeats_3203_ = leanh::lean_ctor_get(v___y_3192_, 8);
    v_maxHeartbeats_3204_ = leanh::lean_ctor_get(v___y_3192_, 9);
    v_quotContext_3205_ = leanh::lean_ctor_get(v___y_3192_, 10);
    v_currMacroScope_3206_ = leanh::lean_ctor_get(v___y_3192_, 11);
    v_diag_3207_ = leanh::lean_ctor_get_uint8(
        v___y_3192_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3208_ = leanh::lean_ctor_get(v___y_3192_, 12);
    v_suppressElabErrors_3209_ = leanh::lean_ctor_get_uint8(
        v___y_3192_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3210_ = leanh::lean_ctor_get(v___y_3192_, 13);
    v_ref_3211_ = l_Lean_replaceRef(v_ref_3188_, v_ref_3200_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3210_);
    leanh::lean_inc(v_cancelTk_x3f_3208_);
    leanh::lean_inc(v_currMacroScope_3206_);
    leanh::lean_inc(v_quotContext_3205_);
    leanh::lean_inc(v_maxHeartbeats_3204_);
    leanh::lean_inc(v_initHeartbeats_3203_);
    leanh::lean_inc(v_openDecls_3202_);
    leanh::lean_inc(v_currNamespace_3201_);
    leanh::lean_inc(v_maxRecDepth_3199_);
    leanh::lean_inc(v_currRecDepth_3198_);
    leanh::lean_inc_ref(v_options_3197_);
    leanh::lean_inc_ref(v_fileMap_3196_);
    leanh::lean_inc_ref(v_fileName_3195_);
    v___x_3212_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3212_, 0, v_fileName_3195_);
    leanh::lean_ctor_set(v___x_3212_, 1, v_fileMap_3196_);
    leanh::lean_ctor_set(v___x_3212_, 2, v_options_3197_);
    leanh::lean_ctor_set(v___x_3212_, 3, v_currRecDepth_3198_);
    leanh::lean_ctor_set(v___x_3212_, 4, v_maxRecDepth_3199_);
    leanh::lean_ctor_set(v___x_3212_, 5, v_ref_3211_);
    leanh::lean_ctor_set(v___x_3212_, 6, v_currNamespace_3201_);
    leanh::lean_ctor_set(v___x_3212_, 7, v_openDecls_3202_);
    leanh::lean_ctor_set(v___x_3212_, 8, v_initHeartbeats_3203_);
    leanh::lean_ctor_set(v___x_3212_, 9, v_maxHeartbeats_3204_);
    leanh::lean_ctor_set(v___x_3212_, 10, v_quotContext_3205_);
    leanh::lean_ctor_set(v___x_3212_, 11, v_currMacroScope_3206_);
    leanh::lean_ctor_set(v___x_3212_, 12, v_cancelTk_x3f_3208_);
    leanh::lean_ctor_set(v___x_3212_, 13, v_inheritedTraceOptions_3210_);
    leanh::lean_ctor_set_uint8(
        v___x_3212_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3207_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3212_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3209_,
    );
    v___x_3213_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v_msg_3189_, v___y_3190_, v___y_3191_, v___x_3212_, v___y_3193_);
    leanh::lean_dec_ref_known(v___x_3212_, 14);
    return v___x_3213_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__7___redArg___boxed(
    mut v_ref_3214_: *mut leanh::LeanObject,
    mut v_msg_3215_: *mut leanh::LeanObject,
    mut v___y_3216_: *mut leanh::LeanObject,
    mut v___y_3217_: *mut leanh::LeanObject,
    mut v___y_3218_: *mut leanh::LeanObject,
    mut v___y_3219_: *mut leanh::LeanObject,
    mut v___y_3220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3221_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__7___redArg(v_ref_3214_, v_msg_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
    leanh::lean_dec(v___y_3219_);
    leanh::lean_dec_ref(v___y_3218_);
    leanh::lean_dec(v___y_3217_);
    leanh::lean_dec_ref(v___y_3216_);
    leanh::lean_dec(v_ref_3214_);
    return v_res_3221_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5___redArg(
    mut v_ref_3222_: *mut leanh::LeanObject,
    mut v_msg_3223_: *mut leanh::LeanObject,
    mut v_declHint_3224_: *mut leanh::LeanObject,
    mut v___y_3225_: *mut leanh::LeanObject,
    mut v___y_3226_: *mut leanh::LeanObject,
    mut v___y_3227_: *mut leanh::LeanObject,
    mut v___y_3228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3230_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6(v_msg_3223_, v_declHint_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
    v_a_3231_ = leanh::lean_ctor_get(v___x_3230_, 0);
    leanh::lean_inc(v_a_3231_);
    leanh::lean_dec_ref(v___x_3230_);
    v___x_3232_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__7___redArg(v_ref_3222_, v_a_3231_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
    return v___x_3232_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5___redArg___boxed(
    mut v_ref_3233_: *mut leanh::LeanObject,
    mut v_msg_3234_: *mut leanh::LeanObject,
    mut v_declHint_3235_: *mut leanh::LeanObject,
    mut v___y_3236_: *mut leanh::LeanObject,
    mut v___y_3237_: *mut leanh::LeanObject,
    mut v___y_3238_: *mut leanh::LeanObject,
    mut v___y_3239_: *mut leanh::LeanObject,
    mut v___y_3240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3241_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5___redArg(v_ref_3233_, v_msg_3234_, v_declHint_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
    leanh::lean_dec(v___y_3239_);
    leanh::lean_dec_ref(v___y_3238_);
    leanh::lean_dec(v___y_3237_);
    leanh::lean_dec_ref(v___y_3236_);
    leanh::lean_dec(v_ref_3233_);
    return v_res_3241_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3243_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg___closed__0;
    v___x_3244_ = l_Lean_stringToMessageData(v___x_3243_);
    return v___x_3244_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg(
    mut v_ref_3245_: *mut leanh::LeanObject,
    mut v_constName_3246_: *mut leanh::LeanObject,
    mut v___y_3247_: *mut leanh::LeanObject,
    mut v___y_3248_: *mut leanh::LeanObject,
    mut v___y_3249_: *mut leanh::LeanObject,
    mut v___y_3250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: u8 = 0;
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3252_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg___closed__1);
    v___x_3253_ = 0;
    leanh::lean_inc(v_constName_3246_);
    v___x_3254_ = l_Lean_MessageData_ofConstName(v_constName_3246_, v___x_3253_);
    v___x_3255_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3255_, 0, v___x_3252_);
    leanh::lean_ctor_set(v___x_3255_, 1, v___x_3254_);
    v___x_3256_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0___closed__1);
    v___x_3257_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3257_, 0, v___x_3255_);
    leanh::lean_ctor_set(v___x_3257_, 1, v___x_3256_);
    v___x_3258_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5___redArg(v_ref_3245_, v___x_3257_, v_constName_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
    return v___x_3258_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_ref_3259_: *mut leanh::LeanObject,
    mut v_constName_3260_: *mut leanh::LeanObject,
    mut v___y_3261_: *mut leanh::LeanObject,
    mut v___y_3262_: *mut leanh::LeanObject,
    mut v___y_3263_: *mut leanh::LeanObject,
    mut v___y_3264_: *mut leanh::LeanObject,
    mut v___y_3265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3266_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg(v_ref_3259_, v_constName_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
    leanh::lean_dec(v___y_3264_);
    leanh::lean_dec_ref(v___y_3263_);
    leanh::lean_dec(v___y_3262_);
    leanh::lean_dec_ref(v___y_3261_);
    leanh::lean_dec(v_ref_3259_);
    return v_res_3266_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2___redArg(
    mut v_constName_3267_: *mut leanh::LeanObject,
    mut v___y_3268_: *mut leanh::LeanObject,
    mut v___y_3269_: *mut leanh::LeanObject,
    mut v___y_3270_: *mut leanh::LeanObject,
    mut v___y_3271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_3273_ = leanh::lean_ctor_get(v___y_3270_, 5);
    v___x_3274_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg(v_ref_3273_, v_constName_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
    return v___x_3274_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2___redArg___boxed(
    mut v_constName_3275_: *mut leanh::LeanObject,
    mut v___y_3276_: *mut leanh::LeanObject,
    mut v___y_3277_: *mut leanh::LeanObject,
    mut v___y_3278_: *mut leanh::LeanObject,
    mut v___y_3279_: *mut leanh::LeanObject,
    mut v___y_3280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3281_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2___redArg(v_constName_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
    leanh::lean_dec(v___y_3279_);
    leanh::lean_dec_ref(v___y_3278_);
    leanh::lean_dec(v___y_3277_);
    leanh::lean_dec_ref(v___y_3276_);
    return v_res_3281_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2(
    mut v_constName_3282_: *mut leanh::LeanObject,
    mut v___y_3283_: *mut leanh::LeanObject,
    mut v___y_3284_: *mut leanh::LeanObject,
    mut v___y_3285_: *mut leanh::LeanObject,
    mut v___y_3286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3296_: u8 = 0;
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3288_ = lean_st_ref_get(v___y_3286_);
                v_env_3289_ = leanh::lean_ctor_get(v___x_3288_, 0);
                leanh::lean_inc_ref(v_env_3289_);
                leanh::lean_dec(v___x_3288_);
                v___x_3290_ = 0;
                leanh::lean_inc(v_constName_3282_);
                v___x_3291_ =
                    l_Lean_Environment_find_x3f(v_env_3289_, v_constName_3282_, v___x_3290_);
                if leanh::lean_obj_tag(v___x_3291_) == 0 {
                    v___x_3292_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2___redArg(v_constName_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
                    return v___x_3292_;
                } else {
                    leanh::lean_dec(v_constName_3282_);
                    v_val_3293_ = leanh::lean_ctor_get(v___x_3291_, 0);
                    v_isSharedCheck_3300_ = (!leanh::lean_is_exclusive(v___x_3291_)) as u8;
                    if v_isSharedCheck_3300_ == 0 {
                        v___x_3295_ = v___x_3291_;
                        v_isShared_3296_ = v_isSharedCheck_3300_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3293_);
                        leanh::lean_dec(v___x_3291_);
                        v___x_3295_ = leanh::lean_box(0);
                        v_isShared_3296_ = v_isSharedCheck_3300_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3296_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3295_, 0);
                    v___x_3298_ = v___x_3295_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3299_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_val_3293_);
                    v___x_3298_ = v_reuseFailAlloc_3299_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2___boxed(
    mut v_constName_3301_: *mut leanh::LeanObject,
    mut v___y_3302_: *mut leanh::LeanObject,
    mut v___y_3303_: *mut leanh::LeanObject,
    mut v___y_3304_: *mut leanh::LeanObject,
    mut v___y_3305_: *mut leanh::LeanObject,
    mut v___y_3306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2(v_constName_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
    leanh::lean_dec(v___y_3305_);
    leanh::lean_dec_ref(v___y_3304_);
    leanh::lean_dec(v___y_3303_);
    leanh::lean_dec_ref(v___y_3302_);
    return v_res_3307_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo(
    mut v_c_3311_: *mut leanh::LeanObject,
    mut v_args_3312_: *mut leanh::LeanObject,
    mut v_a_3313_: *mut leanh::LeanObject,
    mut v_a_3314_: *mut leanh::LeanObject,
    mut v_a_3315_: *mut leanh::LeanObject,
    mut v_a_3316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: u8 = 0;
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3330_: u8 = 0;
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3334_: u8 = 0;
    let mut v_pre_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3349_: u8 = 0;
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3353_: u8 = 0;
    let mut v___x_3354_: u8 = 0;
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3360_: u8 = 0;
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_c_3311_) == 1 {
                    v_pre_3335_ = leanh::lean_ctor_get(v_c_3311_, 0);
                    v_str_3336_ = leanh::lean_ctor_get(v_c_3311_, 1);
                    leanh::lean_inc(v_pre_3335_);
                    v_baseName_3337_ = l_Lean_privateToUserName(v_pre_3335_);
                    v___x_3354_ = l_Lean_Name_isAnonymous(v_baseName_3337_);
                    if v___x_3354_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_baseName_3337_);
                        leanh::lean_dec_ref_known(v_c_3311_, 2);
                        leanh::lean_dec_ref(v_args_3312_);
                        v___x_3355_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1);
                        v___x_3356_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v___x_3355_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
                        v_a_3357_ = leanh::lean_ctor_get(v___x_3356_, 0);
                        v_isSharedCheck_3364_ =
                            (!leanh::lean_is_exclusive(v___x_3356_)) as u8;
                        if v_isSharedCheck_3364_ == 0 {
                            v___x_3359_ = v___x_3356_;
                            v_isShared_3360_ = v_isSharedCheck_3364_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3357_);
                            leanh::lean_dec(v___x_3356_);
                            v___x_3359_ = leanh::lean_box(0);
                            v_isShared_3360_ = v_isSharedCheck_3364_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_args_3312_);
                    leanh::lean_dec(v_c_3311_);
                    v___x_3365_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1);
                    v___x_3366_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v___x_3365_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
                    return v___x_3366_;
                }
            }
            1 => {
                v___x_3320_ = l_Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2(v_c_3311_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
                if leanh::lean_obj_tag(v___x_3320_) == 0 {
                    v_a_3321_ = leanh::lean_ctor_get(v___x_3320_, 0);
                    leanh::lean_inc(v_a_3321_);
                    leanh::lean_dec_ref_known(v___x_3320_, 1);
                    v___x_3322_ = l_Lean_ConstantInfo_type(v_a_3321_);
                    leanh::lean_dec(v_a_3321_);
                    v___x_3323_ = lean_array_get_size(v_args_3312_);
                    leanh::lean_dec_ref(v_args_3312_);
                    v___x_3324_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3324_, 0, v___x_3323_);
                    v___x_3325_ = 0;
                    v___x_3326_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__3___redArg(v___x_3322_, v___x_3324_, v___y_3319_, v___x_3325_, v___x_3325_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
                    return v___x_3326_;
                } else {
                    leanh::lean_dec_ref(v___y_3319_);
                    leanh::lean_dec_ref(v_args_3312_);
                    v_a_3327_ = leanh::lean_ctor_get(v___x_3320_, 0);
                    v_isSharedCheck_3334_ = (!leanh::lean_is_exclusive(v___x_3320_)) as u8;
                    if v_isSharedCheck_3334_ == 0 {
                        v___x_3329_ = v___x_3320_;
                        v_isShared_3330_ = v_isSharedCheck_3334_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3327_);
                        leanh::lean_dec(v___x_3320_);
                        v___x_3329_ = leanh::lean_box(0);
                        v_isShared_3330_ = v_isSharedCheck_3334_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3330_ == 0 {
                    v___x_3332_ = v___x_3329_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3333_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
                    v___x_3332_ = v_reuseFailAlloc_3333_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3332_;
            }
            4 => {
                v___x_3339_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_str_3336_);
                v___x_3340_ = l_Lean_Name_str___override(v___x_3339_, v_str_3336_);
                leanh::lean_inc(v_baseName_3337_);
                leanh::lean_inc_ref(v_args_3312_);
                v___f_3341_ = leanh::lean_alloc_closure(l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                leanh::lean_closure_set(v___f_3341_, 0, v___x_3340_);
                leanh::lean_closure_set(v___f_3341_, 1, v_args_3312_);
                leanh::lean_closure_set(v___f_3341_, 2, v_baseName_3337_);
                v___x_3342_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___closed__1;
                v___x_3343_ = lean_name_eq(v_baseName_3337_, v___x_3342_);
                leanh::lean_dec(v_baseName_3337_);
                if v___x_3343_ == 0 {
                    v___y_3319_ = v___f_3341_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___f_3341_);
                    leanh::lean_dec_ref_known(v_c_3311_, 2);
                    leanh::lean_dec_ref(v_args_3312_);
                    v___x_3344_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1);
                    v___x_3345_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v___x_3344_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
                    v_a_3346_ = leanh::lean_ctor_get(v___x_3345_, 0);
                    v_isSharedCheck_3353_ = (!leanh::lean_is_exclusive(v___x_3345_)) as u8;
                    if v_isSharedCheck_3353_ == 0 {
                        v___x_3348_ = v___x_3345_;
                        v_isShared_3349_ = v_isSharedCheck_3353_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3346_);
                        leanh::lean_dec(v___x_3345_);
                        v___x_3348_ = leanh::lean_box(0);
                        v_isShared_3349_ = v_isSharedCheck_3353_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3349_ == 0 {
                    v___x_3351_ = v___x_3348_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3352_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
                    v___x_3351_ = v_reuseFailAlloc_3352_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3351_;
            }
            7 => {
                if v_isShared_3360_ == 0 {
                    v___x_3362_ = v___x_3359_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3363_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
                    v___x_3362_ = v_reuseFailAlloc_3363_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3362_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo___boxed(
    mut v_c_3367_: *mut leanh::LeanObject,
    mut v_args_3368_: *mut leanh::LeanObject,
    mut v_a_3369_: *mut leanh::LeanObject,
    mut v_a_3370_: *mut leanh::LeanObject,
    mut v_a_3371_: *mut leanh::LeanObject,
    mut v_a_3372_: *mut leanh::LeanObject,
    mut v_a_3373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3374_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo(v_c_3367_, v_args_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_);
    leanh::lean_dec(v_a_3372_);
    leanh::lean_dec_ref(v_a_3371_);
    leanh::lean_dec(v_a_3370_);
    leanh::lean_dec_ref(v_a_3369_);
    return v_res_3374_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1(
    mut v_upperBound_3375_: *mut leanh::LeanObject,
    mut v_params_3376_: *mut leanh::LeanObject,
    mut v___x_3377_: *mut leanh::LeanObject,
    mut v_args_3378_: *mut leanh::LeanObject,
    mut v_baseName_3379_: *mut leanh::LeanObject,
    mut v_inst_3380_: *mut leanh::LeanObject,
    mut v_R_3381_: *mut leanh::LeanObject,
    mut v_a_3382_: *mut leanh::LeanObject,
    mut v_b_3383_: *mut leanh::LeanObject,
    mut v_c_3384_: *mut leanh::LeanObject,
    mut v___y_3385_: *mut leanh::LeanObject,
    mut v___y_3386_: *mut leanh::LeanObject,
    mut v___y_3387_: *mut leanh::LeanObject,
    mut v___y_3388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3390_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg(v_upperBound_3375_, v_params_3376_, v___x_3377_, v_args_3378_, v_baseName_3379_, v_a_3382_, v_b_3383_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
    return v___x_3390_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___boxed(
    mut v_upperBound_3391_: *mut leanh::LeanObject,
    mut v_params_3392_: *mut leanh::LeanObject,
    mut v___x_3393_: *mut leanh::LeanObject,
    mut v_args_3394_: *mut leanh::LeanObject,
    mut v_baseName_3395_: *mut leanh::LeanObject,
    mut v_inst_3396_: *mut leanh::LeanObject,
    mut v_R_3397_: *mut leanh::LeanObject,
    mut v_a_3398_: *mut leanh::LeanObject,
    mut v_b_3399_: *mut leanh::LeanObject,
    mut v_c_3400_: *mut leanh::LeanObject,
    mut v___y_3401_: *mut leanh::LeanObject,
    mut v___y_3402_: *mut leanh::LeanObject,
    mut v___y_3403_: *mut leanh::LeanObject,
    mut v___y_3404_: *mut leanh::LeanObject,
    mut v___y_3405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3406_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1(v_upperBound_3391_, v_params_3392_, v___x_3393_, v_args_3394_, v_baseName_3395_, v_inst_3396_, v_R_3397_, v_a_3398_, v_b_3399_, v_c_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
    leanh::lean_dec(v___y_3404_);
    leanh::lean_dec_ref(v___y_3403_);
    leanh::lean_dec(v___y_3402_);
    leanh::lean_dec_ref(v___y_3401_);
    leanh::lean_dec(v_baseName_3395_);
    leanh::lean_dec_ref(v_args_3394_);
    leanh::lean_dec_ref(v_params_3392_);
    leanh::lean_dec(v_upperBound_3391_);
    return v_res_3406_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2(
    mut v_00_u03b1_3407_: *mut leanh::LeanObject,
    mut v_constName_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
    mut v___y_3410_: *mut leanh::LeanObject,
    mut v___y_3411_: *mut leanh::LeanObject,
    mut v___y_3412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2___redArg(v_constName_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
    return v___x_3414_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2___boxed(
    mut v_00_u03b1_3415_: *mut leanh::LeanObject,
    mut v_constName_3416_: *mut leanh::LeanObject,
    mut v___y_3417_: *mut leanh::LeanObject,
    mut v___y_3418_: *mut leanh::LeanObject,
    mut v___y_3419_: *mut leanh::LeanObject,
    mut v___y_3420_: *mut leanh::LeanObject,
    mut v___y_3421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3422_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2(v_00_u03b1_3415_, v_constName_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
    leanh::lean_dec(v___y_3420_);
    leanh::lean_dec_ref(v___y_3419_);
    leanh::lean_dec(v___y_3418_);
    leanh::lean_dec_ref(v___y_3417_);
    return v_res_3422_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4(
    mut v_00_u03b1_3423_: *mut leanh::LeanObject,
    mut v_ref_3424_: *mut leanh::LeanObject,
    mut v_constName_3425_: *mut leanh::LeanObject,
    mut v___y_3426_: *mut leanh::LeanObject,
    mut v___y_3427_: *mut leanh::LeanObject,
    mut v___y_3428_: *mut leanh::LeanObject,
    mut v___y_3429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3431_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___redArg(v_ref_3424_, v_constName_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
    return v___x_3431_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b1_3432_: *mut leanh::LeanObject,
    mut v_ref_3433_: *mut leanh::LeanObject,
    mut v_constName_3434_: *mut leanh::LeanObject,
    mut v___y_3435_: *mut leanh::LeanObject,
    mut v___y_3436_: *mut leanh::LeanObject,
    mut v___y_3437_: *mut leanh::LeanObject,
    mut v___y_3438_: *mut leanh::LeanObject,
    mut v___y_3439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3440_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4(v_00_u03b1_3432_, v_ref_3433_, v_constName_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
    leanh::lean_dec(v___y_3438_);
    leanh::lean_dec_ref(v___y_3437_);
    leanh::lean_dec(v___y_3436_);
    leanh::lean_dec_ref(v___y_3435_);
    leanh::lean_dec(v_ref_3433_);
    return v_res_3440_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5(
    mut v_00_u03b1_3441_: *mut leanh::LeanObject,
    mut v_ref_3442_: *mut leanh::LeanObject,
    mut v_msg_3443_: *mut leanh::LeanObject,
    mut v_declHint_3444_: *mut leanh::LeanObject,
    mut v___y_3445_: *mut leanh::LeanObject,
    mut v___y_3446_: *mut leanh::LeanObject,
    mut v___y_3447_: *mut leanh::LeanObject,
    mut v___y_3448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3450_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5___redArg(v_ref_3442_, v_msg_3443_, v_declHint_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
    return v___x_3450_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5___boxed(
    mut v_00_u03b1_3451_: *mut leanh::LeanObject,
    mut v_ref_3452_: *mut leanh::LeanObject,
    mut v_msg_3453_: *mut leanh::LeanObject,
    mut v_declHint_3454_: *mut leanh::LeanObject,
    mut v___y_3455_: *mut leanh::LeanObject,
    mut v___y_3456_: *mut leanh::LeanObject,
    mut v___y_3457_: *mut leanh::LeanObject,
    mut v___y_3458_: *mut leanh::LeanObject,
    mut v___y_3459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3460_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5(v_00_u03b1_3451_, v_ref_3452_, v_msg_3453_, v_declHint_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
    leanh::lean_dec(v___y_3458_);
    leanh::lean_dec_ref(v___y_3457_);
    leanh::lean_dec(v___y_3456_);
    leanh::lean_dec_ref(v___y_3455_);
    leanh::lean_dec(v_ref_3452_);
    return v_res_3460_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7(
    mut v_msg_3461_: *mut leanh::LeanObject,
    mut v_declHint_3462_: *mut leanh::LeanObject,
    mut v___y_3463_: *mut leanh::LeanObject,
    mut v___y_3464_: *mut leanh::LeanObject,
    mut v___y_3465_: *mut leanh::LeanObject,
    mut v___y_3466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3468_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___redArg(v_msg_3461_, v_declHint_3462_, v___y_3466_);
    return v___x_3468_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7___boxed(
    mut v_msg_3469_: *mut leanh::LeanObject,
    mut v_declHint_3470_: *mut leanh::LeanObject,
    mut v___y_3471_: *mut leanh::LeanObject,
    mut v___y_3472_: *mut leanh::LeanObject,
    mut v___y_3473_: *mut leanh::LeanObject,
    mut v___y_3474_: *mut leanh::LeanObject,
    mut v___y_3475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3476_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__6_spec__7(v_msg_3469_, v_declHint_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
    leanh::lean_dec(v___y_3474_);
    leanh::lean_dec_ref(v___y_3473_);
    leanh::lean_dec(v___y_3472_);
    leanh::lean_dec_ref(v___y_3471_);
    return v_res_3476_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__7(
    mut v_00_u03b1_3477_: *mut leanh::LeanObject,
    mut v_ref_3478_: *mut leanh::LeanObject,
    mut v_msg_3479_: *mut leanh::LeanObject,
    mut v___y_3480_: *mut leanh::LeanObject,
    mut v___y_3481_: *mut leanh::LeanObject,
    mut v___y_3482_: *mut leanh::LeanObject,
    mut v___y_3483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3485_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__7___redArg(v_ref_3478_, v_msg_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
    return v___x_3485_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__7___boxed(
    mut v_00_u03b1_3486_: *mut leanh::LeanObject,
    mut v_ref_3487_: *mut leanh::LeanObject,
    mut v_msg_3488_: *mut leanh::LeanObject,
    mut v___y_3489_: *mut leanh::LeanObject,
    mut v___y_3490_: *mut leanh::LeanObject,
    mut v___y_3491_: *mut leanh::LeanObject,
    mut v___y_3492_: *mut leanh::LeanObject,
    mut v___y_3493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3494_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__2_spec__2_spec__4_spec__5_spec__7(v_00_u03b1_3486_, v_ref_3487_, v_msg_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
    leanh::lean_dec(v___y_3492_);
    leanh::lean_dec_ref(v___y_3491_);
    leanh::lean_dec(v___y_3490_);
    leanh::lean_dec_ref(v___y_3489_);
    leanh::lean_dec(v_ref_3487_);
    return v_res_3494_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_testAppOf(
    mut v_e_3495_: *mut leanh::LeanObject,
    mut v_c_3496_: *mut leanh::LeanObject,
    mut v_a_3497_: *mut leanh::LeanObject,
    mut v_a_3498_: *mut leanh::LeanObject,
    mut v_a_3499_: *mut leanh::LeanObject,
    mut v_a_3500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3502_: u8 = 0;
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3507_: u8 = 0;
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3513_: u8 = 0;
    let mut v_a_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3517_: u8 = 0;
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3521_: u8 = 0;
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3502_ = l_Lean_Expr_isAppOf(v_e_3495_, v_c_3496_);
                if v___x_3502_ == 0 {
                    v___x_3503_ =
                        l_Lean_Meta_whnfD(v_e_3495_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
                    if leanh::lean_obj_tag(v___x_3503_) == 0 {
                        v_a_3504_ = leanh::lean_ctor_get(v___x_3503_, 0);
                        v_isSharedCheck_3513_ =
                            (!leanh::lean_is_exclusive(v___x_3503_)) as u8;
                        if v_isSharedCheck_3513_ == 0 {
                            v___x_3506_ = v___x_3503_;
                            v_isShared_3507_ = v_isSharedCheck_3513_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3504_);
                            leanh::lean_dec(v___x_3503_);
                            v___x_3506_ = leanh::lean_box(0);
                            v_isShared_3507_ = v_isSharedCheck_3513_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3514_ = leanh::lean_ctor_get(v___x_3503_, 0);
                        v_isSharedCheck_3521_ =
                            (!leanh::lean_is_exclusive(v___x_3503_)) as u8;
                        if v_isSharedCheck_3521_ == 0 {
                            v___x_3516_ = v___x_3503_;
                            v_isShared_3517_ = v_isSharedCheck_3521_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3514_);
                            leanh::lean_dec(v___x_3503_);
                            v___x_3516_ = leanh::lean_box(0);
                            v_isShared_3517_ = v_isSharedCheck_3521_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3495_);
                    v___x_3522_ = leanh::lean_box((v___x_3502_) as usize);
                    v___x_3523_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3523_, 0, v___x_3522_);
                    return v___x_3523_;
                }
            }
            1 => {
                v___x_3508_ = l_Lean_Expr_isAppOf(v_a_3504_, v_c_3496_);
                leanh::lean_dec(v_a_3504_);
                v___x_3509_ = leanh::lean_box((v___x_3508_) as usize);
                if v_isShared_3507_ == 0 {
                    leanh::lean_ctor_set(v___x_3506_, 0, v___x_3509_);
                    v___x_3511_ = v___x_3506_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3512_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3509_);
                    v___x_3511_ = v_reuseFailAlloc_3512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3511_;
            }
            3 => {
                if v_isShared_3517_ == 0 {
                    v___x_3519_ = v___x_3516_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3520_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
                    v___x_3519_ = v_reuseFailAlloc_3520_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_testAppOf___boxed(
    mut v_e_3524_: *mut leanh::LeanObject,
    mut v_c_3525_: *mut leanh::LeanObject,
    mut v_a_3526_: *mut leanh::LeanObject,
    mut v_a_3527_: *mut leanh::LeanObject,
    mut v_a_3528_: *mut leanh::LeanObject,
    mut v_a_3529_: *mut leanh::LeanObject,
    mut v_a_3530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3531_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_testAppOf(v_e_3524_, v_c_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_);
    leanh::lean_dec(v_a_3529_);
    leanh::lean_dec_ref(v_a_3528_);
    leanh::lean_dec(v_a_3527_);
    leanh::lean_dec_ref(v_a_3526_);
    leanh::lean_dec(v_c_3525_);
    return v_res_3531_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f(
    mut v_f_3532_: *mut leanh::LeanObject,
    mut v_args_3533_: *mut leanh::LeanObject,
    mut v_useGeneralizedFieldNotation_3534_: u8,
    mut v_a_3535_: *mut leanh::LeanObject,
    mut v_a_3536_: *mut leanh::LeanObject,
    mut v_a_3537_: *mut leanh::LeanObject,
    mut v_a_3538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3545_: u8 = 0;
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: u8 = 0;
    let mut v___x_3550_: u8 = 0;
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3559_: u8 = 0;
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3564_: u8 = 0;
    let mut v_a_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3570_: u8 = 0;
    let mut v___x_3571_: u8 = 0;
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: u8 = 0;
    let mut v_env_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: u8 = 0;
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3580_: u8 = 0;
    let mut v_val_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3584_: u8 = 0;
    let mut v_snd_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3591_: u8 = 0;
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3607_: u8 = 0;
    let mut v___x_3608_: u8 = 0;
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3622_: u8 = 0;
    let mut v_a_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3626_: u8 = 0;
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3630_: u8 = 0;
    let mut v_a_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3634_: u8 = 0;
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3638_: u8 = 0;
    let mut v_snd_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v_fst_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: u8 = 0;
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3648_: u8 = 0;
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: u8 = 0;
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3657_: u8 = 0;
    let mut v_a_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3665_: u8 = 0;
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3678_: u8 = 0;
    let mut v_a_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3682_: u8 = 0;
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3551_ = lean_st_ref_get(v_a_3538_);
                v___x_3552_ = l_Lean_Expr_consumeMData(v_f_3532_);
                if leanh::lean_obj_tag(v___x_3552_) == 4 {
                    v_declName_3553_ = leanh::lean_ctor_get(v___x_3552_, 0);
                    leanh::lean_inc_n(v_declName_3553_, 2);
                    leanh::lean_dec_ref_known(v___x_3552_, 2);
                    v___x_3566_ = l_Lean_isInaccessiblePrivateName___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_isAppOfBaseName_spec__0(v_declName_3553_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_);
                    if leanh::lean_obj_tag(v___x_3566_) == 0 {
                        v_a_3567_ = leanh::lean_ctor_get(v___x_3566_, 0);
                        v_isSharedCheck_3678_ =
                            (!leanh::lean_is_exclusive(v___x_3566_)) as u8;
                        if v_isSharedCheck_3678_ == 0 {
                            v___x_3569_ = v___x_3566_;
                            v_isShared_3570_ = v_isSharedCheck_3678_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3567_);
                            leanh::lean_dec(v___x_3566_);
                            v___x_3569_ = leanh::lean_box(0);
                            v_isShared_3570_ = v_isSharedCheck_3678_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declName_3553_);
                        leanh::lean_dec(v___x_3551_);
                        leanh::lean_dec_ref(v_args_3533_);
                        leanh::lean_dec_ref(v_f_3532_);
                        v_a_3679_ = leanh::lean_ctor_get(v___x_3566_, 0);
                        v_isSharedCheck_3686_ =
                            (!leanh::lean_is_exclusive(v___x_3566_)) as u8;
                        if v_isSharedCheck_3686_ == 0 {
                            v___x_3681_ = v___x_3566_;
                            v_isShared_3682_ = v_isSharedCheck_3686_;
                            state = 28;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3679_);
                            leanh::lean_dec(v___x_3566_);
                            v___x_3681_ = leanh::lean_box(0);
                            v_isShared_3682_ = v_isSharedCheck_3686_;
                            state = 28;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3552_);
                    leanh::lean_dec(v___x_3551_);
                    leanh::lean_dec_ref(v_args_3533_);
                    leanh::lean_dec_ref(v_f_3532_);
                    v___x_3687_ = leanh::lean_box(0);
                    v___x_3688_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3688_, 0, v___x_3687_);
                    return v___x_3688_;
                }
            }
            1 => {
                v___x_3541_ = leanh::lean_box(0);
                v___x_3542_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3542_, 0, v___x_3541_);
                return v___x_3542_;
            }
            2 => {
                if v___y_3545_ == 0 {
                    leanh::lean_dec_ref(v___y_3544_);
                    state = 1;
                    continue;
                } else {
                    v___x_3546_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3546_, 0, v___y_3544_);
                    return v___x_3546_;
                }
            }
            3 => {
                v___x_3549_ = l_Lean_Exception_isInterrupt(v_a_3548_);
                if v___x_3549_ == 0 {
                    leanh::lean_inc_ref(v_a_3548_);
                    v___x_3550_ = l_Lean_Exception_isRuntime(v_a_3548_);
                    v___y_3544_ = v_a_3548_;
                    v___y_3545_ = v___x_3550_;
                    state = 2;
                    continue;
                } else {
                    v___y_3544_ = v_a_3548_;
                    v___y_3545_ = v___x_3549_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_3555_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo(v_declName_3553_, v_args_3533_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_);
                if leanh::lean_obj_tag(v___x_3555_) == 0 {
                    v_a_3556_ = leanh::lean_ctor_get(v___x_3555_, 0);
                    v_isSharedCheck_3564_ = (!leanh::lean_is_exclusive(v___x_3555_)) as u8;
                    if v_isSharedCheck_3564_ == 0 {
                        v___x_3558_ = v___x_3555_;
                        v_isShared_3559_ = v_isSharedCheck_3564_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3556_);
                        leanh::lean_dec(v___x_3555_);
                        v___x_3558_ = leanh::lean_box(0);
                        v_isShared_3559_ = v_isSharedCheck_3564_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3565_ = leanh::lean_ctor_get(v___x_3555_, 0);
                    leanh::lean_inc(v_a_3565_);
                    leanh::lean_dec_ref_known(v___x_3555_, 1);
                    v_a_3548_ = v_a_3565_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_3560_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3560_, 0, v_a_3556_);
                if v_isShared_3559_ == 0 {
                    leanh::lean_ctor_set(v___x_3558_, 0, v___x_3560_);
                    v___x_3562_ = v___x_3558_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3563_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3560_);
                    v___x_3562_ = v_reuseFailAlloc_3563_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3562_;
            }
            7 => {
                v___x_3571_ = (leanh::lean_unbox(v_a_3567_) as u8);
                leanh::lean_dec(v_a_3567_);
                if v___x_3571_ == 0 {
                    v___x_3572_ = l_Lean_Name_getPrefix(v_declName_3553_);
                    v___x_3573_ = l_Lean_Name_isAnonymous(v___x_3572_);
                    if v___x_3573_ == 0 {
                        v_env_3574_ = leanh::lean_ctor_get(v___x_3551_, 0);
                        leanh::lean_inc_ref(v_env_3574_);
                        leanh::lean_dec(v___x_3551_);
                        leanh::lean_inc(v_declName_3553_);
                        v___x_3575_ = l_Lean_hasPPNoDotAttribute(v_env_3574_, v_declName_3553_);
                        if v___x_3575_ == 0 {
                            leanh::lean_inc(v_declName_3553_);
                            v___x_3576_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo(v_declName_3553_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_);
                            if leanh::lean_obj_tag(v___x_3576_) == 0 {
                                v_a_3577_ = leanh::lean_ctor_get(v___x_3576_, 0);
                                v_isSharedCheck_3657_ =
                                    (!leanh::lean_is_exclusive(v___x_3576_)) as u8;
                                if v_isSharedCheck_3657_ == 0 {
                                    v___x_3579_ = v___x_3576_;
                                    v_isShared_3580_ = v_isSharedCheck_3657_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3577_);
                                    leanh::lean_dec(v___x_3576_);
                                    v___x_3579_ = leanh::lean_box(0);
                                    v_isShared_3580_ = v_isSharedCheck_3657_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_3572_);
                                leanh::lean_del_object(v___x_3569_);
                                leanh::lean_dec(v_declName_3553_);
                                leanh::lean_dec_ref(v_args_3533_);
                                leanh::lean_dec_ref(v_f_3532_);
                                v_a_3658_ = leanh::lean_ctor_get(v___x_3576_, 0);
                                v_isSharedCheck_3665_ =
                                    (!leanh::lean_is_exclusive(v___x_3576_)) as u8;
                                if v_isSharedCheck_3665_ == 0 {
                                    v___x_3660_ = v___x_3576_;
                                    v_isShared_3661_ = v_isSharedCheck_3665_;
                                    state = 23;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3658_);
                                    leanh::lean_dec(v___x_3576_);
                                    v___x_3660_ = leanh::lean_box(0);
                                    v_isShared_3661_ = v_isSharedCheck_3665_;
                                    state = 23;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_3572_);
                            leanh::lean_dec(v_declName_3553_);
                            leanh::lean_dec_ref(v_args_3533_);
                            leanh::lean_dec_ref(v_f_3532_);
                            v___x_3666_ = leanh::lean_box(0);
                            if v_isShared_3570_ == 0 {
                                leanh::lean_ctor_set(v___x_3569_, 0, v___x_3666_);
                                v___x_3668_ = v___x_3569_;
                                state = 25;
                                continue;
                            } else {
                                v_reuseFailAlloc_3669_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3666_);
                                v___x_3668_ = v_reuseFailAlloc_3669_;
                                state = 25;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3572_);
                        leanh::lean_dec(v_declName_3553_);
                        leanh::lean_dec(v___x_3551_);
                        leanh::lean_dec_ref(v_args_3533_);
                        leanh::lean_dec_ref(v_f_3532_);
                        v___x_3670_ = leanh::lean_box(0);
                        if v_isShared_3570_ == 0 {
                            leanh::lean_ctor_set(v___x_3569_, 0, v___x_3670_);
                            v___x_3672_ = v___x_3569_;
                            state = 26;
                            continue;
                        } else {
                            v_reuseFailAlloc_3673_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3670_);
                            v___x_3672_ = v_reuseFailAlloc_3673_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_declName_3553_);
                    leanh::lean_dec(v___x_3551_);
                    leanh::lean_dec_ref(v_args_3533_);
                    leanh::lean_dec_ref(v_f_3532_);
                    v___x_3674_ = leanh::lean_box(0);
                    if v_isShared_3570_ == 0 {
                        leanh::lean_ctor_set(v___x_3569_, 0, v___x_3674_);
                        v___x_3676_ = v___x_3569_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_3677_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3674_);
                        v___x_3676_ = v_reuseFailAlloc_3677_;
                        state = 27;
                        continue;
                    }
                }
            }
            8 => {
                if leanh::lean_obj_tag(v_a_3577_) == 1 {
                    leanh::lean_dec(v_declName_3553_);
                    leanh::lean_dec_ref(v_f_3532_);
                    v_val_3581_ = leanh::lean_ctor_get(v_a_3577_, 0);
                    v_isSharedCheck_3649_ = (!leanh::lean_is_exclusive(v_a_3577_)) as u8;
                    if v_isSharedCheck_3649_ == 0 {
                        v___x_3583_ = v_a_3577_;
                        v_isShared_3584_ = v_isSharedCheck_3649_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3581_);
                        leanh::lean_dec(v_a_3577_);
                        v___x_3583_ = leanh::lean_box(0);
                        v_isShared_3584_ = v_isSharedCheck_3649_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3579_);
                    leanh::lean_dec(v_a_3577_);
                    leanh::lean_dec(v___x_3572_);
                    leanh::lean_del_object(v___x_3569_);
                    if v_useGeneralizedFieldNotation_3534_ == 0 {
                        leanh::lean_dec(v_declName_3553_);
                        leanh::lean_dec_ref(v_args_3533_);
                        leanh::lean_dec_ref(v_f_3532_);
                        state = 1;
                        continue;
                    } else {
                        v___x_3650_ = l_Lean_Meta_isProof(
                            v_f_3532_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_,
                        );
                        if leanh::lean_obj_tag(v___x_3650_) == 0 {
                            v_a_3651_ = leanh::lean_ctor_get(v___x_3650_, 0);
                            leanh::lean_inc(v_a_3651_);
                            leanh::lean_dec_ref_known(v___x_3650_, 1);
                            v___x_3652_ = (leanh::lean_unbox(v_a_3651_) as u8);
                            leanh::lean_dec(v_a_3651_);
                            if v___x_3652_ == 0 {
                                state = 4;
                                continue;
                            } else {
                                if v___x_3575_ == 0 {
                                    leanh::lean_dec(v_declName_3553_);
                                    leanh::lean_dec_ref(v_args_3533_);
                                    v___x_3653_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_generalizedFieldInfo_spec__1___redArg___lam__0___closed__1);
                                    v___x_3654_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo_spec__0_spec__0___redArg(v___x_3653_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_);
                                    v_a_3655_ = leanh::lean_ctor_get(v___x_3654_, 0);
                                    leanh::lean_inc(v_a_3655_);
                                    leanh::lean_dec_ref(v___x_3654_);
                                    v_a_3548_ = v_a_3655_;
                                    state = 3;
                                    continue;
                                } else {
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_declName_3553_);
                            leanh::lean_dec_ref(v_args_3533_);
                            v_a_3656_ = leanh::lean_ctor_get(v___x_3650_, 0);
                            leanh::lean_inc(v_a_3656_);
                            leanh::lean_dec_ref_known(v___x_3650_, 1);
                            v_a_3548_ = v_a_3656_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            9 => {
                v_snd_3585_ = leanh::lean_ctor_get(v_val_3581_, 1);
                leanh::lean_inc(v_snd_3585_);
                v_fst_3586_ = leanh::lean_ctor_get(v_val_3581_, 0);
                leanh::lean_inc(v_fst_3586_);
                leanh::lean_dec(v_val_3581_);
                v_fst_3587_ = leanh::lean_ctor_get(v_snd_3585_, 0);
                v_snd_3588_ = leanh::lean_ctor_get(v_snd_3585_, 1);
                v_isSharedCheck_3648_ = (!leanh::lean_is_exclusive(v_snd_3585_)) as u8;
                if v_isSharedCheck_3648_ == 0 {
                    v___x_3590_ = v_snd_3585_;
                    v_isShared_3591_ = v_isSharedCheck_3648_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3588_);
                    leanh::lean_inc(v_fst_3587_);
                    leanh::lean_dec(v_snd_3585_);
                    v___x_3590_ = leanh::lean_box(0);
                    v_isShared_3591_ = v_isSharedCheck_3648_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_snd_3639_ = leanh::lean_ctor_get(v_snd_3588_, 1);
                leanh::lean_inc(v_snd_3639_);
                leanh::lean_dec(v_snd_3588_);
                v_snd_3640_ = leanh::lean_ctor_get(v_snd_3639_, 1);
                v___x_3641_ = (leanh::lean_unbox(v_snd_3640_) as u8);
                if v___x_3641_ == 0 {
                    leanh::lean_dec(v_snd_3639_);
                    leanh::lean_del_object(v___x_3569_);
                    state = 11;
                    continue;
                } else {
                    if v___x_3575_ == 0 {
                        v_fst_3642_ = leanh::lean_ctor_get(v_snd_3639_, 0);
                        leanh::lean_inc(v_fst_3642_);
                        leanh::lean_dec(v_snd_3639_);
                        v___x_3643_ = (leanh::lean_unbox(v_fst_3642_) as u8);
                        leanh::lean_dec(v_fst_3642_);
                        if v___x_3643_ == 0 {
                            leanh::lean_del_object(v___x_3590_);
                            leanh::lean_dec(v_fst_3587_);
                            leanh::lean_dec(v_fst_3586_);
                            leanh::lean_del_object(v___x_3583_);
                            leanh::lean_del_object(v___x_3579_);
                            leanh::lean_dec(v___x_3572_);
                            leanh::lean_dec_ref(v_args_3533_);
                            v___x_3644_ = leanh::lean_box(0);
                            if v_isShared_3570_ == 0 {
                                leanh::lean_ctor_set(v___x_3569_, 0, v___x_3644_);
                                v___x_3646_ = v___x_3569_;
                                state = 22;
                                continue;
                            } else {
                                v_reuseFailAlloc_3647_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
                                v___x_3646_ = v_reuseFailAlloc_3647_;
                                state = 22;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3569_);
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_3639_);
                        leanh::lean_del_object(v___x_3569_);
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                v___x_3593_ = lean_array_get_size(v_args_3533_);
                v___x_3594_ = lean_nat_dec_lt(v_fst_3587_, v___x_3593_);
                if v___x_3594_ == 0 {
                    leanh::lean_del_object(v___x_3590_);
                    leanh::lean_dec(v_fst_3587_);
                    leanh::lean_dec(v_fst_3586_);
                    leanh::lean_del_object(v___x_3583_);
                    leanh::lean_dec(v___x_3572_);
                    leanh::lean_dec_ref(v_args_3533_);
                    v___x_3595_ = leanh::lean_box(0);
                    if v_isShared_3580_ == 0 {
                        leanh::lean_ctor_set(v___x_3579_, 0, v___x_3595_);
                        v___x_3597_ = v___x_3579_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3598_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3595_);
                        v___x_3597_ = v_reuseFailAlloc_3598_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3579_);
                    v___x_3599_ = l_Lean_instInhabitedExpr;
                    v___x_3600_ = lean_array_get(v___x_3599_, v_args_3533_, v_fst_3587_);
                    leanh::lean_dec_ref(v_args_3533_);
                    leanh::lean_inc(v_a_3538_);
                    leanh::lean_inc_ref(v_a_3537_);
                    leanh::lean_inc(v_a_3536_);
                    leanh::lean_inc_ref(v_a_3535_);
                    v___x_3601_ =
                        lean_infer_type(v___x_3600_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_);
                    if leanh::lean_obj_tag(v___x_3601_) == 0 {
                        v_a_3602_ = leanh::lean_ctor_get(v___x_3601_, 0);
                        leanh::lean_inc(v_a_3602_);
                        leanh::lean_dec_ref_known(v___x_3601_, 1);
                        v___x_3603_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_testAppOf(v_a_3602_, v___x_3572_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_);
                        leanh::lean_dec(v___x_3572_);
                        if leanh::lean_obj_tag(v___x_3603_) == 0 {
                            v_a_3604_ = leanh::lean_ctor_get(v___x_3603_, 0);
                            v_isSharedCheck_3622_ =
                                (!leanh::lean_is_exclusive(v___x_3603_)) as u8;
                            if v_isSharedCheck_3622_ == 0 {
                                v___x_3606_ = v___x_3603_;
                                v_isShared_3607_ = v_isSharedCheck_3622_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3604_);
                                leanh::lean_dec(v___x_3603_);
                                v___x_3606_ = leanh::lean_box(0);
                                v_isShared_3607_ = v_isSharedCheck_3622_;
                                state = 13;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3590_);
                            leanh::lean_dec(v_fst_3587_);
                            leanh::lean_dec(v_fst_3586_);
                            leanh::lean_del_object(v___x_3583_);
                            v_a_3623_ = leanh::lean_ctor_get(v___x_3603_, 0);
                            v_isSharedCheck_3630_ =
                                (!leanh::lean_is_exclusive(v___x_3603_)) as u8;
                            if v_isSharedCheck_3630_ == 0 {
                                v___x_3625_ = v___x_3603_;
                                v_isShared_3626_ = v_isSharedCheck_3630_;
                                state = 18;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3623_);
                                leanh::lean_dec(v___x_3603_);
                                v___x_3625_ = leanh::lean_box(0);
                                v_isShared_3626_ = v_isSharedCheck_3630_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_3590_);
                        leanh::lean_dec(v_fst_3587_);
                        leanh::lean_dec(v_fst_3586_);
                        leanh::lean_del_object(v___x_3583_);
                        leanh::lean_dec(v___x_3572_);
                        v_a_3631_ = leanh::lean_ctor_get(v___x_3601_, 0);
                        v_isSharedCheck_3638_ =
                            (!leanh::lean_is_exclusive(v___x_3601_)) as u8;
                        if v_isSharedCheck_3638_ == 0 {
                            v___x_3633_ = v___x_3601_;
                            v_isShared_3634_ = v_isSharedCheck_3638_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3631_);
                            leanh::lean_dec(v___x_3601_);
                            v___x_3633_ = leanh::lean_box(0);
                            v_isShared_3634_ = v_isSharedCheck_3638_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            12 => {
                return v___x_3597_;
            }
            13 => {
                v___x_3608_ = (leanh::lean_unbox(v_a_3604_) as u8);
                leanh::lean_dec(v_a_3604_);
                if v___x_3608_ == 0 {
                    leanh::lean_del_object(v___x_3590_);
                    leanh::lean_dec(v_fst_3587_);
                    leanh::lean_dec(v_fst_3586_);
                    leanh::lean_del_object(v___x_3583_);
                    v___x_3609_ = leanh::lean_box(0);
                    if v_isShared_3607_ == 0 {
                        leanh::lean_ctor_set(v___x_3606_, 0, v___x_3609_);
                        v___x_3611_ = v___x_3606_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3612_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3609_);
                        v___x_3611_ = v_reuseFailAlloc_3612_;
                        state = 14;
                        continue;
                    }
                } else {
                    if v_isShared_3591_ == 0 {
                        leanh::lean_ctor_set(v___x_3590_, 1, v_fst_3587_);
                        leanh::lean_ctor_set(v___x_3590_, 0, v_fst_3586_);
                        v___x_3614_ = v___x_3590_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3621_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_fst_3586_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_fst_3587_);
                        v___x_3614_ = v_reuseFailAlloc_3621_;
                        state = 15;
                        continue;
                    }
                }
            }
            14 => {
                return v___x_3611_;
            }
            15 => {
                if v_isShared_3584_ == 0 {
                    leanh::lean_ctor_set(v___x_3583_, 0, v___x_3614_);
                    v___x_3616_ = v___x_3583_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3620_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3614_);
                    v___x_3616_ = v_reuseFailAlloc_3620_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_3607_ == 0 {
                    leanh::lean_ctor_set(v___x_3606_, 0, v___x_3616_);
                    v___x_3618_ = v___x_3606_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3619_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3616_);
                    v___x_3618_ = v_reuseFailAlloc_3619_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3618_;
            }
            18 => {
                if v_isShared_3626_ == 0 {
                    v___x_3628_ = v___x_3625_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3629_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
                    v___x_3628_ = v_reuseFailAlloc_3629_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3628_;
            }
            20 => {
                if v_isShared_3634_ == 0 {
                    v___x_3636_ = v___x_3633_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3637_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
                    v___x_3636_ = v_reuseFailAlloc_3637_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3636_;
            }
            22 => {
                return v___x_3646_;
            }
            23 => {
                if v_isShared_3661_ == 0 {
                    v___x_3663_ = v___x_3660_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3664_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
                    v___x_3663_ = v_reuseFailAlloc_3664_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3663_;
            }
            25 => {
                return v___x_3668_;
            }
            26 => {
                return v___x_3672_;
            }
            27 => {
                return v___x_3676_;
            }
            28 => {
                if v_isShared_3682_ == 0 {
                    v___x_3684_ = v___x_3681_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
                    v___x_3684_ = v_reuseFailAlloc_3685_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f___boxed(
    mut v_f_3689_: *mut leanh::LeanObject,
    mut v_args_3690_: *mut leanh::LeanObject,
    mut v_useGeneralizedFieldNotation_3691_: *mut leanh::LeanObject,
    mut v_a_3692_: *mut leanh::LeanObject,
    mut v_a_3693_: *mut leanh::LeanObject,
    mut v_a_3694_: *mut leanh::LeanObject,
    mut v_a_3695_: *mut leanh::LeanObject,
    mut v_a_3696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useGeneralizedFieldNotation_boxed_3697_: u8 = 0;
    let mut v_res_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useGeneralizedFieldNotation_boxed_3697_ =
        (leanh::lean_unbox(v_useGeneralizedFieldNotation_3691_) as u8);
    v_res_3698_ = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f(
        v_f_3689_,
        v_args_3690_,
        v_useGeneralizedFieldNotation_boxed_3697_,
        v_a_3692_,
        v_a_3693_,
        v_a_3694_,
        v_a_3695_,
    );
    leanh::lean_dec(v_a_3695_);
    leanh::lean_dec_ref(v_a_3694_);
    leanh::lean_dec(v_a_3693_);
    leanh::lean_dec_ref(v_a_3692_);
    return v_res_3698_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_parentProj_x3f(
    mut v_explicit_3699_: u8,
    mut v_e_3700_: *mut leanh::LeanObject,
    mut v_a_3701_: *mut leanh::LeanObject,
    mut v_a_3702_: *mut leanh::LeanObject,
    mut v_a_3703_: *mut leanh::LeanObject,
    mut v_a_3704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3706_: u8 = 0;
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3715_: u8 = 0;
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v_snd_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3730_: u8 = 0;
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: u8 = 0;
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: u8 = 0;
    let mut v_fst_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: u8 = 0;
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: u8 = 0;
    let mut v_isSharedCheck_3746_: u8 = 0;
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3749_: u8 = 0;
    let mut v_a_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3753_: u8 = 0;
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3757_: u8 = 0;
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3706_ = l_Lean_Expr_isApp(v_e_3700_);
                if v___x_3706_ == 0 {
                    v___x_3707_ = leanh::lean_box(0);
                    v___x_3708_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3708_, 0, v___x_3707_);
                    return v___x_3708_;
                } else {
                    v___x_3709_ = l_Lean_Expr_getAppFn(v_e_3700_);
                    if leanh::lean_obj_tag(v___x_3709_) == 4 {
                        v_declName_3710_ = leanh::lean_ctor_get(v___x_3709_, 0);
                        leanh::lean_inc(v_declName_3710_);
                        leanh::lean_dec_ref_known(v___x_3709_, 2);
                        v___x_3711_ = l___private_Lean_PrettyPrinter_Delaborator_FieldNotation_0__Lean_PrettyPrinter_Delaborator_projInfo(v_declName_3710_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_);
                        if leanh::lean_obj_tag(v___x_3711_) == 0 {
                            v_a_3712_ = leanh::lean_ctor_get(v___x_3711_, 0);
                            v_isSharedCheck_3749_ =
                                (!leanh::lean_is_exclusive(v___x_3711_)) as u8;
                            if v_isSharedCheck_3749_ == 0 {
                                v___x_3714_ = v___x_3711_;
                                v_isShared_3715_ = v_isSharedCheck_3749_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3712_);
                                leanh::lean_dec(v___x_3711_);
                                v___x_3714_ = leanh::lean_box(0);
                                v_isShared_3715_ = v_isSharedCheck_3749_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3750_ = leanh::lean_ctor_get(v___x_3711_, 0);
                            v_isSharedCheck_3757_ =
                                (!leanh::lean_is_exclusive(v___x_3711_)) as u8;
                            if v_isSharedCheck_3757_ == 0 {
                                v___x_3752_ = v___x_3711_;
                                v_isShared_3753_ = v_isSharedCheck_3757_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3750_);
                                leanh::lean_dec(v___x_3711_);
                                v___x_3752_ = leanh::lean_box(0);
                                v_isShared_3753_ = v_isSharedCheck_3757_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3709_);
                        v___x_3758_ = leanh::lean_box(0);
                        v___x_3759_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3759_, 0, v___x_3758_);
                        return v___x_3759_;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3712_) == 1 {
                    v_val_3721_ = leanh::lean_ctor_get(v_a_3712_, 0);
                    v_isSharedCheck_3746_ = (!leanh::lean_is_exclusive(v_a_3712_)) as u8;
                    if v_isSharedCheck_3746_ == 0 {
                        v___x_3723_ = v_a_3712_;
                        v_isShared_3724_ = v_isSharedCheck_3746_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3721_);
                        leanh::lean_dec(v_a_3712_);
                        v___x_3723_ = leanh::lean_box(0);
                        v_isShared_3724_ = v_isSharedCheck_3746_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3714_);
                    leanh::lean_dec(v_a_3712_);
                    v___x_3747_ = leanh::lean_box(0);
                    v___x_3748_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3748_, 0, v___x_3747_);
                    return v___x_3748_;
                }
            }
            2 => {
                v___x_3717_ = leanh::lean_box(0);
                if v_isShared_3715_ == 0 {
                    leanh::lean_ctor_set(v___x_3714_, 0, v___x_3717_);
                    v___x_3719_ = v___x_3714_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3720_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3717_);
                    v___x_3719_ = v_reuseFailAlloc_3720_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3719_;
            }
            4 => {
                v_snd_3725_ = leanh::lean_ctor_get(v_val_3721_, 1);
                leanh::lean_inc(v_snd_3725_);
                v_fst_3726_ = leanh::lean_ctor_get(v_val_3721_, 0);
                leanh::lean_inc(v_fst_3726_);
                leanh::lean_dec(v_val_3721_);
                v_fst_3727_ = leanh::lean_ctor_get(v_snd_3725_, 0);
                leanh::lean_inc(v_fst_3727_);
                v_snd_3728_ = leanh::lean_ctor_get(v_snd_3725_, 1);
                leanh::lean_inc(v_snd_3728_);
                leanh::lean_dec(v_snd_3725_);
                v_snd_3739_ = leanh::lean_ctor_get(v_snd_3728_, 1);
                leanh::lean_inc(v_snd_3739_);
                v_fst_3740_ = leanh::lean_ctor_get(v_snd_3728_, 0);
                leanh::lean_inc(v_fst_3740_);
                leanh::lean_dec(v_snd_3728_);
                v___x_3741_ = (leanh::lean_unbox(v_fst_3740_) as u8);
                leanh::lean_dec(v_fst_3740_);
                if v___x_3741_ == 0 {
                    leanh::lean_dec(v_snd_3739_);
                    leanh::lean_dec(v_fst_3727_);
                    leanh::lean_dec(v_fst_3726_);
                    leanh::lean_del_object(v___x_3723_);
                    state = 2;
                    continue;
                } else {
                    v_fst_3742_ = leanh::lean_ctor_get(v_snd_3739_, 0);
                    leanh::lean_inc(v_fst_3742_);
                    leanh::lean_dec(v_snd_3739_);
                    v___x_3743_ = (leanh::lean_unbox(v_fst_3742_) as u8);
                    leanh::lean_dec(v_fst_3742_);
                    if v___x_3743_ == 0 {
                        leanh::lean_dec(v_fst_3727_);
                        leanh::lean_dec(v_fst_3726_);
                        leanh::lean_del_object(v___x_3723_);
                        state = 2;
                        continue;
                    } else {
                        if v_explicit_3699_ == 0 {
                            v___y_3730_ = v___x_3706_;
                            state = 5;
                            continue;
                        } else {
                            v___x_3744_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3745_ = lean_nat_dec_eq(v_fst_3727_, v___x_3744_);
                            v___y_3730_ = v___x_3745_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v___y_3730_ == 0 {
                    leanh::lean_dec(v_fst_3727_);
                    leanh::lean_dec(v_fst_3726_);
                    leanh::lean_del_object(v___x_3723_);
                    state = 2;
                    continue;
                } else {
                    v___x_3731_ = l_Lean_Expr_getAppNumArgs(v_e_3700_);
                    v___x_3732_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3733_ = lean_nat_add(v_fst_3727_, v___x_3732_);
                    leanh::lean_dec(v_fst_3727_);
                    v___x_3734_ = lean_nat_dec_eq(v___x_3731_, v___x_3733_);
                    leanh::lean_dec(v___x_3733_);
                    leanh::lean_dec(v___x_3731_);
                    if v___x_3734_ == 0 {
                        leanh::lean_dec(v_fst_3726_);
                        leanh::lean_del_object(v___x_3723_);
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_3714_);
                        if v_isShared_3724_ == 0 {
                            leanh::lean_ctor_set(v___x_3723_, 0, v_fst_3726_);
                            v___x_3736_ = v___x_3723_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3738_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_fst_3726_);
                            v___x_3736_ = v_reuseFailAlloc_3738_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___x_3737_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3737_, 0, v___x_3736_);
                return v___x_3737_;
            }
            7 => {
                if v_isShared_3753_ == 0 {
                    v___x_3755_ = v___x_3752_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3756_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
                    v___x_3755_ = v_reuseFailAlloc_3756_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3755_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_parentProj_x3f___boxed(
    mut v_explicit_3760_: *mut leanh::LeanObject,
    mut v_e_3761_: *mut leanh::LeanObject,
    mut v_a_3762_: *mut leanh::LeanObject,
    mut v_a_3763_: *mut leanh::LeanObject,
    mut v_a_3764_: *mut leanh::LeanObject,
    mut v_a_3765_: *mut leanh::LeanObject,
    mut v_a_3766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_explicit_boxed_3767_: u8 = 0;
    let mut v_res_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_explicit_boxed_3767_ = (leanh::lean_unbox(v_explicit_3760_) as u8);
    v_res_3768_ = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f(
        v_explicit_boxed_3767_,
        v_e_3761_,
        v_a_3762_,
        v_a_3763_,
        v_a_3764_,
        v_a_3765_,
    );
    leanh::lean_dec(v_a_3765_);
    leanh::lean_dec_ref(v_a_3764_);
    leanh::lean_dec(v_a_3763_);
    leanh::lean_dec_ref(v_a_3762_);
    leanh::lean_dec_ref(v_e_3761_);
    return v_res_3768_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_isParentProj(
    mut v_explicit_3769_: u8,
    mut v_e_3770_: *mut leanh::LeanObject,
    mut v_a_3771_: *mut leanh::LeanObject,
    mut v_a_3772_: *mut leanh::LeanObject,
    mut v_a_3773_: *mut leanh::LeanObject,
    mut v_a_3774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3780_: u8 = 0;
    let mut v___x_3781_: u8 = 0;
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3791_: u8 = 0;
    let mut v_a_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3795_: u8 = 0;
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3776_ = l_Lean_PrettyPrinter_Delaborator_parentProj_x3f(
                    v_explicit_3769_,
                    v_e_3770_,
                    v_a_3771_,
                    v_a_3772_,
                    v_a_3773_,
                    v_a_3774_,
                );
                if leanh::lean_obj_tag(v___x_3776_) == 0 {
                    v_a_3777_ = leanh::lean_ctor_get(v___x_3776_, 0);
                    v_isSharedCheck_3791_ = (!leanh::lean_is_exclusive(v___x_3776_)) as u8;
                    if v_isSharedCheck_3791_ == 0 {
                        v___x_3779_ = v___x_3776_;
                        v_isShared_3780_ = v_isSharedCheck_3791_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3777_);
                        leanh::lean_dec(v___x_3776_);
                        v___x_3779_ = leanh::lean_box(0);
                        v_isShared_3780_ = v_isSharedCheck_3791_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3792_ = leanh::lean_ctor_get(v___x_3776_, 0);
                    v_isSharedCheck_3799_ = (!leanh::lean_is_exclusive(v___x_3776_)) as u8;
                    if v_isSharedCheck_3799_ == 0 {
                        v___x_3794_ = v___x_3776_;
                        v_isShared_3795_ = v_isSharedCheck_3799_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3792_);
                        leanh::lean_dec(v___x_3776_);
                        v___x_3794_ = leanh::lean_box(0);
                        v_isShared_3795_ = v_isSharedCheck_3799_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3777_) == 0 {
                    v___x_3781_ = 0;
                    v___x_3782_ = leanh::lean_box((v___x_3781_) as usize);
                    if v_isShared_3780_ == 0 {
                        leanh::lean_ctor_set(v___x_3779_, 0, v___x_3782_);
                        v___x_3784_ = v___x_3779_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3785_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3782_);
                        v___x_3784_ = v_reuseFailAlloc_3785_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_a_3777_, 1);
                    v___x_3786_ = 1;
                    v___x_3787_ = leanh::lean_box((v___x_3786_) as usize);
                    if v_isShared_3780_ == 0 {
                        leanh::lean_ctor_set(v___x_3779_, 0, v___x_3787_);
                        v___x_3789_ = v___x_3779_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3790_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3787_);
                        v___x_3789_ = v_reuseFailAlloc_3790_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3784_;
            }
            3 => {
                return v___x_3789_;
            }
            4 => {
                if v_isShared_3795_ == 0 {
                    v___x_3797_ = v___x_3794_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3798_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
                    v___x_3797_ = v_reuseFailAlloc_3798_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_isParentProj___boxed(
    mut v_explicit_3800_: *mut leanh::LeanObject,
    mut v_e_3801_: *mut leanh::LeanObject,
    mut v_a_3802_: *mut leanh::LeanObject,
    mut v_a_3803_: *mut leanh::LeanObject,
    mut v_a_3804_: *mut leanh::LeanObject,
    mut v_a_3805_: *mut leanh::LeanObject,
    mut v_a_3806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_explicit_boxed_3807_: u8 = 0;
    let mut v_res_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_explicit_boxed_3807_ = (leanh::lean_unbox(v_explicit_3800_) as u8);
    v_res_3808_ = l_Lean_PrettyPrinter_Delaborator_isParentProj(
        v_explicit_boxed_3807_,
        v_e_3801_,
        v_a_3802_,
        v_a_3803_,
        v_a_3804_,
        v_a_3805_,
    );
    leanh::lean_dec(v_a_3805_);
    leanh::lean_dec_ref(v_a_3804_);
    leanh::lean_dec(v_a_3803_);
    leanh::lean_dec_ref(v_a_3802_);
    leanh::lean_dec_ref(v_e_3801_);
    return v_res_3808_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrettyPrinter_Delaborator_FieldNotation(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Attributes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrettyPrinter_Delaborator_FieldNotation(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_PrettyPrinter_Delaborator_FieldNotation(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_WHNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Delaborator_Attributes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_FieldNotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_PrettyPrinter_Delaborator_FieldNotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_PrettyPrinter_Delaborator_FieldNotation(builtin);
}