// Lean compiler output
// Module: Lean.Elab.DeclNameGen
// Imports: Lean.Elab.Command Init.Data.String.Modify Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv,
    lean_expr_instantiate_rev_range, lean_expr_instantiate1, lean_find_expr, lean_infer_type,
    lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_string_dec_eq,
    lean_string_utf8_get, lean_string_utf8_set, lean_uint32_add, lean_uint32_dec_le,
    lean_uint64_lor, lean_uint64_of_nat, lean_uint64_shift_left, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_land, lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right,
    lean_usize_sub, lean_usize_to_nat, lean_whnf,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_getRoot;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hasMacroScopes,
    l_Lean_Name_hash___override___boxed, l_Lean_Name_str___override,
    l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::{l_Lean_Core_mkFreshUserName, l_Lean_Exception_isRuntime};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::Binders::l_Lean_Elab_Term_elabBinders___boxed;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_runTermElabM___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabType, l_Lean_Elab_Term_withAutoBoundImplicit___redArg,
    l_Lean_Elab_Term_withoutErrToSorryImp___redArg,
};
use crate::r#gen::Lean::Elab::Util::{
    l_Lean_Elab_expandMacroImpl_x3f, l_Lean_Elab_getBetterRef,
    l_Lean_Elab_mkUnusedBaseName___boxed, l_Lean_Elab_pp_macroStack,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_allImportedModuleNames, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg, l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isExplicit, l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21,
    l_Lean_Expr_bvar___override, l_Lean_Expr_const___override, l_Lean_Expr_etaExpandedStrict_x3f,
    l_Lean_Expr_forallE___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar, l_Lean_Expr_hash, l_Lean_Expr_isForall,
    l_Lean_Expr_isProp, l_Lean_Expr_isSort, l_Lean_Expr_isType, l_Lean_Expr_sort___override,
};
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_param___override, l_Lean_Level_succ___override};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_mkForallFVars,
};
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_isProof, l_Lean_Meta_isTypeFormer};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::{l_Lean_isPrivateName, l_Lean_privateToUserName};
use crate::r#gen::Lean::ProjFns::l_Lean_Environment_getProjectionFnInfo_x3f;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_resolveGlobalName, l_Lean_ResolveName_resolveNamespace,
};
use crate::r#gen::Lean::Structure::l_Lean_isSubobjectField_x3f;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___closed__0: u64 = 0;
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [117, 0]};
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__1_value) as *mut crate::leanh::LeanObject,12562556307207860968 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [70, 111, 114, 97, 108, 108, 0]};
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 114, 111, 112, 0]};
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 121, 112, 101, 0]};
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 111, 114, 116, 0]};
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [79, 102, 0]};
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1_value:
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
    m_fun: l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__20_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__21_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__22_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__22_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<158> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [105, 110, 115, 116, 0],
};
static mut l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(
    mut v_e_3462_: *mut crate::leanh::LeanObject,
    mut v_a_3463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v_ctorName_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: u8 = 0;
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: u8 = 0;
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3501_: u8 = 0;
    let mut v_induct_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3510_: u8 = 0;
    let mut v_isSharedCheck_3511_: u8 = 0;
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3471_ = l_Lean_Expr_getAppFn(v_e_3462_);
                if crate::leanh::lean_obj_tag(v___x_3471_) == 4 {
                    v_declName_3472_ = crate::leanh::lean_ctor_get(v___x_3471_, 0);
                    crate::leanh::lean_inc(v_declName_3472_);
                    crate::leanh::lean_dec_ref_known(v___x_3471_, 2);
                    if crate::leanh::lean_obj_tag(v_declName_3472_) == 1 {
                        v_str_3473_ = crate::leanh::lean_ctor_get(v_declName_3472_, 1);
                        crate::leanh::lean_inc_ref(v_str_3473_);
                        v___x_3474_ = lean_st_ref_get(v_a_3463_);
                        v_env_3479_ = crate::leanh::lean_ctor_get(v___x_3474_, 0);
                        crate::leanh::lean_inc_ref_n(v_env_3479_, 2);
                        crate::leanh::lean_dec(v___x_3474_);
                        v___x_3480_ = l_Lean_Environment_getProjectionFnInfo_x3f(
                            v_env_3479_,
                            v_declName_3472_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3480_) == 1 {
                            v_val_3481_ = crate::leanh::lean_ctor_get(v___x_3480_, 0);
                            v_isSharedCheck_3511_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3480_)) as u8;
                            if v_isSharedCheck_3511_ == 0 {
                                v___x_3483_ = v___x_3480_;
                                v_isShared_3484_ = v_isSharedCheck_3511_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_3481_);
                                crate::leanh::lean_dec(v___x_3480_);
                                v___x_3483_ = crate::leanh::lean_box(0);
                                v_isShared_3484_ = v_isSharedCheck_3511_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3480_);
                            crate::leanh::lean_dec_ref(v_env_3479_);
                            crate::leanh::lean_dec_ref(v_str_3473_);
                            v___x_3512_ = crate::leanh::lean_box(0);
                            v___x_3513_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3513_, 0, v___x_3512_);
                            return v___x_3513_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_3472_);
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3471_);
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3466_ = crate::leanh::lean_box(0);
                v___x_3467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3467_, 0, v___x_3466_);
                return v___x_3467_;
            }
            2 => {
                v___x_3469_ = crate::leanh::lean_box(0);
                v___x_3470_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3470_, 0, v___x_3469_);
                return v___x_3470_;
            }
            3 => {
                v___x_3476_ = l_Lean_Expr_appArg_x21(v_e_3462_);
                v___x_3477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3477_, 0, v___x_3476_);
                v___x_3478_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3478_, 0, v___x_3477_);
                return v___x_3478_;
            }
            4 => {
                v_ctorName_3485_ = crate::leanh::lean_ctor_get(v_val_3481_, 0);
                crate::leanh::lean_inc(v_ctorName_3485_);
                v_numParams_3486_ = crate::leanh::lean_ctor_get(v_val_3481_, 1);
                crate::leanh::lean_inc(v_numParams_3486_);
                crate::leanh::lean_dec(v_val_3481_);
                v___x_3487_ = l_Lean_Expr_getAppNumArgs(v_e_3462_);
                v___x_3488_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3489_ = lean_nat_add(v_numParams_3486_, v___x_3488_);
                crate::leanh::lean_dec(v_numParams_3486_);
                v___x_3490_ = lean_nat_dec_eq(v___x_3487_, v___x_3489_);
                crate::leanh::lean_dec(v___x_3489_);
                crate::leanh::lean_dec(v___x_3487_);
                if v___x_3490_ == 0 {
                    crate::leanh::lean_dec(v_ctorName_3485_);
                    crate::leanh::lean_dec_ref(v_env_3479_);
                    crate::leanh::lean_dec_ref(v_str_3473_);
                    v___x_3491_ = crate::leanh::lean_box(0);
                    if v_isShared_3484_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3483_, 0);
                        crate::leanh::lean_ctor_set(v___x_3483_, 0, v___x_3491_);
                        v___x_3493_ = v___x_3483_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
                        v___x_3493_ = v_reuseFailAlloc_3494_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3483_);
                    v___x_3495_ = 0;
                    crate::leanh::lean_inc_ref(v_env_3479_);
                    v___x_3496_ =
                        l_Lean_Environment_find_x3f(v_env_3479_, v_ctorName_3485_, v___x_3495_);
                    if crate::leanh::lean_obj_tag(v___x_3496_) == 1 {
                        v_val_3497_ = crate::leanh::lean_ctor_get(v___x_3496_, 0);
                        crate::leanh::lean_inc(v_val_3497_);
                        crate::leanh::lean_dec_ref_known(v___x_3496_, 1);
                        if crate::leanh::lean_obj_tag(v_val_3497_) == 6 {
                            v_val_3498_ = crate::leanh::lean_ctor_get(v_val_3497_, 0);
                            v_isSharedCheck_3510_ =
                                (!crate::leanh::lean_is_exclusive(v_val_3497_)) as u8;
                            if v_isSharedCheck_3510_ == 0 {
                                v___x_3500_ = v_val_3497_;
                                v_isShared_3501_ = v_isSharedCheck_3510_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_3498_);
                                crate::leanh::lean_dec(v_val_3497_);
                                v___x_3500_ = crate::leanh::lean_box(0);
                                v_isShared_3501_ = v_isSharedCheck_3510_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_3497_);
                            crate::leanh::lean_dec_ref(v_env_3479_);
                            crate::leanh::lean_dec_ref(v_str_3473_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3496_);
                        crate::leanh::lean_dec_ref(v_env_3479_);
                        crate::leanh::lean_dec_ref(v_str_3473_);
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3493_;
            }
            6 => {
                v_induct_3502_ = crate::leanh::lean_ctor_get(v_val_3498_, 1);
                crate::leanh::lean_inc(v_induct_3502_);
                crate::leanh::lean_dec_ref(v_val_3498_);
                v___x_3503_ = crate::leanh::lean_box(0);
                v___x_3504_ = l_Lean_Name_str___override(v___x_3503_, v_str_3473_);
                v___x_3505_ = l_Lean_isSubobjectField_x3f(v_env_3479_, v_induct_3502_, v___x_3504_);
                if crate::leanh::lean_obj_tag(v___x_3505_) == 0 {
                    if v___x_3490_ == 0 {
                        crate::leanh::lean_del_object(v___x_3500_);
                        state = 3;
                        continue;
                    } else {
                        v___x_3506_ = crate::leanh::lean_box(0);
                        if v_isShared_3501_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_3500_, 0);
                            crate::leanh::lean_ctor_set(v___x_3500_, 0, v___x_3506_);
                            v___x_3508_ = v___x_3500_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3509_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
                            v___x_3508_ = v_reuseFailAlloc_3509_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3505_, 1);
                    crate::leanh::lean_del_object(v___x_3500_);
                    state = 3;
                    continue;
                }
            }
            7 => {
                return v___x_3508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg___boxed(
    mut v_e_3514_: *mut crate::leanh::LeanObject,
    mut v_a_3515_: *mut crate::leanh::LeanObject,
    mut v_a_3516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3517_ =
        l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(
            v_e_3514_, v_a_3515_,
        );
    crate::leanh::lean_dec(v_a_3515_);
    crate::leanh::lean_dec_ref(v_e_3514_);
    return v_res_3517_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg(
    mut v_e_3518_: *mut crate::leanh::LeanObject,
    mut v_a_3519_: *mut crate::leanh::LeanObject,
    mut v_a_3520_: *mut crate::leanh::LeanObject,
    mut v_a_3521_: *mut crate::leanh::LeanObject,
    mut v_a_3522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3524_ =
        l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(
            v_e_3518_, v_a_3522_,
        );
    return v___x_3524_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___boxed(
    mut v_e_3525_: *mut crate::leanh::LeanObject,
    mut v_a_3526_: *mut crate::leanh::LeanObject,
    mut v_a_3527_: *mut crate::leanh::LeanObject,
    mut v_a_3528_: *mut crate::leanh::LeanObject,
    mut v_a_3529_: *mut crate::leanh::LeanObject,
    mut v_a_3530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3531_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg(
        v_e_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_,
    );
    crate::leanh::lean_dec(v_a_3529_);
    crate::leanh::lean_dec_ref(v_a_3528_);
    crate::leanh::lean_dec(v_a_3527_);
    crate::leanh::lean_dec_ref(v_a_3526_);
    crate::leanh::lean_dec_ref(v_e_3525_);
    return v_res_3531_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0(
    mut v_k_3532_: *mut crate::leanh::LeanObject,
    mut v___y_3533_: *mut crate::leanh::LeanObject,
    mut v_b_3534_: *mut crate::leanh::LeanObject,
    mut v___y_3535_: *mut crate::leanh::LeanObject,
    mut v___y_3536_: *mut crate::leanh::LeanObject,
    mut v___y_3537_: *mut crate::leanh::LeanObject,
    mut v___y_3538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3538_);
    crate::leanh::lean_inc_ref(v___y_3537_);
    crate::leanh::lean_inc(v___y_3536_);
    crate::leanh::lean_inc_ref(v___y_3535_);
    crate::leanh::lean_inc(v___y_3533_);
    v___x_3540_ = crate::leanh::lean_apply_7(
        v_k_3532_,
        v_b_3534_,
        v___y_3533_,
        v___y_3535_,
        v___y_3536_,
        v___y_3537_,
        v___y_3538_,
        crate::leanh::lean_box(0),
    );
    return v___x_3540_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0___boxed(
    mut v_k_3541_: *mut crate::leanh::LeanObject,
    mut v___y_3542_: *mut crate::leanh::LeanObject,
    mut v_b_3543_: *mut crate::leanh::LeanObject,
    mut v___y_3544_: *mut crate::leanh::LeanObject,
    mut v___y_3545_: *mut crate::leanh::LeanObject,
    mut v___y_3546_: *mut crate::leanh::LeanObject,
    mut v___y_3547_: *mut crate::leanh::LeanObject,
    mut v___y_3548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3549_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0(v_k_3541_, v___y_3542_, v_b_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
    crate::leanh::lean_dec(v___y_3547_);
    crate::leanh::lean_dec_ref(v___y_3546_);
    crate::leanh::lean_dec(v___y_3545_);
    crate::leanh::lean_dec_ref(v___y_3544_);
    crate::leanh::lean_dec(v___y_3542_);
    return v_res_3549_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(
    mut v_name_3550_: *mut crate::leanh::LeanObject,
    mut v_bi_3551_: u8,
    mut v_type_3552_: *mut crate::leanh::LeanObject,
    mut v_k_3553_: *mut crate::leanh::LeanObject,
    mut v_kind_3554_: u8,
    mut v___y_3555_: *mut crate::leanh::LeanObject,
    mut v___y_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
    mut v___y_3558_: *mut crate::leanh::LeanObject,
    mut v___y_3559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3566_: u8 = 0;
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3555_);
                v___f_3561_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                crate::leanh::lean_closure_set(v___f_3561_, 0, v_k_3553_);
                crate::leanh::lean_closure_set(v___f_3561_, 1, v___y_3555_);
                v___x_3562_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_3550_,
                    v_bi_3551_,
                    v_type_3552_,
                    v___f_3561_,
                    v_kind_3554_,
                    v___y_3556_,
                    v___y_3557_,
                    v___y_3558_,
                    v___y_3559_,
                );
                if crate::leanh::lean_obj_tag(v___x_3562_) == 0 {
                    return v___x_3562_;
                } else {
                    v_a_3563_ = crate::leanh::lean_ctor_get(v___x_3562_, 0);
                    v_isSharedCheck_3570_ = (!crate::leanh::lean_is_exclusive(v___x_3562_)) as u8;
                    if v_isSharedCheck_3570_ == 0 {
                        v___x_3565_ = v___x_3562_;
                        v_isShared_3566_ = v_isSharedCheck_3570_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3563_);
                        crate::leanh::lean_dec(v___x_3562_);
                        v___x_3565_ = crate::leanh::lean_box(0);
                        v_isShared_3566_ = v_isSharedCheck_3570_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3566_ == 0 {
                    v___x_3568_ = v___x_3565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
                    v___x_3568_ = v_reuseFailAlloc_3569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___boxed(
    mut v_name_3571_: *mut crate::leanh::LeanObject,
    mut v_bi_3572_: *mut crate::leanh::LeanObject,
    mut v_type_3573_: *mut crate::leanh::LeanObject,
    mut v_k_3574_: *mut crate::leanh::LeanObject,
    mut v_kind_3575_: *mut crate::leanh::LeanObject,
    mut v___y_3576_: *mut crate::leanh::LeanObject,
    mut v___y_3577_: *mut crate::leanh::LeanObject,
    mut v___y_3578_: *mut crate::leanh::LeanObject,
    mut v___y_3579_: *mut crate::leanh::LeanObject,
    mut v___y_3580_: *mut crate::leanh::LeanObject,
    mut v___y_3581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3582_: u8 = 0;
    let mut v_kind_boxed_3583_: u8 = 0;
    let mut v_res_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3582_ = (crate::leanh::lean_unbox(v_bi_3572_) as u8);
    v_kind_boxed_3583_ = (crate::leanh::lean_unbox(v_kind_3575_) as u8);
    v_res_3584_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_name_3571_, v_bi_boxed_3582_, v_type_3573_, v_k_3574_, v_kind_boxed_3583_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
    crate::leanh::lean_dec(v___y_3580_);
    crate::leanh::lean_dec_ref(v___y_3579_);
    crate::leanh::lean_dec(v___y_3578_);
    crate::leanh::lean_dec_ref(v___y_3577_);
    crate::leanh::lean_dec(v___y_3576_);
    return v_res_3584_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(
    mut v_00_u03b1_3585_: *mut crate::leanh::LeanObject,
    mut v_name_3586_: *mut crate::leanh::LeanObject,
    mut v_bi_3587_: u8,
    mut v_type_3588_: *mut crate::leanh::LeanObject,
    mut v_k_3589_: *mut crate::leanh::LeanObject,
    mut v_kind_3590_: u8,
    mut v___y_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
    mut v___y_3593_: *mut crate::leanh::LeanObject,
    mut v___y_3594_: *mut crate::leanh::LeanObject,
    mut v___y_3595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3597_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_name_3586_, v_bi_3587_, v_type_3588_, v_k_3589_, v_kind_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
    return v___x_3597_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___boxed(
    mut v_00_u03b1_3598_: *mut crate::leanh::LeanObject,
    mut v_name_3599_: *mut crate::leanh::LeanObject,
    mut v_bi_3600_: *mut crate::leanh::LeanObject,
    mut v_type_3601_: *mut crate::leanh::LeanObject,
    mut v_k_3602_: *mut crate::leanh::LeanObject,
    mut v_kind_3603_: *mut crate::leanh::LeanObject,
    mut v___y_3604_: *mut crate::leanh::LeanObject,
    mut v___y_3605_: *mut crate::leanh::LeanObject,
    mut v___y_3606_: *mut crate::leanh::LeanObject,
    mut v___y_3607_: *mut crate::leanh::LeanObject,
    mut v___y_3608_: *mut crate::leanh::LeanObject,
    mut v___y_3609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3610_: u8 = 0;
    let mut v_kind_boxed_3611_: u8 = 0;
    let mut v_res_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3610_ = (crate::leanh::lean_unbox(v_bi_3600_) as u8);
    v_kind_boxed_3611_ = (crate::leanh::lean_unbox(v_kind_3603_) as u8);
    v_res_3612_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(v_00_u03b1_3598_, v_name_3599_, v_bi_boxed_3610_, v_type_3601_, v_k_3602_, v_kind_boxed_3611_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
    crate::leanh::lean_dec(v___y_3608_);
    crate::leanh::lean_dec_ref(v___y_3607_);
    crate::leanh::lean_dec(v___y_3606_);
    crate::leanh::lean_dec_ref(v___y_3605_);
    crate::leanh::lean_dec(v___y_3604_);
    return v_res_3612_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(
    mut v_msgData_3613_: *mut crate::leanh::LeanObject,
    mut v___y_3614_: *mut crate::leanh::LeanObject,
    mut v___y_3615_: *mut crate::leanh::LeanObject,
    mut v___y_3616_: *mut crate::leanh::LeanObject,
    mut v___y_3617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3619_ = lean_st_ref_get(v___y_3617_);
    v_env_3620_ = crate::leanh::lean_ctor_get(v___x_3619_, 0);
    crate::leanh::lean_inc_ref(v_env_3620_);
    crate::leanh::lean_dec(v___x_3619_);
    v___x_3621_ = lean_st_ref_get(v___y_3615_);
    v_mctx_3622_ = crate::leanh::lean_ctor_get(v___x_3621_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3622_);
    crate::leanh::lean_dec(v___x_3621_);
    v_lctx_3623_ = crate::leanh::lean_ctor_get(v___y_3614_, 2);
    v_options_3624_ = crate::leanh::lean_ctor_get(v___y_3616_, 2);
    crate::leanh::lean_inc_ref(v_options_3624_);
    crate::leanh::lean_inc_ref(v_lctx_3623_);
    v___x_3625_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3625_, 0, v_env_3620_);
    crate::leanh::lean_ctor_set(v___x_3625_, 1, v_mctx_3622_);
    crate::leanh::lean_ctor_set(v___x_3625_, 2, v_lctx_3623_);
    crate::leanh::lean_ctor_set(v___x_3625_, 3, v_options_3624_);
    v___x_3626_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3626_, 0, v___x_3625_);
    crate::leanh::lean_ctor_set(v___x_3626_, 1, v_msgData_3613_);
    v___x_3627_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3627_, 0, v___x_3626_);
    return v___x_3627_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0___boxed(
    mut v_msgData_3628_: *mut crate::leanh::LeanObject,
    mut v___y_3629_: *mut crate::leanh::LeanObject,
    mut v___y_3630_: *mut crate::leanh::LeanObject,
    mut v___y_3631_: *mut crate::leanh::LeanObject,
    mut v___y_3632_: *mut crate::leanh::LeanObject,
    mut v___y_3633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3634_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msgData_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
    crate::leanh::lean_dec(v___y_3632_);
    crate::leanh::lean_dec_ref(v___y_3631_);
    crate::leanh::lean_dec(v___y_3630_);
    crate::leanh::lean_dec_ref(v___y_3629_);
    return v_res_3634_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(
    mut v_msg_3635_: *mut crate::leanh::LeanObject,
    mut v___y_3636_: *mut crate::leanh::LeanObject,
    mut v___y_3637_: *mut crate::leanh::LeanObject,
    mut v___y_3638_: *mut crate::leanh::LeanObject,
    mut v___y_3639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3646_: u8 = 0;
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3641_ = crate::leanh::lean_ctor_get(v___y_3638_, 5);
                v___x_3642_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
                v_a_3643_ = crate::leanh::lean_ctor_get(v___x_3642_, 0);
                v_isSharedCheck_3651_ = (!crate::leanh::lean_is_exclusive(v___x_3642_)) as u8;
                if v_isSharedCheck_3651_ == 0 {
                    v___x_3645_ = v___x_3642_;
                    v_isShared_3646_ = v_isSharedCheck_3651_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3643_);
                    crate::leanh::lean_dec(v___x_3642_);
                    v___x_3645_ = crate::leanh::lean_box(0);
                    v_isShared_3646_ = v_isSharedCheck_3651_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3641_);
                v___x_3647_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3647_, 0, v_ref_3641_);
                crate::leanh::lean_ctor_set(v___x_3647_, 1, v_a_3643_);
                if v_isShared_3646_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3645_, 1);
                    crate::leanh::lean_ctor_set(v___x_3645_, 0, v___x_3647_);
                    v___x_3649_ = v___x_3645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
                    v___x_3649_ = v_reuseFailAlloc_3650_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg___boxed(
    mut v_msg_3652_: *mut crate::leanh::LeanObject,
    mut v___y_3653_: *mut crate::leanh::LeanObject,
    mut v___y_3654_: *mut crate::leanh::LeanObject,
    mut v___y_3655_: *mut crate::leanh::LeanObject,
    mut v___y_3656_: *mut crate::leanh::LeanObject,
    mut v___y_3657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3658_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
    crate::leanh::lean_dec(v___y_3656_);
    crate::leanh::lean_dec_ref(v___y_3655_);
    crate::leanh::lean_dec(v___y_3654_);
    crate::leanh::lean_dec_ref(v___y_3653_);
    return v_res_3658_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(
    mut v_a_3659_: *mut crate::leanh::LeanObject,
    mut v_x_3660_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3661_: u8 = 0;
    let mut v_key_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3660_) == 0 {
                    v___x_3661_ = 0;
                    return v___x_3661_;
                } else {
                    v_key_3662_ = crate::leanh::lean_ctor_get(v_x_3660_, 0);
                    v_tail_3663_ = crate::leanh::lean_ctor_get(v_x_3660_, 2);
                    v___x_3664_ = lean_expr_eqv(v_key_3662_, v_a_3659_);
                    if v___x_3664_ == 0 {
                        v_x_3660_ = v_tail_3663_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3664_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg___boxed(
    mut v_a_3666_: *mut crate::leanh::LeanObject,
    mut v_x_3667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3668_: u8 = 0;
    let mut v_r_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3668_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_3666_, v_x_3667_);
    crate::leanh::lean_dec(v_x_3667_);
    crate::leanh::lean_dec_ref(v_a_3666_);
    v_r_3669_ = crate::leanh::lean_box((v_res_3668_) as usize);
    return v_r_3669_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(
    mut v_x_3670_: *mut crate::leanh::LeanObject,
    mut v_x_3671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3677_: u8 = 0;
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: u64 = 0;
    let mut v___x_3680_: u64 = 0;
    let mut v___x_3681_: u64 = 0;
    let mut v_fold_3682_: u64 = 0;
    let mut v___x_3683_: u64 = 0;
    let mut v___x_3684_: u64 = 0;
    let mut v___x_3685_: u64 = 0;
    let mut v___x_3686_: usize = 0;
    let mut v___x_3687_: usize = 0;
    let mut v___x_3688_: usize = 0;
    let mut v___x_3689_: usize = 0;
    let mut v___x_3690_: usize = 0;
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3671_) == 0 {
                    return v_x_3670_;
                } else {
                    v_key_3672_ = crate::leanh::lean_ctor_get(v_x_3671_, 0);
                    v_value_3673_ = crate::leanh::lean_ctor_get(v_x_3671_, 1);
                    v_tail_3674_ = crate::leanh::lean_ctor_get(v_x_3671_, 2);
                    v_isSharedCheck_3697_ = (!crate::leanh::lean_is_exclusive(v_x_3671_)) as u8;
                    if v_isSharedCheck_3697_ == 0 {
                        v___x_3676_ = v_x_3671_;
                        v_isShared_3677_ = v_isSharedCheck_3697_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3674_);
                        crate::leanh::lean_inc(v_value_3673_);
                        crate::leanh::lean_inc(v_key_3672_);
                        crate::leanh::lean_dec(v_x_3671_);
                        v___x_3676_ = crate::leanh::lean_box(0);
                        v_isShared_3677_ = v_isSharedCheck_3697_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3678_ = lean_array_get_size(v_x_3670_);
                v___x_3679_ = l_Lean_Expr_hash(v_key_3672_);
                v___x_3680_ = 32u64;
                v___x_3681_ = lean_uint64_shift_right(v___x_3679_, v___x_3680_);
                v_fold_3682_ = lean_uint64_xor(v___x_3679_, v___x_3681_);
                v___x_3683_ = 16u64;
                v___x_3684_ = lean_uint64_shift_right(v_fold_3682_, v___x_3683_);
                v___x_3685_ = lean_uint64_xor(v_fold_3682_, v___x_3684_);
                v___x_3686_ = lean_uint64_to_usize(v___x_3685_);
                v___x_3687_ = lean_usize_of_nat(v___x_3678_);
                v___x_3688_ = 1usize;
                v___x_3689_ = lean_usize_sub(v___x_3687_, v___x_3688_);
                v___x_3690_ = lean_usize_land(v___x_3686_, v___x_3689_);
                v___x_3691_ = lean_array_uget_borrowed(v_x_3670_, v___x_3690_);
                crate::leanh::lean_inc(v___x_3691_);
                if v_isShared_3677_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3676_, 2, v___x_3691_);
                    v___x_3693_ = v___x_3676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3696_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_key_3672_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_value_3673_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3696_, 2, v___x_3691_);
                    v___x_3693_ = v_reuseFailAlloc_3696_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3694_ = lean_array_uset(v_x_3670_, v___x_3690_, v___x_3693_);
                v_x_3670_ = v___x_3694_;
                v_x_3671_ = v_tail_3674_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(
    mut v_i_3698_: *mut crate::leanh::LeanObject,
    mut v_source_3699_: *mut crate::leanh::LeanObject,
    mut v_target_3700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: u8 = 0;
    let mut v_es_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3701_ = lean_array_get_size(v_source_3699_);
                v___x_3702_ = lean_nat_dec_lt(v_i_3698_, v___x_3701_);
                if v___x_3702_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3699_);
                    crate::leanh::lean_dec(v_i_3698_);
                    return v_target_3700_;
                } else {
                    v_es_3703_ = lean_array_fget(v_source_3699_, v_i_3698_);
                    v___x_3704_ = crate::leanh::lean_box(0);
                    v_source_3705_ = lean_array_fset(v_source_3699_, v_i_3698_, v___x_3704_);
                    v_target_3706_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(v_target_3700_, v_es_3703_);
                    v___x_3707_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3708_ = lean_nat_add(v_i_3698_, v___x_3707_);
                    crate::leanh::lean_dec(v_i_3698_);
                    v_i_3698_ = v___x_3708_;
                    v_source_3699_ = v_source_3705_;
                    v_target_3700_ = v_target_3706_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(
    mut v_data_3710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3711_ = lean_array_get_size(v_data_3710_);
    v___x_3712_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3713_ = lean_nat_mul(v___x_3711_, v___x_3712_);
    v___x_3714_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3715_ = crate::leanh::lean_box(0);
    v___x_3716_ = lean_mk_array(v_nbuckets_3713_, v___x_3715_);
    v___x_3717_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(v___x_3714_, v_data_3710_, v___x_3716_);
    return v___x_3717_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(
    mut v_a_3718_: *mut crate::leanh::LeanObject,
    mut v_b_3719_: *mut crate::leanh::LeanObject,
    mut v_x_3720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3726_: u8 = 0;
    let mut v___x_3727_: u8 = 0;
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3720_) == 0 {
                    crate::leanh::lean_dec(v_b_3719_);
                    crate::leanh::lean_dec_ref(v_a_3718_);
                    return v_x_3720_;
                } else {
                    v_key_3721_ = crate::leanh::lean_ctor_get(v_x_3720_, 0);
                    v_value_3722_ = crate::leanh::lean_ctor_get(v_x_3720_, 1);
                    v_tail_3723_ = crate::leanh::lean_ctor_get(v_x_3720_, 2);
                    v_isSharedCheck_3735_ = (!crate::leanh::lean_is_exclusive(v_x_3720_)) as u8;
                    if v_isSharedCheck_3735_ == 0 {
                        v___x_3725_ = v_x_3720_;
                        v_isShared_3726_ = v_isSharedCheck_3735_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3723_);
                        crate::leanh::lean_inc(v_value_3722_);
                        crate::leanh::lean_inc(v_key_3721_);
                        crate::leanh::lean_dec(v_x_3720_);
                        v___x_3725_ = crate::leanh::lean_box(0);
                        v_isShared_3726_ = v_isSharedCheck_3735_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3727_ = lean_expr_eqv(v_key_3721_, v_a_3718_);
                if v___x_3727_ == 0 {
                    v___x_3728_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_3718_, v_b_3719_, v_tail_3723_);
                    if v_isShared_3726_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3725_, 2, v___x_3728_);
                        v___x_3730_ = v___x_3725_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3731_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_key_3721_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_value_3722_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 2, v___x_3728_);
                        v___x_3730_ = v_reuseFailAlloc_3731_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3722_);
                    crate::leanh::lean_dec(v_key_3721_);
                    if v_isShared_3726_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3725_, 1, v_b_3719_);
                        crate::leanh::lean_ctor_set(v___x_3725_, 0, v_a_3718_);
                        v___x_3733_ = v___x_3725_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3734_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3718_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_b_3719_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_tail_3723_);
                        v___x_3733_ = v_reuseFailAlloc_3734_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3730_;
            }
            3 => {
                return v___x_3733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(
    mut v_m_3736_: *mut crate::leanh::LeanObject,
    mut v_a_3737_: *mut crate::leanh::LeanObject,
    mut v_b_3738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: u64 = 0;
    let mut v___x_3746_: u64 = 0;
    let mut v___x_3747_: u64 = 0;
    let mut v_fold_3748_: u64 = 0;
    let mut v___x_3749_: u64 = 0;
    let mut v___x_3750_: u64 = 0;
    let mut v___x_3751_: u64 = 0;
    let mut v___x_3752_: usize = 0;
    let mut v___x_3753_: usize = 0;
    let mut v___x_3754_: usize = 0;
    let mut v___x_3755_: usize = 0;
    let mut v___x_3756_: usize = 0;
    let mut v_bkt_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: u8 = 0;
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: u8 = 0;
    let mut v_val_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3739_ = crate::leanh::lean_ctor_get(v_m_3736_, 0);
                v_buckets_3740_ = crate::leanh::lean_ctor_get(v_m_3736_, 1);
                v_isSharedCheck_3783_ = (!crate::leanh::lean_is_exclusive(v_m_3736_)) as u8;
                if v_isSharedCheck_3783_ == 0 {
                    v___x_3742_ = v_m_3736_;
                    v_isShared_3743_ = v_isSharedCheck_3783_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3740_);
                    crate::leanh::lean_inc(v_size_3739_);
                    crate::leanh::lean_dec(v_m_3736_);
                    v___x_3742_ = crate::leanh::lean_box(0);
                    v_isShared_3743_ = v_isSharedCheck_3783_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3744_ = lean_array_get_size(v_buckets_3740_);
                v___x_3745_ = l_Lean_Expr_hash(v_a_3737_);
                v___x_3746_ = 32u64;
                v___x_3747_ = lean_uint64_shift_right(v___x_3745_, v___x_3746_);
                v_fold_3748_ = lean_uint64_xor(v___x_3745_, v___x_3747_);
                v___x_3749_ = 16u64;
                v___x_3750_ = lean_uint64_shift_right(v_fold_3748_, v___x_3749_);
                v___x_3751_ = lean_uint64_xor(v_fold_3748_, v___x_3750_);
                v___x_3752_ = lean_uint64_to_usize(v___x_3751_);
                v___x_3753_ = lean_usize_of_nat(v___x_3744_);
                v___x_3754_ = 1usize;
                v___x_3755_ = lean_usize_sub(v___x_3753_, v___x_3754_);
                v___x_3756_ = lean_usize_land(v___x_3752_, v___x_3755_);
                v_bkt_3757_ = lean_array_uget_borrowed(v_buckets_3740_, v___x_3756_);
                v___x_3758_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_3737_, v_bkt_3757_);
                if v___x_3758_ == 0 {
                    v___x_3759_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3760_ = lean_nat_add(v_size_3739_, v___x_3759_);
                    crate::leanh::lean_dec(v_size_3739_);
                    crate::leanh::lean_inc(v_bkt_3757_);
                    v___x_3761_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3761_, 0, v_a_3737_);
                    crate::leanh::lean_ctor_set(v___x_3761_, 1, v_b_3738_);
                    crate::leanh::lean_ctor_set(v___x_3761_, 2, v_bkt_3757_);
                    v_buckets_x27_3762_ =
                        lean_array_uset(v_buckets_3740_, v___x_3756_, v___x_3761_);
                    v___x_3763_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3764_ = lean_nat_mul(v_size_x27_3760_, v___x_3763_);
                    v___x_3765_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3766_ = lean_nat_div(v___x_3764_, v___x_3765_);
                    crate::leanh::lean_dec(v___x_3764_);
                    v___x_3767_ = lean_array_get_size(v_buckets_x27_3762_);
                    v___x_3768_ = lean_nat_dec_le(v___x_3766_, v___x_3767_);
                    crate::leanh::lean_dec(v___x_3766_);
                    if v___x_3768_ == 0 {
                        v_val_3769_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_buckets_x27_3762_);
                        if v_isShared_3743_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3742_, 1, v_val_3769_);
                            crate::leanh::lean_ctor_set(v___x_3742_, 0, v_size_x27_3760_);
                            v___x_3771_ = v___x_3742_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3772_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3772_,
                                0,
                                v_size_x27_3760_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_val_3769_);
                            v___x_3771_ = v_reuseFailAlloc_3772_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3743_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3742_, 1, v_buckets_x27_3762_);
                            crate::leanh::lean_ctor_set(v___x_3742_, 0, v_size_x27_3760_);
                            v___x_3774_ = v___x_3742_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3775_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3775_,
                                0,
                                v_size_x27_3760_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3775_,
                                1,
                                v_buckets_x27_3762_,
                            );
                            v___x_3774_ = v_reuseFailAlloc_3775_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3757_);
                    v___x_3776_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3777_ =
                        lean_array_uset(v_buckets_3740_, v___x_3756_, v___x_3776_);
                    v___x_3778_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_3737_, v_b_3738_, v_bkt_3757_);
                    v___x_3779_ = lean_array_uset(v_buckets_x27_3777_, v___x_3756_, v___x_3778_);
                    if v_isShared_3743_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3742_, 1, v___x_3779_);
                        v___x_3781_ = v___x_3742_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3782_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_size_3739_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 1, v___x_3779_);
                        v___x_3781_ = v_reuseFailAlloc_3782_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3771_;
            }
            3 => {
                return v___x_3774_;
            }
            4 => {
                return v___x_3781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(
    mut v_a_3784_: *mut crate::leanh::LeanObject,
    mut v_x_3785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: u8 = 0;
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3785_) == 0 {
                    v___x_3786_ = crate::leanh::lean_box(0);
                    return v___x_3786_;
                } else {
                    v_key_3787_ = crate::leanh::lean_ctor_get(v_x_3785_, 0);
                    v_value_3788_ = crate::leanh::lean_ctor_get(v_x_3785_, 1);
                    v_tail_3789_ = crate::leanh::lean_ctor_get(v_x_3785_, 2);
                    v___x_3790_ = lean_expr_eqv(v_key_3787_, v_a_3784_);
                    if v___x_3790_ == 0 {
                        v_x_3785_ = v_tail_3789_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3788_);
                        v___x_3792_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3792_, 0, v_value_3788_);
                        return v___x_3792_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg___boxed(
    mut v_a_3793_: *mut crate::leanh::LeanObject,
    mut v_x_3794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3795_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_3793_, v_x_3794_);
    crate::leanh::lean_dec(v_x_3794_);
    crate::leanh::lean_dec_ref(v_a_3793_);
    return v_res_3795_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(
    mut v_m_3796_: *mut crate::leanh::LeanObject,
    mut v_a_3797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u64 = 0;
    let mut v___x_3801_: u64 = 0;
    let mut v___x_3802_: u64 = 0;
    let mut v_fold_3803_: u64 = 0;
    let mut v___x_3804_: u64 = 0;
    let mut v___x_3805_: u64 = 0;
    let mut v___x_3806_: u64 = 0;
    let mut v___x_3807_: usize = 0;
    let mut v___x_3808_: usize = 0;
    let mut v___x_3809_: usize = 0;
    let mut v___x_3810_: usize = 0;
    let mut v___x_3811_: usize = 0;
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3798_ = crate::leanh::lean_ctor_get(v_m_3796_, 1);
    v___x_3799_ = lean_array_get_size(v_buckets_3798_);
    v___x_3800_ = l_Lean_Expr_hash(v_a_3797_);
    v___x_3801_ = 32u64;
    v___x_3802_ = lean_uint64_shift_right(v___x_3800_, v___x_3801_);
    v_fold_3803_ = lean_uint64_xor(v___x_3800_, v___x_3802_);
    v___x_3804_ = 16u64;
    v___x_3805_ = lean_uint64_shift_right(v_fold_3803_, v___x_3804_);
    v___x_3806_ = lean_uint64_xor(v_fold_3803_, v___x_3805_);
    v___x_3807_ = lean_uint64_to_usize(v___x_3806_);
    v___x_3808_ = lean_usize_of_nat(v___x_3799_);
    v___x_3809_ = 1usize;
    v___x_3810_ = lean_usize_sub(v___x_3808_, v___x_3809_);
    v___x_3811_ = lean_usize_land(v___x_3807_, v___x_3810_);
    v___x_3812_ = lean_array_uget_borrowed(v_buckets_3798_, v___x_3811_);
    v___x_3813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_3797_, v___x_3812_);
    return v___x_3813_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg___boxed(
    mut v_m_3814_: *mut crate::leanh::LeanObject,
    mut v_a_3815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3816_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_3814_, v_a_3815_);
    crate::leanh::lean_dec_ref(v_a_3815_);
    crate::leanh::lean_dec_ref(v_m_3814_);
    return v_res_3816_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3817_ = crate::leanh::lean_box(0);
    v_dummy_3818_ = l_Lean_Expr_sort___override(v___x_3817_);
    return v_dummy_3818_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3820_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0;
    v___x_3821_ = l_Lean_stringToMessageData(v___x_3820_);
    return v___x_3821_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(
    mut v_args_3822_: *mut crate::leanh::LeanObject,
    mut v_a_3823_: *mut crate::leanh::LeanObject,
    mut v_snd_3824_: *mut crate::leanh::LeanObject,
    mut v_____r_3825_: *mut crate::leanh::LeanObject,
    mut v_fty_3826_: *mut crate::leanh::LeanObject,
    mut v_j_3827_: *mut crate::leanh::LeanObject,
    mut v___y_3828_: *mut crate::leanh::LeanObject,
    mut v___y_3829_: *mut crate::leanh::LeanObject,
    mut v___y_3830_: *mut crate::leanh::LeanObject,
    mut v___y_3831_: *mut crate::leanh::LeanObject,
    mut v___y_3832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_body_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3835_: u8 = 0;
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3838_: u8 = 0;
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3853_: u8 = 0;
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut v_a_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3865_: u8 = 0;
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3869_: u8 = 0;
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3876_: u8 = 0;
    let mut v_a_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3880_: u8 = 0;
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3884_: u8 = 0;
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: u8 = 0;
    let mut v_a_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v___x_3897_: u8 = 0;
    let mut v___x_3898_: u8 = 0;
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3903_: u8 = 0;
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut v_unused_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3915_: u8 = 0;
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_fty_3826_) == 7 {
                    v_body_3834_ = crate::leanh::lean_ctor_get(v_fty_3826_, 2);
                    crate::leanh::lean_inc_ref(v_body_3834_);
                    v_binderInfo_3835_ = crate::leanh::lean_ctor_get_uint8(
                        v_fty_3826_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_fty_3826_, 3);
                    v___x_3836_ = lean_array_fget_borrowed(v_args_3822_, v_a_3823_);
                    v___x_3897_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_3835_);
                    if v___x_3897_ == 0 {
                        v___x_3898_ = l_Lean_Expr_isSort(v___x_3836_);
                        if v___x_3898_ == 0 {
                            state = 10;
                            continue;
                        } else {
                            if v___x_3897_ == 0 {
                                v_a_3838_ = v___x_3897_;
                                state = 1;
                                continue;
                            } else {
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        v_a_3838_ = v___x_3897_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3899_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1);
                    v___x_3900_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v___x_3899_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
                    if crate::leanh::lean_obj_tag(v___x_3900_) == 0 {
                        v_isSharedCheck_3910_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3900_)) as u8;
                        if v_isSharedCheck_3910_ == 0 {
                            v_unused_3911_ = crate::leanh::lean_ctor_get(v___x_3900_, 0);
                            crate::leanh::lean_dec(v_unused_3911_);
                            v___x_3902_ = v___x_3900_;
                            v_isShared_3903_ = v_isSharedCheck_3910_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3900_);
                            v___x_3902_ = crate::leanh::lean_box(0);
                            v_isShared_3903_ = v_isSharedCheck_3910_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_fty_3826_);
                        crate::leanh::lean_dec(v_snd_3824_);
                        v_a_3912_ = crate::leanh::lean_ctor_get(v___x_3900_, 0);
                        v_isSharedCheck_3919_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3900_)) as u8;
                        if v_isSharedCheck_3919_ == 0 {
                            v___x_3914_ = v___x_3900_;
                            v_isShared_3915_ = v_isSharedCheck_3919_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3912_);
                            crate::leanh::lean_dec(v___x_3900_);
                            v___x_3914_ = crate::leanh::lean_box(0);
                            v_isShared_3915_ = v_isSharedCheck_3919_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_a_3838_ == 0 {
                    crate::leanh::lean_inc(v_j_3827_);
                    v___x_3839_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3839_, 0, v_j_3827_);
                    crate::leanh::lean_ctor_set(v___x_3839_, 1, v_snd_3824_);
                    v___x_3840_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3840_, 0, v_body_3834_);
                    crate::leanh::lean_ctor_set(v___x_3840_, 1, v___x_3839_);
                    v___x_3841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3841_, 0, v___x_3840_);
                    v___x_3842_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3842_, 0, v___x_3841_);
                    return v___x_3842_;
                } else {
                    crate::leanh::lean_inc(v___x_3836_);
                    v___x_3843_ = l_Lean_Meta_isProof(
                        v___x_3836_,
                        v___y_3829_,
                        v___y_3830_,
                        v___y_3831_,
                        v___y_3832_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3843_) == 0 {
                        v_a_3844_ = crate::leanh::lean_ctor_get(v___x_3843_, 0);
                        v_isSharedCheck_3876_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3843_)) as u8;
                        if v_isSharedCheck_3876_ == 0 {
                            v___x_3846_ = v___x_3843_;
                            v_isShared_3847_ = v_isSharedCheck_3876_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3844_);
                            crate::leanh::lean_dec(v___x_3843_);
                            v___x_3846_ = crate::leanh::lean_box(0);
                            v_isShared_3847_ = v_isSharedCheck_3876_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_3834_);
                        crate::leanh::lean_dec(v_snd_3824_);
                        v_a_3877_ = crate::leanh::lean_ctor_get(v___x_3843_, 0);
                        v_isSharedCheck_3884_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3843_)) as u8;
                        if v_isSharedCheck_3884_ == 0 {
                            v___x_3879_ = v___x_3843_;
                            v_isShared_3880_ = v_isSharedCheck_3884_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3877_);
                            crate::leanh::lean_dec(v___x_3843_);
                            v___x_3879_ = crate::leanh::lean_box(0);
                            v_isShared_3880_ = v_isSharedCheck_3884_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3848_ = (crate::leanh::lean_unbox(v_a_3844_) as u8);
                crate::leanh::lean_dec(v_a_3844_);
                if v___x_3848_ == 0 {
                    crate::leanh::lean_del_object(v___x_3846_);
                    crate::leanh::lean_inc(v___x_3836_);
                    v___x_3849_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_3836_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
                    if crate::leanh::lean_obj_tag(v___x_3849_) == 0 {
                        v_a_3850_ = crate::leanh::lean_ctor_get(v___x_3849_, 0);
                        v_isSharedCheck_3861_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3849_)) as u8;
                        if v_isSharedCheck_3861_ == 0 {
                            v___x_3852_ = v___x_3849_;
                            v_isShared_3853_ = v_isSharedCheck_3861_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3850_);
                            crate::leanh::lean_dec(v___x_3849_);
                            v___x_3852_ = crate::leanh::lean_box(0);
                            v_isShared_3853_ = v_isSharedCheck_3861_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_3834_);
                        crate::leanh::lean_dec(v_snd_3824_);
                        v_a_3862_ = crate::leanh::lean_ctor_get(v___x_3849_, 0);
                        v_isSharedCheck_3869_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3849_)) as u8;
                        if v_isSharedCheck_3869_ == 0 {
                            v___x_3864_ = v___x_3849_;
                            v_isShared_3865_ = v_isSharedCheck_3869_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3862_);
                            crate::leanh::lean_dec(v___x_3849_);
                            v___x_3864_ = crate::leanh::lean_box(0);
                            v_isShared_3865_ = v_isSharedCheck_3869_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_j_3827_);
                    v___x_3870_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3870_, 0, v_j_3827_);
                    crate::leanh::lean_ctor_set(v___x_3870_, 1, v_snd_3824_);
                    v___x_3871_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3871_, 0, v_body_3834_);
                    crate::leanh::lean_ctor_set(v___x_3871_, 1, v___x_3870_);
                    v___x_3872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3872_, 0, v___x_3871_);
                    if v_isShared_3847_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3846_, 0, v___x_3872_);
                        v___x_3874_ = v___x_3846_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
                        v___x_3874_ = v_reuseFailAlloc_3875_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3854_ = l_Lean_Expr_app___override(v_snd_3824_, v_a_3850_);
                crate::leanh::lean_inc(v_j_3827_);
                v___x_3855_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3855_, 0, v_j_3827_);
                crate::leanh::lean_ctor_set(v___x_3855_, 1, v___x_3854_);
                v___x_3856_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3856_, 0, v_body_3834_);
                crate::leanh::lean_ctor_set(v___x_3856_, 1, v___x_3855_);
                v___x_3857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3857_, 0, v___x_3856_);
                if v_isShared_3853_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3852_, 0, v___x_3857_);
                    v___x_3859_ = v___x_3852_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3857_);
                    v___x_3859_ = v_reuseFailAlloc_3860_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3859_;
            }
            5 => {
                if v_isShared_3865_ == 0 {
                    v___x_3867_ = v___x_3864_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3868_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
                    v___x_3867_ = v_reuseFailAlloc_3868_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3867_;
            }
            7 => {
                return v___x_3874_;
            }
            8 => {
                if v_isShared_3880_ == 0 {
                    v___x_3882_ = v___x_3879_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3883_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
                    v___x_3882_ = v_reuseFailAlloc_3883_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3882_;
            }
            10 => {
                crate::leanh::lean_inc(v___x_3836_);
                v___x_3886_ = l_Lean_Meta_isTypeFormer(
                    v___x_3836_,
                    v___y_3829_,
                    v___y_3830_,
                    v___y_3831_,
                    v___y_3832_,
                );
                if crate::leanh::lean_obj_tag(v___x_3886_) == 0 {
                    v_a_3887_ = crate::leanh::lean_ctor_get(v___x_3886_, 0);
                    crate::leanh::lean_inc(v_a_3887_);
                    crate::leanh::lean_dec_ref_known(v___x_3886_, 1);
                    v___x_3888_ = (crate::leanh::lean_unbox(v_a_3887_) as u8);
                    crate::leanh::lean_dec(v_a_3887_);
                    v_a_3838_ = v___x_3888_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_body_3834_);
                    crate::leanh::lean_dec(v_snd_3824_);
                    v_a_3889_ = crate::leanh::lean_ctor_get(v___x_3886_, 0);
                    v_isSharedCheck_3896_ = (!crate::leanh::lean_is_exclusive(v___x_3886_)) as u8;
                    if v_isSharedCheck_3896_ == 0 {
                        v___x_3891_ = v___x_3886_;
                        v_isShared_3892_ = v_isSharedCheck_3896_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3889_);
                        crate::leanh::lean_dec(v___x_3886_);
                        v___x_3891_ = crate::leanh::lean_box(0);
                        v_isShared_3892_ = v_isSharedCheck_3896_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_3892_ == 0 {
                    v___x_3894_ = v___x_3891_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3895_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
                    v___x_3894_ = v_reuseFailAlloc_3895_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3894_;
            }
            13 => {
                crate::leanh::lean_inc(v_j_3827_);
                v___x_3904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3904_, 0, v_j_3827_);
                crate::leanh::lean_ctor_set(v___x_3904_, 1, v_snd_3824_);
                v___x_3905_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3905_, 0, v_fty_3826_);
                crate::leanh::lean_ctor_set(v___x_3905_, 1, v___x_3904_);
                v___x_3906_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3906_, 0, v___x_3905_);
                if v_isShared_3903_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3902_, 0, v___x_3906_);
                    v___x_3908_ = v___x_3902_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3909_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3906_);
                    v___x_3908_ = v_reuseFailAlloc_3909_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3908_;
            }
            15 => {
                if v_isShared_3915_ == 0 {
                    v___x_3917_ = v___x_3914_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3918_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
                    v___x_3917_ = v_reuseFailAlloc_3918_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___closed__0()
-> u64 {
    let mut v___x_3920_: u8 = 0;
    let mut v___x_3921_: u64 = 0;
    v___x_3920_ = 0;
    v___x_3921_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3920_);
    return v___x_3921_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(
    mut v_upperBound_3922_: *mut crate::leanh::LeanObject,
    mut v_args_3923_: *mut crate::leanh::LeanObject,
    mut v_a_3924_: *mut crate::leanh::LeanObject,
    mut v_b_3925_: *mut crate::leanh::LeanObject,
    mut v___y_3926_: *mut crate::leanh::LeanObject,
    mut v___y_3927_: *mut crate::leanh::LeanObject,
    mut v___y_3928_: *mut crate::leanh::LeanObject,
    mut v___y_3929_: *mut crate::leanh::LeanObject,
    mut v___y_3930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3937_: u8 = 0;
    let mut v_a_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut v_a_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3950_: u8 = 0;
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut v___x_3955_: u8 = 0;
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3967_: u8 = 0;
    let mut v_ctxApprox_3968_: u8 = 0;
    let mut v_quasiPatternApprox_3969_: u8 = 0;
    let mut v_constApprox_3970_: u8 = 0;
    let mut v_isDefEqStuckEx_3971_: u8 = 0;
    let mut v_unificationHints_3972_: u8 = 0;
    let mut v_proofIrrelevance_3973_: u8 = 0;
    let mut v_assignSyntheticOpaque_3974_: u8 = 0;
    let mut v_offsetCnstrs_3975_: u8 = 0;
    let mut v_etaStruct_3976_: u8 = 0;
    let mut v_univApprox_3977_: u8 = 0;
    let mut v_iota_3978_: u8 = 0;
    let mut v_beta_3979_: u8 = 0;
    let mut v_proj_3980_: u8 = 0;
    let mut v_zeta_3981_: u8 = 0;
    let mut v_zetaDelta_3982_: u8 = 0;
    let mut v_zetaUnused_3983_: u8 = 0;
    let mut v_zetaHave_3984_: u8 = 0;
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3987_: u8 = 0;
    let mut v_trackZetaDelta_3988_: u8 = 0;
    let mut v_zetaDeltaSet_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3995_: u8 = 0;
    let mut v_inTypeClassResolution_3996_: u8 = 0;
    let mut v_cacheInferType_3997_: u8 = 0;
    let mut v___x_3998_: u8 = 0;
    let mut v_config_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: u64 = 0;
    let mut v___x_4002_: u64 = 0;
    let mut v___x_4003_: u64 = 0;
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: u64 = 0;
    let mut v___x_4006_: u64 = 0;
    let mut v_key_4007_: u64 = 0;
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4016_: u8 = 0;
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4020_: u8 = 0;
    let mut v_reuseFailAlloc_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4022_: u8 = 0;
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3955_ = lean_nat_dec_lt(v_a_3924_, v_upperBound_3922_);
                if v___x_3955_ == 0 {
                    crate::leanh::lean_dec(v_a_3924_);
                    v___x_3956_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3956_, 0, v_b_3925_);
                    return v___x_3956_;
                } else {
                    v_snd_3957_ = crate::leanh::lean_ctor_get(v_b_3925_, 1);
                    crate::leanh::lean_inc(v_snd_3957_);
                    v_fst_3958_ = crate::leanh::lean_ctor_get(v_b_3925_, 0);
                    crate::leanh::lean_inc(v_fst_3958_);
                    crate::leanh::lean_dec_ref(v_b_3925_);
                    v_fst_3959_ = crate::leanh::lean_ctor_get(v_snd_3957_, 0);
                    crate::leanh::lean_inc(v_fst_3959_);
                    v_snd_3960_ = crate::leanh::lean_ctor_get(v_snd_3957_, 1);
                    crate::leanh::lean_inc(v_snd_3960_);
                    crate::leanh::lean_dec(v_snd_3957_);
                    v___x_3965_ = l_Lean_Expr_isForall(v_fst_3958_);
                    if v___x_3965_ == 0 {
                        v___x_3966_ = l_Lean_Meta_Context_config(v___y_3927_);
                        v_foApprox_3967_ = crate::leanh::lean_ctor_get_uint8(v___x_3966_, 0 as u32);
                        v_ctxApprox_3968_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 1 as u32);
                        v_quasiPatternApprox_3969_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 2 as u32);
                        v_constApprox_3970_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 3 as u32);
                        v_isDefEqStuckEx_3971_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 4 as u32);
                        v_unificationHints_3972_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 5 as u32);
                        v_proofIrrelevance_3973_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 6 as u32);
                        v_assignSyntheticOpaque_3974_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 7 as u32);
                        v_offsetCnstrs_3975_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 8 as u32);
                        v_etaStruct_3976_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 10 as u32);
                        v_univApprox_3977_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 11 as u32);
                        v_iota_3978_ = crate::leanh::lean_ctor_get_uint8(v___x_3966_, 12 as u32);
                        v_beta_3979_ = crate::leanh::lean_ctor_get_uint8(v___x_3966_, 13 as u32);
                        v_proj_3980_ = crate::leanh::lean_ctor_get_uint8(v___x_3966_, 14 as u32);
                        v_zeta_3981_ = crate::leanh::lean_ctor_get_uint8(v___x_3966_, 15 as u32);
                        v_zetaDelta_3982_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 16 as u32);
                        v_zetaUnused_3983_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 17 as u32);
                        v_zetaHave_3984_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_3966_, 18 as u32);
                        v_isSharedCheck_4022_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3966_)) as u8;
                        if v_isSharedCheck_4022_ == 0 {
                            v___x_3986_ = v___x_3966_;
                            v_isShared_3987_ = v_isSharedCheck_4022_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3966_);
                            v___x_3986_ = crate::leanh::lean_box(0);
                            v_isShared_3987_ = v_isSharedCheck_4022_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___x_4023_ = crate::leanh::lean_box(0);
                        v___x_4024_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_args_3923_, v_a_3924_, v_snd_3960_, v___x_4023_, v_fst_3958_, v_fst_3959_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
                        crate::leanh::lean_dec(v_fst_3959_);
                        v___y_3933_ = v___x_4024_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_3933_) == 0 {
                    v_a_3934_ = crate::leanh::lean_ctor_get(v___y_3933_, 0);
                    v_isSharedCheck_3946_ = (!crate::leanh::lean_is_exclusive(v___y_3933_)) as u8;
                    if v_isSharedCheck_3946_ == 0 {
                        v___x_3936_ = v___y_3933_;
                        v_isShared_3937_ = v_isSharedCheck_3946_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3934_);
                        crate::leanh::lean_dec(v___y_3933_);
                        v___x_3936_ = crate::leanh::lean_box(0);
                        v_isShared_3937_ = v_isSharedCheck_3946_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3924_);
                    v_a_3947_ = crate::leanh::lean_ctor_get(v___y_3933_, 0);
                    v_isSharedCheck_3954_ = (!crate::leanh::lean_is_exclusive(v___y_3933_)) as u8;
                    if v_isSharedCheck_3954_ == 0 {
                        v___x_3949_ = v___y_3933_;
                        v_isShared_3950_ = v_isSharedCheck_3954_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3947_);
                        crate::leanh::lean_dec(v___y_3933_);
                        v___x_3949_ = crate::leanh::lean_box(0);
                        v_isShared_3950_ = v_isSharedCheck_3954_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3934_) == 0 {
                    crate::leanh::lean_dec(v_a_3924_);
                    v_a_3938_ = crate::leanh::lean_ctor_get(v_a_3934_, 0);
                    crate::leanh::lean_inc(v_a_3938_);
                    crate::leanh::lean_dec_ref_known(v_a_3934_, 1);
                    if v_isShared_3937_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3936_, 0, v_a_3938_);
                        v___x_3940_ = v___x_3936_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3941_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3938_);
                        v___x_3940_ = v_reuseFailAlloc_3941_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3936_);
                    v_a_3942_ = crate::leanh::lean_ctor_get(v_a_3934_, 0);
                    crate::leanh::lean_inc(v_a_3942_);
                    crate::leanh::lean_dec_ref_known(v_a_3934_, 1);
                    v___x_3943_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3944_ = lean_nat_add(v_a_3924_, v___x_3943_);
                    crate::leanh::lean_dec(v_a_3924_);
                    v_a_3924_ = v___x_3944_;
                    v_b_3925_ = v_a_3942_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_3940_;
            }
            4 => {
                if v_isShared_3950_ == 0 {
                    v___x_3952_ = v___x_3949_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3953_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
                    v___x_3952_ = v_reuseFailAlloc_3953_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3952_;
            }
            6 => {
                v___x_3963_ = crate::leanh::lean_box(0);
                v___x_3964_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_args_3923_, v_a_3924_, v_snd_3960_, v___x_3963_, v_a_3962_, v_a_3924_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
                v___y_3933_ = v___x_3964_;
                state = 1;
                continue;
            }
            7 => {
                v_trackZetaDelta_3988_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3927_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3989_ = crate::leanh::lean_ctor_get(v___y_3927_, 1);
                v_lctx_3990_ = crate::leanh::lean_ctor_get(v___y_3927_, 2);
                v_localInstances_3991_ = crate::leanh::lean_ctor_get(v___y_3927_, 3);
                v_defEqCtx_x3f_3992_ = crate::leanh::lean_ctor_get(v___y_3927_, 4);
                v_synthPendingDepth_3993_ = crate::leanh::lean_ctor_get(v___y_3927_, 5);
                v_canUnfold_x3f_3994_ = crate::leanh::lean_ctor_get(v___y_3927_, 6);
                v_univApprox_3995_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3927_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3996_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3927_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3997_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3927_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_3998_ = 0;
                if v_isShared_3987_ == 0 {
                    v_config_4000_ = v___x_3986_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4021_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        0 as u32,
                        v_foApprox_3967_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        1 as u32,
                        v_ctxApprox_3968_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        2 as u32,
                        v_quasiPatternApprox_3969_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        3 as u32,
                        v_constApprox_3970_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        4 as u32,
                        v_isDefEqStuckEx_3971_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        5 as u32,
                        v_unificationHints_3972_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        6 as u32,
                        v_proofIrrelevance_3973_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        7 as u32,
                        v_assignSyntheticOpaque_3974_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        8 as u32,
                        v_offsetCnstrs_3975_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        10 as u32,
                        v_etaStruct_3976_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        11 as u32,
                        v_univApprox_3977_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        12 as u32,
                        v_iota_3978_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        13 as u32,
                        v_beta_3979_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        14 as u32,
                        v_proj_3980_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        15 as u32,
                        v_zeta_3981_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        16 as u32,
                        v_zetaDelta_3982_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        17 as u32,
                        v_zetaUnused_3983_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4021_,
                        18 as u32,
                        v_zetaHave_3984_,
                    );
                    v_config_4000_ = v_reuseFailAlloc_4021_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_ctor_set_uint8(v_config_4000_, 9 as u32, v___x_3998_);
                v___x_4001_ = l_Lean_Meta_Context_configKey(v___y_3927_);
                v___x_4002_ = 3u64;
                v___x_4003_ = lean_uint64_shift_right(v___x_4001_, v___x_4002_);
                v___x_4004_ = lean_expr_instantiate_rev_range(
                    v_fst_3958_,
                    v_fst_3959_,
                    v_a_3924_,
                    v_args_3923_,
                );
                crate::leanh::lean_dec(v_fst_3959_);
                crate::leanh::lean_dec(v_fst_3958_);
                v___x_4005_ = lean_uint64_shift_left(v___x_4003_, v___x_4002_);
                v___x_4006_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___closed__0);
                v_key_4007_ = lean_uint64_lor(v___x_4005_, v___x_4006_);
                v___x_4008_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_4008_, 0, v_config_4000_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_4008_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_4007_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_3994_);
                crate::leanh::lean_inc(v_synthPendingDepth_3993_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_3992_);
                crate::leanh::lean_inc_ref(v_localInstances_3991_);
                crate::leanh::lean_inc_ref(v_lctx_3990_);
                crate::leanh::lean_inc(v_zetaDeltaSet_3989_);
                v___x_4009_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_4009_, 0, v___x_4008_);
                crate::leanh::lean_ctor_set(v___x_4009_, 1, v_zetaDeltaSet_3989_);
                crate::leanh::lean_ctor_set(v___x_4009_, 2, v_lctx_3990_);
                crate::leanh::lean_ctor_set(v___x_4009_, 3, v_localInstances_3991_);
                crate::leanh::lean_ctor_set(v___x_4009_, 4, v_defEqCtx_x3f_3992_);
                crate::leanh::lean_ctor_set(v___x_4009_, 5, v_synthPendingDepth_3993_);
                crate::leanh::lean_ctor_set(v___x_4009_, 6, v_canUnfold_x3f_3994_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4009_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3988_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4009_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3995_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4009_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3996_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4009_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3997_,
                );
                crate::leanh::lean_inc(v___y_3930_);
                crate::leanh::lean_inc_ref(v___y_3929_);
                crate::leanh::lean_inc(v___y_3928_);
                v___x_4010_ = lean_whnf(
                    v___x_4004_,
                    v___x_4009_,
                    v___y_3928_,
                    v___y_3929_,
                    v___y_3930_,
                );
                if crate::leanh::lean_obj_tag(v___x_4010_) == 0 {
                    v_a_4011_ = crate::leanh::lean_ctor_get(v___x_4010_, 0);
                    crate::leanh::lean_inc(v_a_4011_);
                    crate::leanh::lean_dec_ref_known(v___x_4010_, 1);
                    v_a_3962_ = v_a_4011_;
                    state = 6;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_4010_) == 0 {
                        v_a_4012_ = crate::leanh::lean_ctor_get(v___x_4010_, 0);
                        crate::leanh::lean_inc(v_a_4012_);
                        crate::leanh::lean_dec_ref_known(v___x_4010_, 1);
                        v_a_3962_ = v_a_4012_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_3960_);
                        crate::leanh::lean_dec(v_a_3924_);
                        v_a_4013_ = crate::leanh::lean_ctor_get(v___x_4010_, 0);
                        v_isSharedCheck_4020_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4010_)) as u8;
                        if v_isSharedCheck_4020_ == 0 {
                            v___x_4015_ = v___x_4010_;
                            v_isShared_4016_ = v_isSharedCheck_4020_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4013_);
                            crate::leanh::lean_dec(v___x_4010_);
                            v___x_4015_ = crate::leanh::lean_box(0);
                            v_isShared_4016_ = v_isSharedCheck_4020_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            9 => {
                if v_isShared_4016_ == 0 {
                    v___x_4018_ = v___x_4015_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4019_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
                    v___x_4018_ = v_reuseFailAlloc_4019_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(
    mut v_x_4025_: *mut crate::leanh::LeanObject,
    mut v_x_4026_: *mut crate::leanh::LeanObject,
    mut v_x_4027_: *mut crate::leanh::LeanObject,
    mut v___y_4028_: *mut crate::leanh::LeanObject,
    mut v___y_4029_: *mut crate::leanh::LeanObject,
    mut v___y_4030_: *mut crate::leanh::LeanObject,
    mut v___y_4031_: *mut crate::leanh::LeanObject,
    mut v___y_4032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v_snd_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4058_: u8 = 0;
    let mut v_a_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4062_: u8 = 0;
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4025_) == 5 {
                    v_fn_4034_ = crate::leanh::lean_ctor_get(v_x_4025_, 0);
                    crate::leanh::lean_inc_ref(v_fn_4034_);
                    v_arg_4035_ = crate::leanh::lean_ctor_get(v_x_4025_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4035_);
                    crate::leanh::lean_dec_ref_known(v_x_4025_, 2);
                    v___x_4036_ = lean_array_set(v_x_4026_, v_x_4027_, v_arg_4035_);
                    v___x_4037_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4038_ = lean_nat_sub(v_x_4027_, v___x_4037_);
                    crate::leanh::lean_dec(v_x_4027_);
                    v_x_4025_ = v_fn_4034_;
                    v_x_4026_ = v___x_4036_;
                    v_x_4027_ = v___x_4038_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_4027_);
                    crate::leanh::lean_inc(v___y_4032_);
                    crate::leanh::lean_inc_ref(v___y_4031_);
                    crate::leanh::lean_inc(v___y_4030_);
                    crate::leanh::lean_inc_ref(v___y_4029_);
                    crate::leanh::lean_inc_ref(v_x_4025_);
                    v___x_4040_ = lean_infer_type(
                        v_x_4025_,
                        v___y_4029_,
                        v___y_4030_,
                        v___y_4031_,
                        v___y_4032_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4040_) == 0 {
                        v_a_4041_ = crate::leanh::lean_ctor_get(v___x_4040_, 0);
                        crate::leanh::lean_inc(v_a_4041_);
                        crate::leanh::lean_dec_ref_known(v___x_4040_, 1);
                        v___x_4042_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_x_4025_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
                        if crate::leanh::lean_obj_tag(v___x_4042_) == 0 {
                            v_a_4043_ = crate::leanh::lean_ctor_get(v___x_4042_, 0);
                            crate::leanh::lean_inc(v_a_4043_);
                            crate::leanh::lean_dec_ref_known(v___x_4042_, 1);
                            v___x_4044_ = lean_array_get_size(v_x_4026_);
                            v___x_4045_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_4046_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4046_, 0, v___x_4045_);
                            crate::leanh::lean_ctor_set(v___x_4046_, 1, v_a_4043_);
                            v___x_4047_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4047_, 0, v_a_4041_);
                            crate::leanh::lean_ctor_set(v___x_4047_, 1, v___x_4046_);
                            v___x_4048_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v___x_4044_, v_x_4026_, v___x_4045_, v___x_4047_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
                            crate::leanh::lean_dec_ref(v_x_4026_);
                            if crate::leanh::lean_obj_tag(v___x_4048_) == 0 {
                                v_a_4049_ = crate::leanh::lean_ctor_get(v___x_4048_, 0);
                                v_isSharedCheck_4058_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4048_)) as u8;
                                if v_isSharedCheck_4058_ == 0 {
                                    v___x_4051_ = v___x_4048_;
                                    v_isShared_4052_ = v_isSharedCheck_4058_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4049_);
                                    crate::leanh::lean_dec(v___x_4048_);
                                    v___x_4051_ = crate::leanh::lean_box(0);
                                    v_isShared_4052_ = v_isSharedCheck_4058_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_4059_ = crate::leanh::lean_ctor_get(v___x_4048_, 0);
                                v_isSharedCheck_4066_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4048_)) as u8;
                                if v_isSharedCheck_4066_ == 0 {
                                    v___x_4061_ = v___x_4048_;
                                    v_isShared_4062_ = v_isSharedCheck_4066_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4059_);
                                    crate::leanh::lean_dec(v___x_4048_);
                                    v___x_4061_ = crate::leanh::lean_box(0);
                                    v_isShared_4062_ = v_isSharedCheck_4066_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4041_);
                            crate::leanh::lean_dec_ref(v_x_4026_);
                            return v___x_4042_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_4026_);
                        crate::leanh::lean_dec_ref(v_x_4025_);
                        return v___x_4040_;
                    }
                }
            }
            1 => {
                v_snd_4053_ = crate::leanh::lean_ctor_get(v_a_4049_, 1);
                crate::leanh::lean_inc(v_snd_4053_);
                crate::leanh::lean_dec(v_a_4049_);
                v_snd_4054_ = crate::leanh::lean_ctor_get(v_snd_4053_, 1);
                crate::leanh::lean_inc(v_snd_4054_);
                crate::leanh::lean_dec(v_snd_4053_);
                if v_isShared_4052_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4051_, 0, v_snd_4054_);
                    v___x_4056_ = v___x_4051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_snd_4054_);
                    v___x_4056_ = v_reuseFailAlloc_4057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4056_;
            }
            3 => {
                if v_isShared_4062_ == 0 {
                    v___x_4064_ = v___x_4061_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
                    v___x_4064_ = v_reuseFailAlloc_4065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4067_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4068_ = l_Lean_Expr_bvar___override(v___x_4067_);
    return v___x_4068_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(
    mut v_body_4069_: *mut crate::leanh::LeanObject,
    mut v_binderName_4070_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_4071_: u8,
    mut v_binderType_4072_: *mut crate::leanh::LeanObject,
    mut v_arg_4073_: *mut crate::leanh::LeanObject,
    mut v___y_4074_: *mut crate::leanh::LeanObject,
    mut v___y_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
    mut v___y_4077_: *mut crate::leanh::LeanObject,
    mut v___y_4078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ty_x27_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4087_: u8 = 0;
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut v___x_4093_: u8 = 0;
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4093_ = l_Lean_Expr_hasLooseBVars(v_body_4069_);
                if v___x_4093_ == 0 {
                    v___x_4094_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_binderType_4072_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
                    if crate::leanh::lean_obj_tag(v___x_4094_) == 0 {
                        v_a_4095_ = crate::leanh::lean_ctor_get(v___x_4094_, 0);
                        crate::leanh::lean_inc(v_a_4095_);
                        crate::leanh::lean_dec_ref_known(v___x_4094_, 1);
                        v_ty_x27_4081_ = v_a_4095_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_binderName_4070_);
                        return v___x_4094_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_binderType_4072_);
                    v___x_4096_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once), _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
                    v_ty_x27_4081_ = v___x_4096_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4082_ = lean_expr_instantiate1(v_body_4069_, v_arg_4073_);
                v___x_4083_ =
                    l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(
                        v___x_4082_,
                        v___y_4074_,
                        v___y_4075_,
                        v___y_4076_,
                        v___y_4077_,
                        v___y_4078_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4083_) == 0 {
                    v_a_4084_ = crate::leanh::lean_ctor_get(v___x_4083_, 0);
                    v_isSharedCheck_4092_ = (!crate::leanh::lean_is_exclusive(v___x_4083_)) as u8;
                    if v_isSharedCheck_4092_ == 0 {
                        v___x_4086_ = v___x_4083_;
                        v_isShared_4087_ = v_isSharedCheck_4092_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4084_);
                        crate::leanh::lean_dec(v___x_4083_);
                        v___x_4086_ = crate::leanh::lean_box(0);
                        v_isShared_4087_ = v_isSharedCheck_4092_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ty_x27_4081_);
                    crate::leanh::lean_dec(v_binderName_4070_);
                    return v___x_4083_;
                }
            }
            2 => {
                v___x_4088_ = l_Lean_Expr_forallE___override(
                    v_binderName_4070_,
                    v_ty_x27_4081_,
                    v_a_4084_,
                    v_binderInfo_4071_,
                );
                if v_isShared_4087_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4086_, 0, v___x_4088_);
                    v___x_4090_ = v___x_4086_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4088_);
                    v___x_4090_ = v_reuseFailAlloc_4091_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4090_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed(
    mut v_body_4097_: *mut crate::leanh::LeanObject,
    mut v_binderName_4098_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_4099_: *mut crate::leanh::LeanObject,
    mut v_binderType_4100_: *mut crate::leanh::LeanObject,
    mut v_arg_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
    mut v___y_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
    mut v___y_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderInfo_18593__boxed_4108_: u8 = 0;
    let mut v_res_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_18593__boxed_4108_ = (crate::leanh::lean_unbox(v_binderInfo_4099_) as u8);
    v_res_4109_ =
        l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(
            v_body_4097_,
            v_binderName_4098_,
            v_binderInfo_18593__boxed_4108_,
            v_binderType_4100_,
            v_arg_4101_,
            v___y_4102_,
            v___y_4103_,
            v___y_4104_,
            v___y_4105_,
            v___y_4106_,
        );
    crate::leanh::lean_dec(v___y_4106_);
    crate::leanh::lean_dec_ref(v___y_4105_);
    crate::leanh::lean_dec(v___y_4104_);
    crate::leanh::lean_dec_ref(v___y_4103_);
    crate::leanh::lean_dec(v___y_4102_);
    crate::leanh::lean_dec_ref(v_arg_4101_);
    crate::leanh::lean_dec_ref(v_body_4097_);
    return v_res_4109_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed(
    mut v_body_4110_: *mut crate::leanh::LeanObject,
    mut v_arg_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4118_ =
        l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(
            v_body_4110_,
            v_arg_4111_,
            v___y_4112_,
            v___y_4113_,
            v___y_4114_,
            v___y_4115_,
            v___y_4116_,
        );
    crate::leanh::lean_dec(v___y_4116_);
    crate::leanh::lean_dec_ref(v___y_4115_);
    crate::leanh::lean_dec(v___y_4114_);
    crate::leanh::lean_dec_ref(v___y_4113_);
    crate::leanh::lean_dec(v___y_4112_);
    crate::leanh::lean_dec_ref(v_arg_4111_);
    crate::leanh::lean_dec_ref(v_body_4110_);
    return v_res_4118_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4122_ =
        l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2;
    v___x_4123_ = l_Lean_Level_param___override(v___x_4122_);
    return v___x_4123_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4124_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3_once), _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3);
    v___x_4125_ = l_Lean_Expr_sort___override(v___x_4124_);
    return v___x_4125_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4126_ = crate::leanh::lean_box(0);
    v___x_4127_ = l_Lean_Level_succ___override(v___x_4126_);
    return v___x_4127_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4128_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5_once), _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5);
    v___x_4129_ = l_Lean_Expr_sort___override(v___x_4128_);
    return v___x_4129_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(
    mut v_e_4130_: *mut crate::leanh::LeanObject,
    mut v_a_4131_: *mut crate::leanh::LeanObject,
    mut v_a_4132_: *mut crate::leanh::LeanObject,
    mut v_a_4133_: *mut crate::leanh::LeanObject,
    mut v_a_4134_: *mut crate::leanh::LeanObject,
    mut v_a_4135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: u8 = 0;
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut v_binderName_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4172_: u8 = 0;
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: u8 = 0;
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4180_: u8 = 0;
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: u8 = 0;
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: u8 = 0;
    let mut v___x_4192_: u8 = 0;
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4210_: u8 = 0;
    let mut v_val_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4214_: u8 = 0;
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4146_ = lean_st_ref_get(v_a_4131_);
                v___x_4147_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v___x_4146_, v_e_4130_);
                crate::leanh::lean_dec(v___x_4146_);
                if crate::leanh::lean_obj_tag(v___x_4147_) == 0 {
                    crate::leanh::lean_inc_ref(v_e_4130_);
                    v___x_4148_ =
                        l_Lean_Meta_isProof(v_e_4130_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
                    if crate::leanh::lean_obj_tag(v___x_4148_) == 0 {
                        v_a_4149_ = crate::leanh::lean_ctor_get(v___x_4148_, 0);
                        crate::leanh::lean_inc(v_a_4149_);
                        crate::leanh::lean_dec_ref_known(v___x_4148_, 1);
                        v___x_4150_ = (crate::leanh::lean_unbox(v_a_4149_) as u8);
                        crate::leanh::lean_dec(v_a_4149_);
                        if v___x_4150_ == 0 {
                            match crate::leanh::lean_obj_tag(v_e_4130_) {
                                5 => {
                                    v___x_4151_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_4130_, v_a_4135_);
                                    if crate::leanh::lean_obj_tag(v___x_4151_) == 0 {
                                        v_a_4152_ = crate::leanh::lean_ctor_get(v___x_4151_, 0);
                                        crate::leanh::lean_inc(v_a_4152_);
                                        crate::leanh::lean_dec_ref_known(v___x_4151_, 1);
                                        if crate::leanh::lean_obj_tag(v_a_4152_) == 1 {
                                            v_val_4153_ = crate::leanh::lean_ctor_get(v_a_4152_, 0);
                                            crate::leanh::lean_inc(v_val_4153_);
                                            crate::leanh::lean_dec_ref_known(v_a_4152_, 1);
                                            v___x_4154_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_4153_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
                                            v___y_4144_ = v___x_4154_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_a_4152_);
                                            v_dummy_4155_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once), _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
                                            v_nargs_4156_ = l_Lean_Expr_getAppNumArgs(v_e_4130_);
                                            crate::leanh::lean_inc(v_nargs_4156_);
                                            v___x_4157_ =
                                                lean_mk_array(v_nargs_4156_, v_dummy_4155_);
                                            v___x_4158_ = crate::leanh::lean_unsigned_to_nat(1);
                                            v___x_4159_ = lean_nat_sub(v_nargs_4156_, v___x_4158_);
                                            crate::leanh::lean_dec(v_nargs_4156_);
                                            crate::leanh::lean_inc_ref(v_e_4130_);
                                            v___x_4160_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_e_4130_, v___x_4157_, v___x_4159_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
                                            v___y_4144_ = v___x_4160_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_e_4130_, 2);
                                        v_a_4161_ = crate::leanh::lean_ctor_get(v___x_4151_, 0);
                                        v_isSharedCheck_4168_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4151_)) as u8;
                                        if v_isSharedCheck_4168_ == 0 {
                                            v___x_4163_ = v___x_4151_;
                                            v_isShared_4164_ = v_isSharedCheck_4168_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4161_);
                                            crate::leanh::lean_dec(v___x_4151_);
                                            v___x_4163_ = crate::leanh::lean_box(0);
                                            v_isShared_4164_ = v_isSharedCheck_4168_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                                7 => {
                                    v_binderName_4169_ = crate::leanh::lean_ctor_get(v_e_4130_, 0);
                                    v_binderType_4170_ = crate::leanh::lean_ctor_get(v_e_4130_, 1);
                                    v_body_4171_ = crate::leanh::lean_ctor_get(v_e_4130_, 2);
                                    v_binderInfo_4172_ = crate::leanh::lean_ctor_get_uint8(
                                        v_e_4130_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 8) as u32,
                                    );
                                    v___x_4173_ =
                                        crate::leanh::lean_box((v_binderInfo_4172_) as usize);
                                    crate::leanh::lean_inc_ref_n(v_binderType_4170_, 2);
                                    crate::leanh::lean_inc_n(v_binderName_4169_, 2);
                                    crate::leanh::lean_inc_ref(v_body_4171_);
                                    v___f_4174_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed as *mut core::ffi::c_void, 11, 4);
                                    crate::leanh::lean_closure_set(v___f_4174_, 0, v_body_4171_);
                                    crate::leanh::lean_closure_set(
                                        v___f_4174_,
                                        1,
                                        v_binderName_4169_,
                                    );
                                    crate::leanh::lean_closure_set(v___f_4174_, 2, v___x_4173_);
                                    crate::leanh::lean_closure_set(
                                        v___f_4174_,
                                        3,
                                        v_binderType_4170_,
                                    );
                                    v___x_4175_ = 0;
                                    v___x_4176_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_binderName_4169_, v_binderInfo_4172_, v_binderType_4170_, v___f_4174_, v___x_4175_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
                                    v___y_4144_ = v___x_4176_;
                                    state = 2;
                                    continue;
                                }
                                6 => {
                                    v_binderName_4177_ = crate::leanh::lean_ctor_get(v_e_4130_, 0);
                                    v_binderType_4178_ = crate::leanh::lean_ctor_get(v_e_4130_, 1);
                                    v_body_4179_ = crate::leanh::lean_ctor_get(v_e_4130_, 2);
                                    v_binderInfo_4180_ = crate::leanh::lean_ctor_get_uint8(
                                        v_e_4130_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 8) as u32,
                                    );
                                    crate::leanh::lean_inc_ref(v_e_4130_);
                                    v___x_4181_ = l_Lean_Expr_etaExpandedStrict_x3f(v_e_4130_);
                                    if crate::leanh::lean_obj_tag(v___x_4181_) == 1 {
                                        v_val_4182_ = crate::leanh::lean_ctor_get(v___x_4181_, 0);
                                        crate::leanh::lean_inc(v_val_4182_);
                                        crate::leanh::lean_dec_ref_known(v___x_4181_, 1);
                                        v___x_4183_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_4182_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
                                        v___y_4144_ = v___x_4183_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_4181_);
                                        crate::leanh::lean_inc_ref(v_body_4179_);
                                        v___f_4184_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed as *mut core::ffi::c_void, 8, 1);
                                        crate::leanh::lean_closure_set(
                                            v___f_4184_,
                                            0,
                                            v_body_4179_,
                                        );
                                        v___x_4185_ = 0;
                                        crate::leanh::lean_inc_ref(v_binderType_4178_);
                                        crate::leanh::lean_inc(v_binderName_4177_);
                                        v___x_4186_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_binderName_4177_, v_binderInfo_4180_, v_binderType_4178_, v___f_4184_, v___x_4185_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
                                        v___y_4144_ = v___x_4186_;
                                        state = 2;
                                        continue;
                                    }
                                }
                                8 => {
                                    v_value_4187_ = crate::leanh::lean_ctor_get(v_e_4130_, 2);
                                    v_body_4188_ = crate::leanh::lean_ctor_get(v_e_4130_, 3);
                                    v___x_4189_ =
                                        lean_expr_instantiate1(v_body_4188_, v_value_4187_);
                                    v___x_4190_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_4189_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
                                    v___y_4144_ = v___x_4190_;
                                    state = 2;
                                    continue;
                                }
                                3 => {
                                    v___x_4191_ = l_Lean_Expr_isProp(v_e_4130_);
                                    if v___x_4191_ == 0 {
                                        v___x_4192_ = l_Lean_Expr_isType(v_e_4130_);
                                        if v___x_4192_ == 0 {
                                            v___x_4193_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4_once), _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4);
                                            v_a_4138_ = v___x_4193_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_4194_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6_once), _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6);
                                            v_a_4138_ = v___x_4194_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v___x_4195_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once), _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
                                        v_a_4138_ = v___x_4195_;
                                        state = 1;
                                        continue;
                                    }
                                }
                                4 => {
                                    v_declName_4196_ = crate::leanh::lean_ctor_get(v_e_4130_, 0);
                                    v___x_4197_ = crate::leanh::lean_box(0);
                                    crate::leanh::lean_inc(v_declName_4196_);
                                    v___x_4198_ =
                                        l_Lean_Expr_const___override(v_declName_4196_, v___x_4197_);
                                    v_a_4138_ = v___x_4198_;
                                    state = 1;
                                    continue;
                                }
                                10 => {
                                    v_expr_4199_ = crate::leanh::lean_ctor_get(v_e_4130_, 1);
                                    crate::leanh::lean_inc_ref(v_expr_4199_);
                                    v___x_4200_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_expr_4199_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
                                    v___y_4144_ = v___x_4200_;
                                    state = 2;
                                    continue;
                                }
                                _ => {
                                    v___x_4201_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once), _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
                                    v_a_4138_ = v___x_4201_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v___x_4202_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once), _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
                            v_a_4138_ = v___x_4202_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4130_);
                        v_a_4203_ = crate::leanh::lean_ctor_get(v___x_4148_, 0);
                        v_isSharedCheck_4210_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4148_)) as u8;
                        if v_isSharedCheck_4210_ == 0 {
                            v___x_4205_ = v___x_4148_;
                            v_isShared_4206_ = v_isSharedCheck_4210_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4203_);
                            crate::leanh::lean_dec(v___x_4148_);
                            v___x_4205_ = crate::leanh::lean_box(0);
                            v_isShared_4206_ = v_isSharedCheck_4210_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4130_);
                    v_val_4211_ = crate::leanh::lean_ctor_get(v___x_4147_, 0);
                    v_isSharedCheck_4218_ = (!crate::leanh::lean_is_exclusive(v___x_4147_)) as u8;
                    if v_isSharedCheck_4218_ == 0 {
                        v___x_4213_ = v___x_4147_;
                        v_isShared_4214_ = v_isSharedCheck_4218_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4211_);
                        crate::leanh::lean_dec(v___x_4147_);
                        v___x_4213_ = crate::leanh::lean_box(0);
                        v_isShared_4214_ = v_isSharedCheck_4218_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4139_ = lean_st_ref_take(v_a_4131_);
                crate::leanh::lean_inc_ref(v_a_4138_);
                v___x_4140_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___x_4139_, v_e_4130_, v_a_4138_);
                v___x_4141_ = lean_st_ref_set(v_a_4131_, v___x_4140_);
                v___x_4142_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4142_, 0, v_a_4138_);
                return v___x_4142_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_4144_) == 0 {
                    v_a_4145_ = crate::leanh::lean_ctor_get(v___y_4144_, 0);
                    crate::leanh::lean_inc(v_a_4145_);
                    crate::leanh::lean_dec_ref_known(v___y_4144_, 1);
                    v_a_4138_ = v_a_4145_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_4130_);
                    return v___y_4144_;
                }
            }
            3 => {
                if v_isShared_4164_ == 0 {
                    v___x_4166_ = v___x_4163_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4167_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
                    v___x_4166_ = v_reuseFailAlloc_4167_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4166_;
            }
            5 => {
                if v_isShared_4206_ == 0 {
                    v___x_4208_ = v___x_4205_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4209_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
                    v___x_4208_ = v_reuseFailAlloc_4209_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4208_;
            }
            7 => {
                if v_isShared_4214_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4213_, 0);
                    v___x_4216_ = v___x_4213_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4217_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_val_4211_);
                    v___x_4216_ = v_reuseFailAlloc_4217_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(
    mut v_body_4219_: *mut crate::leanh::LeanObject,
    mut v_arg_4220_: *mut crate::leanh::LeanObject,
    mut v___y_4221_: *mut crate::leanh::LeanObject,
    mut v___y_4222_: *mut crate::leanh::LeanObject,
    mut v___y_4223_: *mut crate::leanh::LeanObject,
    mut v___y_4224_: *mut crate::leanh::LeanObject,
    mut v___y_4225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4227_ = lean_expr_instantiate1(v_body_4219_, v_arg_4220_);
    v___x_4228_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(
        v___x_4227_,
        v___y_4221_,
        v___y_4222_,
        v___y_4223_,
        v___y_4224_,
        v___y_4225_,
    );
    return v___x_4228_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___boxed(
    mut v_x_4229_: *mut crate::leanh::LeanObject,
    mut v_x_4230_: *mut crate::leanh::LeanObject,
    mut v_x_4231_: *mut crate::leanh::LeanObject,
    mut v___y_4232_: *mut crate::leanh::LeanObject,
    mut v___y_4233_: *mut crate::leanh::LeanObject,
    mut v___y_4234_: *mut crate::leanh::LeanObject,
    mut v___y_4235_: *mut crate::leanh::LeanObject,
    mut v___y_4236_: *mut crate::leanh::LeanObject,
    mut v___y_4237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4238_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_x_4229_, v_x_4230_, v_x_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
    crate::leanh::lean_dec(v___y_4236_);
    crate::leanh::lean_dec_ref(v___y_4235_);
    crate::leanh::lean_dec(v___y_4234_);
    crate::leanh::lean_dec_ref(v___y_4233_);
    crate::leanh::lean_dec(v___y_4232_);
    return v_res_4238_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___boxed(
    mut v_upperBound_4239_: *mut crate::leanh::LeanObject,
    mut v_args_4240_: *mut crate::leanh::LeanObject,
    mut v_a_4241_: *mut crate::leanh::LeanObject,
    mut v_b_4242_: *mut crate::leanh::LeanObject,
    mut v___y_4243_: *mut crate::leanh::LeanObject,
    mut v___y_4244_: *mut crate::leanh::LeanObject,
    mut v___y_4245_: *mut crate::leanh::LeanObject,
    mut v___y_4246_: *mut crate::leanh::LeanObject,
    mut v___y_4247_: *mut crate::leanh::LeanObject,
    mut v___y_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4249_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_4239_, v_args_4240_, v_a_4241_, v_b_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
    crate::leanh::lean_dec(v___y_4247_);
    crate::leanh::lean_dec_ref(v___y_4246_);
    crate::leanh::lean_dec(v___y_4245_);
    crate::leanh::lean_dec_ref(v___y_4244_);
    crate::leanh::lean_dec(v___y_4243_);
    crate::leanh::lean_dec_ref(v_args_4240_);
    crate::leanh::lean_dec(v_upperBound_4239_);
    return v_res_4249_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___boxed(
    mut v_args_4250_: *mut crate::leanh::LeanObject,
    mut v_a_4251_: *mut crate::leanh::LeanObject,
    mut v_snd_4252_: *mut crate::leanh::LeanObject,
    mut v_____r_4253_: *mut crate::leanh::LeanObject,
    mut v_fty_4254_: *mut crate::leanh::LeanObject,
    mut v_j_4255_: *mut crate::leanh::LeanObject,
    mut v___y_4256_: *mut crate::leanh::LeanObject,
    mut v___y_4257_: *mut crate::leanh::LeanObject,
    mut v___y_4258_: *mut crate::leanh::LeanObject,
    mut v___y_4259_: *mut crate::leanh::LeanObject,
    mut v___y_4260_: *mut crate::leanh::LeanObject,
    mut v___y_4261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4262_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_args_4250_, v_a_4251_, v_snd_4252_, v_____r_4253_, v_fty_4254_, v_j_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
    crate::leanh::lean_dec(v___y_4260_);
    crate::leanh::lean_dec_ref(v___y_4259_);
    crate::leanh::lean_dec(v___y_4258_);
    crate::leanh::lean_dec_ref(v___y_4257_);
    crate::leanh::lean_dec(v___y_4256_);
    crate::leanh::lean_dec(v_j_4255_);
    crate::leanh::lean_dec(v_a_4251_);
    crate::leanh::lean_dec_ref(v_args_4250_);
    return v_res_4262_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___boxed(
    mut v_e_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
    mut v_a_4265_: *mut crate::leanh::LeanObject,
    mut v_a_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
    mut v_a_4268_: *mut crate::leanh::LeanObject,
    mut v_a_4269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4270_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(
        v_e_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_,
    );
    crate::leanh::lean_dec(v_a_4268_);
    crate::leanh::lean_dec_ref(v_a_4267_);
    crate::leanh::lean_dec(v_a_4266_);
    crate::leanh::lean_dec_ref(v_a_4265_);
    crate::leanh::lean_dec(v_a_4264_);
    return v_res_4270_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(
    mut v_00_u03b1_4271_: *mut crate::leanh::LeanObject,
    mut v_msg_4272_: *mut crate::leanh::LeanObject,
    mut v___y_4273_: *mut crate::leanh::LeanObject,
    mut v___y_4274_: *mut crate::leanh::LeanObject,
    mut v___y_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4278_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
    return v___x_4278_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___boxed(
    mut v_00_u03b1_4279_: *mut crate::leanh::LeanObject,
    mut v_msg_4280_: *mut crate::leanh::LeanObject,
    mut v___y_4281_: *mut crate::leanh::LeanObject,
    mut v___y_4282_: *mut crate::leanh::LeanObject,
    mut v___y_4283_: *mut crate::leanh::LeanObject,
    mut v___y_4284_: *mut crate::leanh::LeanObject,
    mut v___y_4285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4286_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(v_00_u03b1_4279_, v_msg_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
    crate::leanh::lean_dec(v___y_4284_);
    crate::leanh::lean_dec_ref(v___y_4283_);
    crate::leanh::lean_dec(v___y_4282_);
    crate::leanh::lean_dec_ref(v___y_4281_);
    return v_res_4286_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(
    mut v_upperBound_4287_: *mut crate::leanh::LeanObject,
    mut v_args_4288_: *mut crate::leanh::LeanObject,
    mut v_inst_4289_: *mut crate::leanh::LeanObject,
    mut v_R_4290_: *mut crate::leanh::LeanObject,
    mut v_a_4291_: *mut crate::leanh::LeanObject,
    mut v_b_4292_: *mut crate::leanh::LeanObject,
    mut v_c_4293_: *mut crate::leanh::LeanObject,
    mut v___y_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
    mut v___y_4296_: *mut crate::leanh::LeanObject,
    mut v___y_4297_: *mut crate::leanh::LeanObject,
    mut v___y_4298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4300_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_4287_, v_args_4288_, v_a_4291_, v_b_4292_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
    return v___x_4300_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___boxed(
    mut v_upperBound_4301_: *mut crate::leanh::LeanObject,
    mut v_args_4302_: *mut crate::leanh::LeanObject,
    mut v_inst_4303_: *mut crate::leanh::LeanObject,
    mut v_R_4304_: *mut crate::leanh::LeanObject,
    mut v_a_4305_: *mut crate::leanh::LeanObject,
    mut v_b_4306_: *mut crate::leanh::LeanObject,
    mut v_c_4307_: *mut crate::leanh::LeanObject,
    mut v___y_4308_: *mut crate::leanh::LeanObject,
    mut v___y_4309_: *mut crate::leanh::LeanObject,
    mut v___y_4310_: *mut crate::leanh::LeanObject,
    mut v___y_4311_: *mut crate::leanh::LeanObject,
    mut v___y_4312_: *mut crate::leanh::LeanObject,
    mut v___y_4313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4314_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(v_upperBound_4301_, v_args_4302_, v_inst_4303_, v_R_4304_, v_a_4305_, v_b_4306_, v_c_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
    crate::leanh::lean_dec(v___y_4312_);
    crate::leanh::lean_dec_ref(v___y_4311_);
    crate::leanh::lean_dec(v___y_4310_);
    crate::leanh::lean_dec_ref(v___y_4309_);
    crate::leanh::lean_dec(v___y_4308_);
    crate::leanh::lean_dec_ref(v_args_4302_);
    crate::leanh::lean_dec(v_upperBound_4301_);
    return v_res_4314_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2(
    mut v_00_u03b2_4315_: *mut crate::leanh::LeanObject,
    mut v_m_4316_: *mut crate::leanh::LeanObject,
    mut v_a_4317_: *mut crate::leanh::LeanObject,
    mut v_b_4318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4319_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v_m_4316_, v_a_4317_, v_b_4318_);
    return v___x_4319_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(
    mut v_00_u03b2_4320_: *mut crate::leanh::LeanObject,
    mut v_m_4321_: *mut crate::leanh::LeanObject,
    mut v_a_4322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4323_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_4321_, v_a_4322_);
    return v___x_4323_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___boxed(
    mut v_00_u03b2_4324_: *mut crate::leanh::LeanObject,
    mut v_m_4325_: *mut crate::leanh::LeanObject,
    mut v_a_4326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(v_00_u03b2_4324_, v_m_4325_, v_a_4326_);
    crate::leanh::lean_dec_ref(v_a_4326_);
    crate::leanh::lean_dec_ref(v_m_4325_);
    return v_res_4327_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(
    mut v_00_u03b2_4328_: *mut crate::leanh::LeanObject,
    mut v_a_4329_: *mut crate::leanh::LeanObject,
    mut v_x_4330_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4331_: u8 = 0;
    v___x_4331_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_4329_, v_x_4330_);
    return v___x_4331_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___boxed(
    mut v_00_u03b2_4332_: *mut crate::leanh::LeanObject,
    mut v_a_4333_: *mut crate::leanh::LeanObject,
    mut v_x_4334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4335_: u8 = 0;
    let mut v_r_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4335_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(v_00_u03b2_4332_, v_a_4333_, v_x_4334_);
    crate::leanh::lean_dec(v_x_4334_);
    crate::leanh::lean_dec_ref(v_a_4333_);
    v_r_4336_ = crate::leanh::lean_box((v_res_4335_) as usize);
    return v_r_4336_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4(
    mut v_00_u03b2_4337_: *mut crate::leanh::LeanObject,
    mut v_data_4338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_data_4338_);
    return v___x_4339_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5(
    mut v_00_u03b2_4340_: *mut crate::leanh::LeanObject,
    mut v_a_4341_: *mut crate::leanh::LeanObject,
    mut v_b_4342_: *mut crate::leanh::LeanObject,
    mut v_x_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4344_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_4341_, v_b_4342_, v_x_4343_);
    return v___x_4344_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(
    mut v_00_u03b2_4345_: *mut crate::leanh::LeanObject,
    mut v_a_4346_: *mut crate::leanh::LeanObject,
    mut v_x_4347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_4346_, v_x_4347_);
    return v___x_4348_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___boxed(
    mut v_00_u03b2_4349_: *mut crate::leanh::LeanObject,
    mut v_a_4350_: *mut crate::leanh::LeanObject,
    mut v_x_4351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4352_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(v_00_u03b2_4349_, v_a_4350_, v_x_4351_);
    crate::leanh::lean_dec(v_x_4351_);
    crate::leanh::lean_dec_ref(v_a_4350_);
    return v_res_4352_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6(
    mut v_00_u03b2_4353_: *mut crate::leanh::LeanObject,
    mut v_i_4354_: *mut crate::leanh::LeanObject,
    mut v_source_4355_: *mut crate::leanh::LeanObject,
    mut v_target_4356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4357_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(v_i_4354_, v_source_4355_, v_target_4356_);
    return v___x_4357_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9(
    mut v_00_u03b2_4358_: *mut crate::leanh::LeanObject,
    mut v_x_4359_: *mut crate::leanh::LeanObject,
    mut v_x_4360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4361_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(v_x_4359_, v_x_4360_);
    return v___x_4361_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4362_ = crate::leanh::lean_box(0);
    v___x_4363_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4364_ = lean_mk_array(v___x_4363_, v___x_4362_);
    return v___x_4364_;
}
pub unsafe fn _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4365_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0_once), _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0);
    v___x_4366_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4367_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4367_, 0, v___x_4366_);
    crate::leanh::lean_ctor_set(v___x_4367_, 1, v___x_4365_);
    return v___x_4367_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(
    mut v_e_4368_: *mut crate::leanh::LeanObject,
    mut v_a_4369_: *mut crate::leanh::LeanObject,
    mut v_a_4370_: *mut crate::leanh::LeanObject,
    mut v_a_4371_: *mut crate::leanh::LeanObject,
    mut v_a_4372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4380_: u8 = 0;
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4385_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4374_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once), _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
                v___x_4375_ = lean_st_mk_ref(v___x_4374_);
                v___x_4376_ =
                    l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(
                        v_e_4368_,
                        v___x_4375_,
                        v_a_4369_,
                        v_a_4370_,
                        v_a_4371_,
                        v_a_4372_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4376_) == 0 {
                    v_a_4377_ = crate::leanh::lean_ctor_get(v___x_4376_, 0);
                    v_isSharedCheck_4385_ = (!crate::leanh::lean_is_exclusive(v___x_4376_)) as u8;
                    if v_isSharedCheck_4385_ == 0 {
                        v___x_4379_ = v___x_4376_;
                        v_isShared_4380_ = v_isSharedCheck_4385_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4377_);
                        crate::leanh::lean_dec(v___x_4376_);
                        v___x_4379_ = crate::leanh::lean_box(0);
                        v_isShared_4380_ = v_isSharedCheck_4385_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4375_);
                    return v___x_4376_;
                }
            }
            1 => {
                v___x_4381_ = lean_st_ref_get(v___x_4375_);
                crate::leanh::lean_dec(v___x_4375_);
                crate::leanh::lean_dec(v___x_4381_);
                if v_isShared_4380_ == 0 {
                    v___x_4383_ = v___x_4379_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4384_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4377_);
                    v___x_4383_ = v_reuseFailAlloc_4384_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4383_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___boxed(
    mut v_e_4386_: *mut crate::leanh::LeanObject,
    mut v_a_4387_: *mut crate::leanh::LeanObject,
    mut v_a_4388_: *mut crate::leanh::LeanObject,
    mut v_a_4389_: *mut crate::leanh::LeanObject,
    mut v_a_4390_: *mut crate::leanh::LeanObject,
    mut v_a_4391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4392_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(
        v_e_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_,
    );
    crate::leanh::lean_dec(v_a_4390_);
    crate::leanh::lean_dec_ref(v_a_4389_);
    crate::leanh::lean_dec(v_a_4388_);
    crate::leanh::lean_dec_ref(v_a_4387_);
    return v_res_4392_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(
    mut v_m_4393_: *mut crate::leanh::LeanObject,
    mut v_a_4394_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: u64 = 0;
    let mut v___x_4398_: u64 = 0;
    let mut v___x_4399_: u64 = 0;
    let mut v_fold_4400_: u64 = 0;
    let mut v___x_4401_: u64 = 0;
    let mut v___x_4402_: u64 = 0;
    let mut v___x_4403_: u64 = 0;
    let mut v___x_4404_: usize = 0;
    let mut v___x_4405_: usize = 0;
    let mut v___x_4406_: usize = 0;
    let mut v___x_4407_: usize = 0;
    let mut v___x_4408_: usize = 0;
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: u8 = 0;
    v_buckets_4395_ = crate::leanh::lean_ctor_get(v_m_4393_, 1);
    v___x_4396_ = lean_array_get_size(v_buckets_4395_);
    v___x_4397_ = l_Lean_Expr_hash(v_a_4394_);
    v___x_4398_ = 32u64;
    v___x_4399_ = lean_uint64_shift_right(v___x_4397_, v___x_4398_);
    v_fold_4400_ = lean_uint64_xor(v___x_4397_, v___x_4399_);
    v___x_4401_ = 16u64;
    v___x_4402_ = lean_uint64_shift_right(v_fold_4400_, v___x_4401_);
    v___x_4403_ = lean_uint64_xor(v_fold_4400_, v___x_4402_);
    v___x_4404_ = lean_uint64_to_usize(v___x_4403_);
    v___x_4405_ = lean_usize_of_nat(v___x_4396_);
    v___x_4406_ = 1usize;
    v___x_4407_ = lean_usize_sub(v___x_4405_, v___x_4406_);
    v___x_4408_ = lean_usize_land(v___x_4404_, v___x_4407_);
    v___x_4409_ = lean_array_uget_borrowed(v_buckets_4395_, v___x_4408_);
    v___x_4410_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_4394_, v___x_4409_);
    return v___x_4410_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg___boxed(
    mut v_m_4411_: *mut crate::leanh::LeanObject,
    mut v_a_4412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4413_: u8 = 0;
    let mut v_r_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4413_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_4411_, v_a_4412_);
    crate::leanh::lean_dec_ref(v_a_4412_);
    crate::leanh::lean_dec_ref(v_m_4411_);
    v_r_4414_ = crate::leanh::lean_box((v_res_4413_) as usize);
    return v_r_4414_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(
    mut v_m_4415_: *mut crate::leanh::LeanObject,
    mut v_a_4416_: *mut crate::leanh::LeanObject,
    mut v_b_4417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u64 = 0;
    let mut v___x_4422_: u64 = 0;
    let mut v___x_4423_: u64 = 0;
    let mut v_fold_4424_: u64 = 0;
    let mut v___x_4425_: u64 = 0;
    let mut v___x_4426_: u64 = 0;
    let mut v___x_4427_: u64 = 0;
    let mut v___x_4428_: usize = 0;
    let mut v___x_4429_: usize = 0;
    let mut v___x_4430_: usize = 0;
    let mut v___x_4431_: usize = 0;
    let mut v___x_4432_: usize = 0;
    let mut v_bkt_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: u8 = 0;
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4437_: u8 = 0;
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: u8 = 0;
    let mut v_val_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4455_: u8 = 0;
    let mut v_unused_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4418_ = crate::leanh::lean_ctor_get(v_m_4415_, 0);
                v_buckets_4419_ = crate::leanh::lean_ctor_get(v_m_4415_, 1);
                v___x_4420_ = lean_array_get_size(v_buckets_4419_);
                v___x_4421_ = l_Lean_Expr_hash(v_a_4416_);
                v___x_4422_ = 32u64;
                v___x_4423_ = lean_uint64_shift_right(v___x_4421_, v___x_4422_);
                v_fold_4424_ = lean_uint64_xor(v___x_4421_, v___x_4423_);
                v___x_4425_ = 16u64;
                v___x_4426_ = lean_uint64_shift_right(v_fold_4424_, v___x_4425_);
                v___x_4427_ = lean_uint64_xor(v_fold_4424_, v___x_4426_);
                v___x_4428_ = lean_uint64_to_usize(v___x_4427_);
                v___x_4429_ = lean_usize_of_nat(v___x_4420_);
                v___x_4430_ = 1usize;
                v___x_4431_ = lean_usize_sub(v___x_4429_, v___x_4430_);
                v___x_4432_ = lean_usize_land(v___x_4428_, v___x_4431_);
                v_bkt_4433_ = lean_array_uget_borrowed(v_buckets_4419_, v___x_4432_);
                v___x_4434_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_4416_, v_bkt_4433_);
                if v___x_4434_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_4419_);
                    crate::leanh::lean_inc(v_size_4418_);
                    v_isSharedCheck_4455_ = (!crate::leanh::lean_is_exclusive(v_m_4415_)) as u8;
                    if v_isSharedCheck_4455_ == 0 {
                        v_unused_4456_ = crate::leanh::lean_ctor_get(v_m_4415_, 1);
                        crate::leanh::lean_dec(v_unused_4456_);
                        v_unused_4457_ = crate::leanh::lean_ctor_get(v_m_4415_, 0);
                        crate::leanh::lean_dec(v_unused_4457_);
                        v___x_4436_ = v_m_4415_;
                        v_isShared_4437_ = v_isSharedCheck_4455_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_4415_);
                        v___x_4436_ = crate::leanh::lean_box(0);
                        v_isShared_4437_ = v_isSharedCheck_4455_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_4417_);
                    crate::leanh::lean_dec_ref(v_a_4416_);
                    return v_m_4415_;
                }
            }
            1 => {
                v___x_4438_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_4439_ = lean_nat_add(v_size_4418_, v___x_4438_);
                crate::leanh::lean_dec(v_size_4418_);
                crate::leanh::lean_inc(v_bkt_4433_);
                v___x_4440_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4440_, 0, v_a_4416_);
                crate::leanh::lean_ctor_set(v___x_4440_, 1, v_b_4417_);
                crate::leanh::lean_ctor_set(v___x_4440_, 2, v_bkt_4433_);
                v_buckets_x27_4441_ = lean_array_uset(v_buckets_4419_, v___x_4432_, v___x_4440_);
                v___x_4442_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_4443_ = lean_nat_mul(v_size_x27_4439_, v___x_4442_);
                v___x_4444_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4445_ = lean_nat_div(v___x_4443_, v___x_4444_);
                crate::leanh::lean_dec(v___x_4443_);
                v___x_4446_ = lean_array_get_size(v_buckets_x27_4441_);
                v___x_4447_ = lean_nat_dec_le(v___x_4445_, v___x_4446_);
                crate::leanh::lean_dec(v___x_4445_);
                if v___x_4447_ == 0 {
                    v_val_4448_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_buckets_x27_4441_);
                    if v_isShared_4437_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4436_, 1, v_val_4448_);
                        crate::leanh::lean_ctor_set(v___x_4436_, 0, v_size_x27_4439_);
                        v___x_4450_ = v___x_4436_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4451_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_size_x27_4439_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4451_, 1, v_val_4448_);
                        v___x_4450_ = v_reuseFailAlloc_4451_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4437_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4436_, 1, v_buckets_x27_4441_);
                        crate::leanh::lean_ctor_set(v___x_4436_, 0, v_size_x27_4439_);
                        v___x_4453_ = v___x_4436_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4454_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_size_x27_4439_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4454_, 1, v_buckets_x27_4441_);
                        v___x_4453_ = v_reuseFailAlloc_4454_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4450_;
            }
            3 => {
                return v___x_4453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(
    mut v_e_4463_: *mut crate::leanh::LeanObject,
    mut v_omitTopForall_4464_: u8,
    mut v_a_4465_: *mut crate::leanh::LeanObject,
    mut v_a_4466_: *mut crate::leanh::LeanObject,
    mut v_a_4467_: *mut crate::leanh::LeanObject,
    mut v_a_4468_: *mut crate::leanh::LeanObject,
    mut v_a_4469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seen_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_consts_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4477_: u8 = 0;
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: u32 = 0;
    let mut v___x_4486_: u32 = 0;
    let mut v___x_4487_: u8 = 0;
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: u32 = 0;
    let mut v___x_4491_: u8 = 0;
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u32 = 0;
    let mut v___x_4495_: u32 = 0;
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4501_: u8 = 0;
    let mut v_fn_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: u8 = 0;
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4511_: u8 = 0;
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4516_: u8 = 0;
    let mut v_binderType_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4527_: u8 = 0;
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4534_: u8 = 0;
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: u8 = 0;
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_4463_) {
                4 => {
                    v_declName_4471_ = crate::leanh::lean_ctor_get(v_e_4463_, 0);
                    crate::leanh::lean_inc(v_declName_4471_);
                    crate::leanh::lean_dec_ref_known(v_e_4463_, 2);
                    v___x_4472_ = lean_st_ref_take(v_a_4465_);
                    v_seen_4473_ = crate::leanh::lean_ctor_get(v___x_4472_, 0);
                    v_consts_4474_ = crate::leanh::lean_ctor_get(v___x_4472_, 1);
                    v_isSharedCheck_4501_ = (!crate::leanh::lean_is_exclusive(v___x_4472_)) as u8;
                    if v_isSharedCheck_4501_ == 0 {
                        v___x_4476_ = v___x_4472_;
                        v_isShared_4477_ = v_isSharedCheck_4501_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_consts_4474_);
                        crate::leanh::lean_inc(v_seen_4473_);
                        crate::leanh::lean_dec(v___x_4472_);
                        v___x_4476_ = crate::leanh::lean_box(0);
                        v_isShared_4477_ = v_isSharedCheck_4501_;
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v_fn_4502_ = crate::leanh::lean_ctor_get(v_e_4463_, 0);
                    crate::leanh::lean_inc_ref(v_fn_4502_);
                    v_arg_4503_ = crate::leanh::lean_ctor_get(v_e_4463_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4503_);
                    crate::leanh::lean_dec_ref_known(v_e_4463_, 2);
                    v___x_4504_ = 0;
                    v___x_4505_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_fn_4502_, v___x_4504_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
                    v_a_4506_ = crate::leanh::lean_ctor_get(v___x_4505_, 0);
                    crate::leanh::lean_inc(v_a_4506_);
                    crate::leanh::lean_dec_ref(v___x_4505_);
                    v___x_4507_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_arg_4503_, v___x_4504_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
                    v_a_4508_ = crate::leanh::lean_ctor_get(v___x_4507_, 0);
                    v_isSharedCheck_4516_ = (!crate::leanh::lean_is_exclusive(v___x_4507_)) as u8;
                    if v_isSharedCheck_4516_ == 0 {
                        v___x_4510_ = v___x_4507_;
                        v_isShared_4511_ = v_isSharedCheck_4516_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4508_);
                        crate::leanh::lean_dec(v___x_4507_);
                        v___x_4510_ = crate::leanh::lean_box(0);
                        v_isShared_4511_ = v_isSharedCheck_4516_;
                        state = 3;
                        continue;
                    }
                }
                7 => {
                    v_binderType_4517_ = crate::leanh::lean_ctor_get(v_e_4463_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_4517_);
                    v_body_4518_ = crate::leanh::lean_ctor_get(v_e_4463_, 2);
                    crate::leanh::lean_inc_ref(v_body_4518_);
                    crate::leanh::lean_dec_ref_known(v_e_4463_, 3);
                    v___x_4519_ = 0;
                    v___x_4520_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_4517_, v___x_4519_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
                    v_a_4521_ = crate::leanh::lean_ctor_get(v___x_4520_, 0);
                    crate::leanh::lean_inc(v_a_4521_);
                    crate::leanh::lean_dec_ref(v___x_4520_);
                    if v_omitTopForall_4464_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        v___x_4535_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0;
                        v___x_4536_ = lean_string_dec_eq(v_a_4521_, v___x_4535_);
                        if v___x_4536_ == 0 {
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_4521_);
                            v___x_4537_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_4518_, v_omitTopForall_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
                            return v___x_4537_;
                        }
                    }
                }
                3 => {
                    v_u_4538_ = crate::leanh::lean_ctor_get(v_e_4463_, 0);
                    crate::leanh::lean_inc(v_u_4538_);
                    crate::leanh::lean_dec_ref_known(v_e_4463_, 1);
                    match crate::leanh::lean_obj_tag(v_u_4538_) {
                        0 => {
                            v___x_4539_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1;
                            v___x_4540_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4540_, 0, v___x_4539_);
                            return v___x_4540_;
                        }
                        1 => {
                            crate::leanh::lean_dec_ref_known(v_u_4538_, 1);
                            v___x_4541_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2;
                            v___x_4542_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4542_, 0, v___x_4541_);
                            return v___x_4542_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_u_4538_);
                            v___x_4543_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3;
                            v___x_4544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4544_, 0, v___x_4543_);
                            return v___x_4544_;
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_4463_);
                    v___x_4545_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0;
                    v___x_4546_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4546_, 0, v___x_4545_);
                    return v___x_4546_;
                }
            },
            1 => {
                crate::leanh::lean_inc(v_declName_4471_);
                v___x_4478_ = l_Lean_NameSet_insert(v_consts_4474_, v_declName_4471_);
                if v_isShared_4477_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4476_, 1, v___x_4478_);
                    v___x_4480_ = v___x_4476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4500_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_seen_4473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4500_, 1, v___x_4478_);
                    v___x_4480_ = v_reuseFailAlloc_4500_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4481_ = lean_st_ref_set(v_a_4465_, v___x_4480_);
                v___x_4482_ = lean_erase_macro_scopes(v_declName_4471_);
                if crate::leanh::lean_obj_tag(v___x_4482_) == 1 {
                    v_str_4483_ = crate::leanh::lean_ctor_get(v___x_4482_, 1);
                    crate::leanh::lean_inc_ref(v_str_4483_);
                    crate::leanh::lean_dec_ref_known(v___x_4482_, 2);
                    v___x_4484_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4485_ = lean_string_utf8_get(v_str_4483_, v___x_4484_);
                    v___x_4486_ = 97;
                    v___x_4487_ = lean_uint32_dec_le(v___x_4486_, v___x_4485_);
                    if v___x_4487_ == 0 {
                        v___x_4488_ = lean_string_utf8_set(v_str_4483_, v___x_4484_, v___x_4485_);
                        v___x_4489_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4489_, 0, v___x_4488_);
                        return v___x_4489_;
                    } else {
                        v___x_4490_ = 122;
                        v___x_4491_ = lean_uint32_dec_le(v___x_4485_, v___x_4490_);
                        if v___x_4491_ == 0 {
                            v___x_4492_ =
                                lean_string_utf8_set(v_str_4483_, v___x_4484_, v___x_4485_);
                            v___x_4493_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4493_, 0, v___x_4492_);
                            return v___x_4493_;
                        } else {
                            v___x_4494_ = 4294967264;
                            v___x_4495_ = lean_uint32_add(v___x_4485_, v___x_4494_);
                            v___x_4496_ =
                                lean_string_utf8_set(v_str_4483_, v___x_4484_, v___x_4495_);
                            v___x_4497_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4497_, 0, v___x_4496_);
                            return v___x_4497_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4482_);
                    v___x_4498_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0;
                    v___x_4499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4499_, 0, v___x_4498_);
                    return v___x_4499_;
                }
            }
            3 => {
                v___x_4512_ = lean_string_append(v_a_4506_, v_a_4508_);
                crate::leanh::lean_dec(v_a_4508_);
                if v_isShared_4511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4510_, 0, v___x_4512_);
                    v___x_4514_ = v___x_4510_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4512_);
                    v___x_4514_ = v_reuseFailAlloc_4515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4514_;
            }
            5 => {
                v___x_4523_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_4518_, v___x_4519_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
                v_a_4524_ = crate::leanh::lean_ctor_get(v___x_4523_, 0);
                v_isSharedCheck_4534_ = (!crate::leanh::lean_is_exclusive(v___x_4523_)) as u8;
                if v_isSharedCheck_4534_ == 0 {
                    v___x_4526_ = v___x_4523_;
                    v_isShared_4527_ = v_isSharedCheck_4534_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4524_);
                    crate::leanh::lean_dec(v___x_4523_);
                    v___x_4526_ = crate::leanh::lean_box(0);
                    v_isShared_4527_ = v_isSharedCheck_4534_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4528_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0;
                v___x_4529_ = lean_string_append(v___x_4528_, v_a_4521_);
                crate::leanh::lean_dec(v_a_4521_);
                v___x_4530_ = lean_string_append(v___x_4529_, v_a_4524_);
                crate::leanh::lean_dec(v_a_4524_);
                if v_isShared_4527_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4526_, 0, v___x_4530_);
                    v___x_4532_ = v___x_4526_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4533_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4530_);
                    v___x_4532_ = v_reuseFailAlloc_4533_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(
    mut v_e_4547_: *mut crate::leanh::LeanObject,
    mut v_omitTopForall_4548_: u8,
    mut v_a_4549_: *mut crate::leanh::LeanObject,
    mut v_a_4550_: *mut crate::leanh::LeanObject,
    mut v_a_4551_: *mut crate::leanh::LeanObject,
    mut v_a_4552_: *mut crate::leanh::LeanObject,
    mut v_a_4553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seen_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: u8 = 0;
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seen_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_consts_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4568_: u8 = 0;
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut v_isSharedCheck_4579_: u8 = 0;
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4555_ = lean_st_ref_get(v_a_4549_);
                v_seen_4556_ = crate::leanh::lean_ctor_get(v___x_4555_, 0);
                crate::leanh::lean_inc_ref(v_seen_4556_);
                crate::leanh::lean_dec(v___x_4555_);
                v___x_4557_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_seen_4556_, v_e_4547_);
                crate::leanh::lean_dec_ref(v_seen_4556_);
                if v___x_4557_ == 0 {
                    crate::leanh::lean_inc_ref(v_e_4547_);
                    v___x_4558_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_4547_, v_omitTopForall_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_);
                    v_a_4559_ = crate::leanh::lean_ctor_get(v___x_4558_, 0);
                    v_isSharedCheck_4579_ = (!crate::leanh::lean_is_exclusive(v___x_4558_)) as u8;
                    if v_isSharedCheck_4579_ == 0 {
                        v___x_4561_ = v___x_4558_;
                        v_isShared_4562_ = v_isSharedCheck_4579_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4559_);
                        crate::leanh::lean_dec(v___x_4558_);
                        v___x_4561_ = crate::leanh::lean_box(0);
                        v_isShared_4562_ = v_isSharedCheck_4579_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4547_);
                    v___x_4580_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0;
                    v___x_4581_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4581_, 0, v___x_4580_);
                    return v___x_4581_;
                }
            }
            1 => {
                v___x_4563_ = lean_st_ref_take(v_a_4549_);
                v_seen_4564_ = crate::leanh::lean_ctor_get(v___x_4563_, 0);
                v_consts_4565_ = crate::leanh::lean_ctor_get(v___x_4563_, 1);
                v_isSharedCheck_4578_ = (!crate::leanh::lean_is_exclusive(v___x_4563_)) as u8;
                if v_isSharedCheck_4578_ == 0 {
                    v___x_4567_ = v___x_4563_;
                    v_isShared_4568_ = v_isSharedCheck_4578_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_consts_4565_);
                    crate::leanh::lean_inc(v_seen_4564_);
                    crate::leanh::lean_dec(v___x_4563_);
                    v___x_4567_ = crate::leanh::lean_box(0);
                    v_isShared_4568_ = v_isSharedCheck_4578_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4569_ = crate::leanh::lean_box(0);
                v___x_4570_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_seen_4564_, v_e_4547_, v___x_4569_);
                if v_isShared_4568_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4567_, 0, v___x_4570_);
                    v___x_4572_ = v___x_4567_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4577_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___x_4570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 1, v_consts_4565_);
                    v___x_4572_ = v_reuseFailAlloc_4577_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4573_ = lean_st_ref_set(v_a_4549_, v___x_4572_);
                if v_isShared_4562_ == 0 {
                    v___x_4575_ = v___x_4561_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4576_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4559_);
                    v___x_4575_ = v_reuseFailAlloc_4576_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___boxed(
    mut v_e_4582_: *mut crate::leanh::LeanObject,
    mut v_omitTopForall_4583_: *mut crate::leanh::LeanObject,
    mut v_a_4584_: *mut crate::leanh::LeanObject,
    mut v_a_4585_: *mut crate::leanh::LeanObject,
    mut v_a_4586_: *mut crate::leanh::LeanObject,
    mut v_a_4587_: *mut crate::leanh::LeanObject,
    mut v_a_4588_: *mut crate::leanh::LeanObject,
    mut v_a_4589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_omitTopForall_boxed_4590_: u8 = 0;
    let mut v_res_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_omitTopForall_boxed_4590_ = (crate::leanh::lean_unbox(v_omitTopForall_4583_) as u8);
    v_res_4591_ =
        l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(
            v_e_4582_,
            v_omitTopForall_boxed_4590_,
            v_a_4584_,
            v_a_4585_,
            v_a_4586_,
            v_a_4587_,
            v_a_4588_,
        );
    crate::leanh::lean_dec(v_a_4588_);
    crate::leanh::lean_dec_ref(v_a_4587_);
    crate::leanh::lean_dec(v_a_4586_);
    crate::leanh::lean_dec_ref(v_a_4585_);
    crate::leanh::lean_dec(v_a_4584_);
    return v_res_4591_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___boxed(
    mut v_e_4592_: *mut crate::leanh::LeanObject,
    mut v_omitTopForall_4593_: *mut crate::leanh::LeanObject,
    mut v_a_4594_: *mut crate::leanh::LeanObject,
    mut v_a_4595_: *mut crate::leanh::LeanObject,
    mut v_a_4596_: *mut crate::leanh::LeanObject,
    mut v_a_4597_: *mut crate::leanh::LeanObject,
    mut v_a_4598_: *mut crate::leanh::LeanObject,
    mut v_a_4599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_omitTopForall_boxed_4600_: u8 = 0;
    let mut v_res_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_omitTopForall_boxed_4600_ = (crate::leanh::lean_unbox(v_omitTopForall_4593_) as u8);
    v_res_4601_ =
        l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(
            v_e_4592_,
            v_omitTopForall_boxed_4600_,
            v_a_4594_,
            v_a_4595_,
            v_a_4596_,
            v_a_4597_,
            v_a_4598_,
        );
    crate::leanh::lean_dec(v_a_4598_);
    crate::leanh::lean_dec_ref(v_a_4597_);
    crate::leanh::lean_dec(v_a_4596_);
    crate::leanh::lean_dec_ref(v_a_4595_);
    crate::leanh::lean_dec(v_a_4594_);
    return v_res_4601_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(
    mut v_00_u03b2_4602_: *mut crate::leanh::LeanObject,
    mut v_m_4603_: *mut crate::leanh::LeanObject,
    mut v_a_4604_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4605_: u8 = 0;
    v___x_4605_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_4603_, v_a_4604_);
    return v___x_4605_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___boxed(
    mut v_00_u03b2_4606_: *mut crate::leanh::LeanObject,
    mut v_m_4607_: *mut crate::leanh::LeanObject,
    mut v_a_4608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4609_: u8 = 0;
    let mut v_r_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4609_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(v_00_u03b2_4606_, v_m_4607_, v_a_4608_);
    crate::leanh::lean_dec_ref(v_a_4608_);
    crate::leanh::lean_dec_ref(v_m_4607_);
    v_r_4610_ = crate::leanh::lean_box((v_res_4609_) as usize);
    return v_r_4610_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1(
    mut v_00_u03b2_4611_: *mut crate::leanh::LeanObject,
    mut v_m_4612_: *mut crate::leanh::LeanObject,
    mut v_a_4613_: *mut crate::leanh::LeanObject,
    mut v_b_4614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4615_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_m_4612_, v_a_4613_, v_b_4614_);
    return v___x_4615_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter___redArg(
    mut v_e_4616_: *mut crate::leanh::LeanObject,
    mut v_h__1_4617_: *mut crate::leanh::LeanObject,
    mut v_h__2_4618_: *mut crate::leanh::LeanObject,
    mut v_h__3_4619_: *mut crate::leanh::LeanObject,
    mut v_h__4_4620_: *mut crate::leanh::LeanObject,
    mut v_h__5_4621_: *mut crate::leanh::LeanObject,
    mut v_h__6_4622_: *mut crate::leanh::LeanObject,
    mut v_h__7_4623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_e_4616_) {
        4 => {
            let mut v_declName_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_us_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_4623_);
            crate::leanh::lean_dec(v_h__6_4622_);
            crate::leanh::lean_dec(v_h__5_4621_);
            crate::leanh::lean_dec(v_h__4_4620_);
            crate::leanh::lean_dec(v_h__3_4619_);
            crate::leanh::lean_dec(v_h__2_4618_);
            v_declName_4624_ = crate::leanh::lean_ctor_get(v_e_4616_, 0);
            crate::leanh::lean_inc(v_declName_4624_);
            v_us_4625_ = crate::leanh::lean_ctor_get(v_e_4616_, 1);
            crate::leanh::lean_inc(v_us_4625_);
            crate::leanh::lean_dec_ref_known(v_e_4616_, 2);
            v___x_4626_ = crate::leanh::lean_apply_2(v_h__1_4617_, v_declName_4624_, v_us_4625_);
            return v___x_4626_;
        }
        5 => {
            let mut v_fn_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_arg_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_4623_);
            crate::leanh::lean_dec(v_h__6_4622_);
            crate::leanh::lean_dec(v_h__5_4621_);
            crate::leanh::lean_dec(v_h__4_4620_);
            crate::leanh::lean_dec(v_h__3_4619_);
            crate::leanh::lean_dec(v_h__1_4617_);
            v_fn_4627_ = crate::leanh::lean_ctor_get(v_e_4616_, 0);
            crate::leanh::lean_inc_ref(v_fn_4627_);
            v_arg_4628_ = crate::leanh::lean_ctor_get(v_e_4616_, 1);
            crate::leanh::lean_inc_ref(v_arg_4628_);
            crate::leanh::lean_dec_ref_known(v_e_4616_, 2);
            v___x_4629_ = crate::leanh::lean_apply_2(v_h__2_4618_, v_fn_4627_, v_arg_4628_);
            return v___x_4629_;
        }
        7 => {
            let mut v_binderName_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderType_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderInfo_4633_: u8 = 0;
            let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_4623_);
            crate::leanh::lean_dec(v_h__6_4622_);
            crate::leanh::lean_dec(v_h__5_4621_);
            crate::leanh::lean_dec(v_h__4_4620_);
            crate::leanh::lean_dec(v_h__2_4618_);
            crate::leanh::lean_dec(v_h__1_4617_);
            v_binderName_4630_ = crate::leanh::lean_ctor_get(v_e_4616_, 0);
            crate::leanh::lean_inc(v_binderName_4630_);
            v_binderType_4631_ = crate::leanh::lean_ctor_get(v_e_4616_, 1);
            crate::leanh::lean_inc_ref(v_binderType_4631_);
            v_body_4632_ = crate::leanh::lean_ctor_get(v_e_4616_, 2);
            crate::leanh::lean_inc_ref(v_body_4632_);
            v_binderInfo_4633_ = crate::leanh::lean_ctor_get_uint8(
                v_e_4616_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
            );
            crate::leanh::lean_dec_ref_known(v_e_4616_, 3);
            v___x_4634_ = crate::leanh::lean_box((v_binderInfo_4633_) as usize);
            v___x_4635_ = crate::leanh::lean_apply_4(
                v_h__3_4619_,
                v_binderName_4630_,
                v_binderType_4631_,
                v_body_4632_,
                v___x_4634_,
            );
            return v___x_4635_;
        }
        3 => {
            let mut v_u_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_4623_);
            crate::leanh::lean_dec(v_h__3_4619_);
            crate::leanh::lean_dec(v_h__2_4618_);
            crate::leanh::lean_dec(v_h__1_4617_);
            v_u_4636_ = crate::leanh::lean_ctor_get(v_e_4616_, 0);
            crate::leanh::lean_inc(v_u_4636_);
            crate::leanh::lean_dec_ref_known(v_e_4616_, 1);
            match crate::leanh::lean_obj_tag(v_u_4636_) {
                0 => {
                    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4622_);
                    crate::leanh::lean_dec(v_h__5_4621_);
                    v___x_4637_ = crate::leanh::lean_box(0);
                    v___x_4638_ = crate::leanh::lean_apply_1(v_h__4_4620_, v___x_4637_);
                    return v___x_4638_;
                }
                1 => {
                    let mut v_a_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4622_);
                    crate::leanh::lean_dec(v_h__4_4620_);
                    v_a_4639_ = crate::leanh::lean_ctor_get(v_u_4636_, 0);
                    crate::leanh::lean_inc(v_a_4639_);
                    crate::leanh::lean_dec_ref_known(v_u_4636_, 1);
                    v___x_4640_ = crate::leanh::lean_apply_1(v_h__5_4621_, v_a_4639_);
                    return v___x_4640_;
                }
                _ => {
                    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__5_4621_);
                    crate::leanh::lean_dec(v_h__4_4620_);
                    v___x_4641_ = crate::leanh::lean_apply_3(
                        v_h__6_4622_,
                        v_u_4636_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4641_;
                }
            }
        }
        _ => {
            let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_4622_);
            crate::leanh::lean_dec(v_h__5_4621_);
            crate::leanh::lean_dec(v_h__4_4620_);
            crate::leanh::lean_dec(v_h__3_4619_);
            crate::leanh::lean_dec(v_h__2_4618_);
            crate::leanh::lean_dec(v_h__1_4617_);
            v___x_4642_ = crate::leanh::lean_apply_7(
                v_h__7_4623_,
                v_e_4616_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_4642_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter(
    mut v_motive_4643_: *mut crate::leanh::LeanObject,
    mut v_e_4644_: *mut crate::leanh::LeanObject,
    mut v_h__1_4645_: *mut crate::leanh::LeanObject,
    mut v_h__2_4646_: *mut crate::leanh::LeanObject,
    mut v_h__3_4647_: *mut crate::leanh::LeanObject,
    mut v_h__4_4648_: *mut crate::leanh::LeanObject,
    mut v_h__5_4649_: *mut crate::leanh::LeanObject,
    mut v_h__6_4650_: *mut crate::leanh::LeanObject,
    mut v_h__7_4651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_e_4644_) {
        4 => {
            let mut v_declName_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_us_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_4651_);
            crate::leanh::lean_dec(v_h__6_4650_);
            crate::leanh::lean_dec(v_h__5_4649_);
            crate::leanh::lean_dec(v_h__4_4648_);
            crate::leanh::lean_dec(v_h__3_4647_);
            crate::leanh::lean_dec(v_h__2_4646_);
            v_declName_4652_ = crate::leanh::lean_ctor_get(v_e_4644_, 0);
            crate::leanh::lean_inc(v_declName_4652_);
            v_us_4653_ = crate::leanh::lean_ctor_get(v_e_4644_, 1);
            crate::leanh::lean_inc(v_us_4653_);
            crate::leanh::lean_dec_ref_known(v_e_4644_, 2);
            v___x_4654_ = crate::leanh::lean_apply_2(v_h__1_4645_, v_declName_4652_, v_us_4653_);
            return v___x_4654_;
        }
        5 => {
            let mut v_fn_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_arg_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_4651_);
            crate::leanh::lean_dec(v_h__6_4650_);
            crate::leanh::lean_dec(v_h__5_4649_);
            crate::leanh::lean_dec(v_h__4_4648_);
            crate::leanh::lean_dec(v_h__3_4647_);
            crate::leanh::lean_dec(v_h__1_4645_);
            v_fn_4655_ = crate::leanh::lean_ctor_get(v_e_4644_, 0);
            crate::leanh::lean_inc_ref(v_fn_4655_);
            v_arg_4656_ = crate::leanh::lean_ctor_get(v_e_4644_, 1);
            crate::leanh::lean_inc_ref(v_arg_4656_);
            crate::leanh::lean_dec_ref_known(v_e_4644_, 2);
            v___x_4657_ = crate::leanh::lean_apply_2(v_h__2_4646_, v_fn_4655_, v_arg_4656_);
            return v___x_4657_;
        }
        7 => {
            let mut v_binderName_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderType_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_body_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_binderInfo_4661_: u8 = 0;
            let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_4651_);
            crate::leanh::lean_dec(v_h__6_4650_);
            crate::leanh::lean_dec(v_h__5_4649_);
            crate::leanh::lean_dec(v_h__4_4648_);
            crate::leanh::lean_dec(v_h__2_4646_);
            crate::leanh::lean_dec(v_h__1_4645_);
            v_binderName_4658_ = crate::leanh::lean_ctor_get(v_e_4644_, 0);
            crate::leanh::lean_inc(v_binderName_4658_);
            v_binderType_4659_ = crate::leanh::lean_ctor_get(v_e_4644_, 1);
            crate::leanh::lean_inc_ref(v_binderType_4659_);
            v_body_4660_ = crate::leanh::lean_ctor_get(v_e_4644_, 2);
            crate::leanh::lean_inc_ref(v_body_4660_);
            v_binderInfo_4661_ = crate::leanh::lean_ctor_get_uint8(
                v_e_4644_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
            );
            crate::leanh::lean_dec_ref_known(v_e_4644_, 3);
            v___x_4662_ = crate::leanh::lean_box((v_binderInfo_4661_) as usize);
            v___x_4663_ = crate::leanh::lean_apply_4(
                v_h__3_4647_,
                v_binderName_4658_,
                v_binderType_4659_,
                v_body_4660_,
                v___x_4662_,
            );
            return v___x_4663_;
        }
        3 => {
            let mut v_u_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_4651_);
            crate::leanh::lean_dec(v_h__3_4647_);
            crate::leanh::lean_dec(v_h__2_4646_);
            crate::leanh::lean_dec(v_h__1_4645_);
            v_u_4664_ = crate::leanh::lean_ctor_get(v_e_4644_, 0);
            crate::leanh::lean_inc(v_u_4664_);
            crate::leanh::lean_dec_ref_known(v_e_4644_, 1);
            match crate::leanh::lean_obj_tag(v_u_4664_) {
                0 => {
                    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4650_);
                    crate::leanh::lean_dec(v_h__5_4649_);
                    v___x_4665_ = crate::leanh::lean_box(0);
                    v___x_4666_ = crate::leanh::lean_apply_1(v_h__4_4648_, v___x_4665_);
                    return v___x_4666_;
                }
                1 => {
                    let mut v_a_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4650_);
                    crate::leanh::lean_dec(v_h__4_4648_);
                    v_a_4667_ = crate::leanh::lean_ctor_get(v_u_4664_, 0);
                    crate::leanh::lean_inc(v_a_4667_);
                    crate::leanh::lean_dec_ref_known(v_u_4664_, 1);
                    v___x_4668_ = crate::leanh::lean_apply_1(v_h__5_4649_, v_a_4667_);
                    return v___x_4668_;
                }
                _ => {
                    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__5_4649_);
                    crate::leanh::lean_dec(v_h__4_4648_);
                    v___x_4669_ = crate::leanh::lean_apply_3(
                        v_h__6_4650_,
                        v_u_4664_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4669_;
                }
            }
        }
        _ => {
            let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_4650_);
            crate::leanh::lean_dec(v_h__5_4649_);
            crate::leanh::lean_dec(v_h__4_4648_);
            crate::leanh::lean_dec(v_h__3_4647_);
            crate::leanh::lean_dec(v_h__2_4646_);
            crate::leanh::lean_dec(v_h__1_4645_);
            v___x_4670_ = crate::leanh::lean_apply_7(
                v_h__7_4651_,
                v_e_4644_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_4670_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter___redArg(
    mut v_x_4671_: *mut crate::leanh::LeanObject,
    mut v_h__1_4672_: *mut crate::leanh::LeanObject,
    mut v_h__2_4673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4671_) == 1 {
        let mut v_pre_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4673_);
        v_pre_4674_ = crate::leanh::lean_ctor_get(v_x_4671_, 0);
        crate::leanh::lean_inc(v_pre_4674_);
        v_str_4675_ = crate::leanh::lean_ctor_get(v_x_4671_, 1);
        crate::leanh::lean_inc_ref(v_str_4675_);
        crate::leanh::lean_dec_ref_known(v_x_4671_, 2);
        v___x_4676_ = crate::leanh::lean_apply_2(v_h__1_4672_, v_pre_4674_, v_str_4675_);
        return v___x_4676_;
    } else {
        let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4672_);
        v___x_4677_ =
            crate::leanh::lean_apply_2(v_h__2_4673_, v_x_4671_, crate::leanh::lean_box(0));
        return v___x_4677_;
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter(
    mut v_motive_4678_: *mut crate::leanh::LeanObject,
    mut v_x_4679_: *mut crate::leanh::LeanObject,
    mut v_h__1_4680_: *mut crate::leanh::LeanObject,
    mut v_h__2_4681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4679_) == 1 {
        let mut v_pre_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4681_);
        v_pre_4682_ = crate::leanh::lean_ctor_get(v_x_4679_, 0);
        crate::leanh::lean_inc(v_pre_4682_);
        v_str_4683_ = crate::leanh::lean_ctor_get(v_x_4679_, 1);
        crate::leanh::lean_inc_ref(v_str_4683_);
        crate::leanh::lean_dec_ref_known(v_x_4679_, 2);
        v___x_4684_ = crate::leanh::lean_apply_2(v_h__1_4680_, v_pre_4682_, v_str_4683_);
        return v___x_4684_;
    } else {
        let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4680_);
        v___x_4685_ =
            crate::leanh::lean_apply_2(v_h__2_4681_, v_x_4679_, crate::leanh::lean_box(0));
        return v___x_4685_;
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(
    mut v_e_4686_: *mut crate::leanh::LeanObject,
    mut v_omitTopForall_4687_: u8,
    mut v_a_4688_: *mut crate::leanh::LeanObject,
    mut v_a_4689_: *mut crate::leanh::LeanObject,
    mut v_a_4690_: *mut crate::leanh::LeanObject,
    mut v_a_4691_: *mut crate::leanh::LeanObject,
    mut v_a_4692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4694_ =
        l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(
            v_e_4686_,
            v_omitTopForall_4687_,
            v_a_4688_,
            v_a_4689_,
            v_a_4690_,
            v_a_4691_,
            v_a_4692_,
        );
    return v___x_4694_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore___boxed(
    mut v_e_4695_: *mut crate::leanh::LeanObject,
    mut v_omitTopForall_4696_: *mut crate::leanh::LeanObject,
    mut v_a_4697_: *mut crate::leanh::LeanObject,
    mut v_a_4698_: *mut crate::leanh::LeanObject,
    mut v_a_4699_: *mut crate::leanh::LeanObject,
    mut v_a_4700_: *mut crate::leanh::LeanObject,
    mut v_a_4701_: *mut crate::leanh::LeanObject,
    mut v_a_4702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_omitTopForall_boxed_4703_: u8 = 0;
    let mut v_res_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_omitTopForall_boxed_4703_ = (crate::leanh::lean_unbox(v_omitTopForall_4696_) as u8);
    v_res_4704_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(
        v_e_4695_,
        v_omitTopForall_boxed_4703_,
        v_a_4697_,
        v_a_4698_,
        v_a_4699_,
        v_a_4700_,
        v_a_4701_,
    );
    crate::leanh::lean_dec(v_a_4701_);
    crate::leanh::lean_dec_ref(v_a_4700_);
    crate::leanh::lean_dec(v_a_4699_);
    crate::leanh::lean_dec_ref(v_a_4698_);
    crate::leanh::lean_dec(v_a_4697_);
    return v_res_4704_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(
    mut v_e_4706_: *mut crate::leanh::LeanObject,
    mut v_a_4707_: *mut crate::leanh::LeanObject,
    mut v_a_4708_: *mut crate::leanh::LeanObject,
    mut v_a_4709_: *mut crate::leanh::LeanObject,
    mut v_a_4710_: *mut crate::leanh::LeanObject,
    mut v_a_4711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderType_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: u8 = 0;
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4724_: u8 = 0;
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: u8 = 0;
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4729_: u8 = 0;
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4739_: u8 = 0;
    let mut v_unused_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4745_: u8 = 0;
    let mut v_a_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4749_: u8 = 0;
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4753_: u8 = 0;
    let mut v___x_4754_: u8 = 0;
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4759_: u8 = 0;
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4765_: u8 = 0;
    let mut v_a_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_4706_) == 7 {
                    v_binderType_4713_ = crate::leanh::lean_ctor_get(v_e_4706_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_4713_);
                    v_body_4714_ = crate::leanh::lean_ctor_get(v_e_4706_, 2);
                    crate::leanh::lean_inc_ref(v_body_4714_);
                    crate::leanh::lean_dec_ref_known(v_e_4706_, 3);
                    v___x_4715_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_body_4714_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
                    if crate::leanh::lean_obj_tag(v___x_4715_) == 0 {
                        v_a_4716_ = crate::leanh::lean_ctor_get(v___x_4715_, 0);
                        crate::leanh::lean_inc(v_a_4716_);
                        crate::leanh::lean_dec_ref_known(v___x_4715_, 1);
                        v_fst_4717_ = crate::leanh::lean_ctor_get(v_a_4716_, 0);
                        v_snd_4718_ = crate::leanh::lean_ctor_get(v_a_4716_, 1);
                        v___x_4719_ = 1;
                        v___x_4720_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_4713_, v___x_4719_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
                        if crate::leanh::lean_obj_tag(v___x_4720_) == 0 {
                            v_a_4721_ = crate::leanh::lean_ctor_get(v___x_4720_, 0);
                            v_isSharedCheck_4745_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4720_)) as u8;
                            if v_isSharedCheck_4745_ == 0 {
                                v___x_4723_ = v___x_4720_;
                                v_isShared_4724_ = v_isSharedCheck_4745_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4721_);
                                crate::leanh::lean_dec(v___x_4720_);
                                v___x_4723_ = crate::leanh::lean_box(0);
                                v_isShared_4724_ = v_isSharedCheck_4745_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4716_);
                            v_a_4746_ = crate::leanh::lean_ctor_get(v___x_4720_, 0);
                            v_isSharedCheck_4753_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4720_)) as u8;
                            if v_isSharedCheck_4753_ == 0 {
                                v___x_4748_ = v___x_4720_;
                                v_isShared_4749_ = v_isSharedCheck_4753_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4746_);
                                crate::leanh::lean_dec(v___x_4720_);
                                v___x_4748_ = crate::leanh::lean_box(0);
                                v_isShared_4749_ = v_isSharedCheck_4753_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_binderType_4713_);
                        return v___x_4715_;
                    }
                } else {
                    v___x_4754_ = 0;
                    v___x_4755_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_4706_, v___x_4754_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
                    if crate::leanh::lean_obj_tag(v___x_4755_) == 0 {
                        v_a_4756_ = crate::leanh::lean_ctor_get(v___x_4755_, 0);
                        v_isSharedCheck_4765_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4755_)) as u8;
                        if v_isSharedCheck_4765_ == 0 {
                            v___x_4758_ = v___x_4755_;
                            v_isShared_4759_ = v_isSharedCheck_4765_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4756_);
                            crate::leanh::lean_dec(v___x_4755_);
                            v___x_4758_ = crate::leanh::lean_box(0);
                            v_isShared_4759_ = v_isSharedCheck_4765_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_4766_ = crate::leanh::lean_ctor_get(v___x_4755_, 0);
                        v_isSharedCheck_4773_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4755_)) as u8;
                        if v_isSharedCheck_4773_ == 0 {
                            v___x_4768_ = v___x_4755_;
                            v_isShared_4769_ = v_isSharedCheck_4773_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4766_);
                            crate::leanh::lean_dec(v___x_4755_);
                            v___x_4768_ = crate::leanh::lean_box(0);
                            v_isShared_4769_ = v_isSharedCheck_4773_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4725_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0;
                v___x_4726_ = lean_string_dec_eq(v_a_4721_, v___x_4725_);
                if v___x_4726_ == 0 {
                    crate::leanh::lean_inc(v_snd_4718_);
                    crate::leanh::lean_inc(v_fst_4717_);
                    v_isSharedCheck_4739_ = (!crate::leanh::lean_is_exclusive(v_a_4716_)) as u8;
                    if v_isSharedCheck_4739_ == 0 {
                        v_unused_4740_ = crate::leanh::lean_ctor_get(v_a_4716_, 1);
                        crate::leanh::lean_dec(v_unused_4740_);
                        v_unused_4741_ = crate::leanh::lean_ctor_get(v_a_4716_, 0);
                        crate::leanh::lean_dec(v_unused_4741_);
                        v___x_4728_ = v_a_4716_;
                        v_isShared_4729_ = v_isSharedCheck_4739_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_4716_);
                        v___x_4728_ = crate::leanh::lean_box(0);
                        v_isShared_4729_ = v_isSharedCheck_4739_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4721_);
                    if v_isShared_4724_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4723_, 0, v_a_4716_);
                        v___x_4743_ = v___x_4723_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4744_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4716_);
                        v___x_4743_ = v_reuseFailAlloc_4744_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4730_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0;
                v___x_4731_ = lean_string_append(v___x_4730_, v_a_4721_);
                crate::leanh::lean_dec(v_a_4721_);
                v___x_4732_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4732_, 0, v___x_4731_);
                crate::leanh::lean_ctor_set(v___x_4732_, 1, v_fst_4717_);
                if v_isShared_4729_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4728_, 0, v___x_4732_);
                    v___x_4734_ = v___x_4728_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4738_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4738_, 0, v___x_4732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4738_, 1, v_snd_4718_);
                    v___x_4734_ = v_reuseFailAlloc_4738_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4724_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4723_, 0, v___x_4734_);
                    v___x_4736_ = v___x_4723_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4737_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4737_, 0, v___x_4734_);
                    v___x_4736_ = v_reuseFailAlloc_4737_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4736_;
            }
            5 => {
                return v___x_4743_;
            }
            6 => {
                if v_isShared_4749_ == 0 {
                    v___x_4751_ = v___x_4748_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4752_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
                    v___x_4751_ = v_reuseFailAlloc_4752_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4751_;
            }
            8 => {
                v___x_4760_ = crate::leanh::lean_box(0);
                v___x_4761_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4761_, 0, v___x_4760_);
                crate::leanh::lean_ctor_set(v___x_4761_, 1, v_a_4756_);
                if v_isShared_4759_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4758_, 0, v___x_4761_);
                    v___x_4763_ = v___x_4758_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4764_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 0, v___x_4761_);
                    v___x_4763_ = v_reuseFailAlloc_4764_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4763_;
            }
            10 => {
                if v_isShared_4769_ == 0 {
                    v___x_4771_ = v___x_4768_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4772_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
                    v___x_4771_ = v_reuseFailAlloc_4772_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___boxed(
    mut v_e_4774_: *mut crate::leanh::LeanObject,
    mut v_a_4775_: *mut crate::leanh::LeanObject,
    mut v_a_4776_: *mut crate::leanh::LeanObject,
    mut v_a_4777_: *mut crate::leanh::LeanObject,
    mut v_a_4778_: *mut crate::leanh::LeanObject,
    mut v_a_4779_: *mut crate::leanh::LeanObject,
    mut v_a_4780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4781_ =
        l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(
            v_e_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_,
        );
    crate::leanh::lean_dec(v_a_4779_);
    crate::leanh::lean_dec_ref(v_a_4778_);
    crate::leanh::lean_dec(v_a_4777_);
    crate::leanh::lean_dec_ref(v_a_4776_);
    crate::leanh::lean_dec(v_a_4775_);
    return v_res_4781_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(
    mut v_x_4782_: *mut crate::leanh::LeanObject,
    mut v_x_4783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4783_) == 0 {
                    return v_x_4782_;
                } else {
                    v_head_4784_ = crate::leanh::lean_ctor_get(v_x_4783_, 0);
                    v_tail_4785_ = crate::leanh::lean_ctor_get(v_x_4783_, 1);
                    v___x_4786_ = lean_string_append(v_x_4782_, v_head_4784_);
                    v_x_4782_ = v___x_4786_;
                    v_x_4783_ = v_tail_4785_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0___boxed(
    mut v_x_4788_: *mut crate::leanh::LeanObject,
    mut v_x_4789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4790_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v_x_4788_, v_x_4789_);
    crate::leanh::lean_dec(v_x_4789_);
    return v_res_4790_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(
    mut v_e_4791_: *mut crate::leanh::LeanObject,
    mut v_a_4792_: *mut crate::leanh::LeanObject,
    mut v_a_4793_: *mut crate::leanh::LeanObject,
    mut v_a_4794_: *mut crate::leanh::LeanObject,
    mut v_a_4795_: *mut crate::leanh::LeanObject,
    mut v_a_4796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4802_: u8 = 0;
    let mut v_fst_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4811_: u8 = 0;
    let mut v_a_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4815_: u8 = 0;
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4798_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_);
                if crate::leanh::lean_obj_tag(v___x_4798_) == 0 {
                    v_a_4799_ = crate::leanh::lean_ctor_get(v___x_4798_, 0);
                    v_isSharedCheck_4811_ = (!crate::leanh::lean_is_exclusive(v___x_4798_)) as u8;
                    if v_isSharedCheck_4811_ == 0 {
                        v___x_4801_ = v___x_4798_;
                        v_isShared_4802_ = v_isSharedCheck_4811_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4799_);
                        crate::leanh::lean_dec(v___x_4798_);
                        v___x_4801_ = crate::leanh::lean_box(0);
                        v_isShared_4802_ = v_isSharedCheck_4811_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4812_ = crate::leanh::lean_ctor_get(v___x_4798_, 0);
                    v_isSharedCheck_4819_ = (!crate::leanh::lean_is_exclusive(v___x_4798_)) as u8;
                    if v_isSharedCheck_4819_ == 0 {
                        v___x_4814_ = v___x_4798_;
                        v_isShared_4815_ = v_isSharedCheck_4819_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4812_);
                        crate::leanh::lean_dec(v___x_4798_);
                        v___x_4814_ = crate::leanh::lean_box(0);
                        v_isShared_4815_ = v_isSharedCheck_4819_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4803_ = crate::leanh::lean_ctor_get(v_a_4799_, 0);
                crate::leanh::lean_inc(v_fst_4803_);
                v_snd_4804_ = crate::leanh::lean_ctor_get(v_a_4799_, 1);
                crate::leanh::lean_inc(v_snd_4804_);
                crate::leanh::lean_dec(v_a_4799_);
                v___x_4805_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0;
                v___x_4806_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v___x_4805_, v_fst_4803_);
                crate::leanh::lean_dec(v_fst_4803_);
                v___x_4807_ = lean_string_append(v_snd_4804_, v___x_4806_);
                crate::leanh::lean_dec_ref(v___x_4806_);
                if v_isShared_4802_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4801_, 0, v___x_4807_);
                    v___x_4809_ = v___x_4801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4810_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4810_, 0, v___x_4807_);
                    v___x_4809_ = v_reuseFailAlloc_4810_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4809_;
            }
            3 => {
                if v_isShared_4815_ == 0 {
                    v___x_4817_ = v___x_4814_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4818_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4812_);
                    v___x_4817_ = v_reuseFailAlloc_4818_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux___boxed(
    mut v_e_4820_: *mut crate::leanh::LeanObject,
    mut v_a_4821_: *mut crate::leanh::LeanObject,
    mut v_a_4822_: *mut crate::leanh::LeanObject,
    mut v_a_4823_: *mut crate::leanh::LeanObject,
    mut v_a_4824_: *mut crate::leanh::LeanObject,
    mut v_a_4825_: *mut crate::leanh::LeanObject,
    mut v_a_4826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4827_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(
        v_e_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_,
    );
    crate::leanh::lean_dec(v_a_4825_);
    crate::leanh::lean_dec_ref(v_a_4824_);
    crate::leanh::lean_dec(v_a_4823_);
    crate::leanh::lean_dec_ref(v_a_4822_);
    crate::leanh::lean_dec(v_a_4821_);
    return v_res_4827_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(
    mut v_ns_4828_: *mut crate::leanh::LeanObject,
    mut v_a_4829_: *mut crate::leanh::LeanObject,
    mut v_a_4830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: u8 = 0;
    let mut v___x_4838_: u8 = 0;
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seen_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_consts_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4845_: u8 = 0;
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4856_: u8 = 0;
    let mut v_pre_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_ns_4828_) {
                0 => {
                    v___x_4832_ = crate::leanh::lean_box(0);
                    v___x_4833_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4833_, 0, v___x_4832_);
                    return v___x_4833_;
                }
                1 => {
                    v_pre_4834_ = crate::leanh::lean_ctor_get(v_ns_4828_, 0);
                    crate::leanh::lean_inc(v_pre_4834_);
                    v___x_4835_ = lean_st_ref_get(v_a_4830_);
                    v_env_4836_ = crate::leanh::lean_ctor_get(v___x_4835_, 0);
                    crate::leanh::lean_inc_ref(v_env_4836_);
                    crate::leanh::lean_dec(v___x_4835_);
                    v___x_4837_ = 1;
                    crate::leanh::lean_inc_ref(v_ns_4828_);
                    v___x_4838_ = l_Lean_Environment_contains(v_env_4836_, v_ns_4828_, v___x_4837_);
                    if v___x_4838_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_ns_4828_, 2);
                        v_ns_4828_ = v_pre_4834_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4840_ = lean_st_ref_take(v_a_4829_);
                        v_seen_4841_ = crate::leanh::lean_ctor_get(v___x_4840_, 0);
                        v_consts_4842_ = crate::leanh::lean_ctor_get(v___x_4840_, 1);
                        v_isSharedCheck_4856_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4840_)) as u8;
                        if v_isSharedCheck_4856_ == 0 {
                            v___x_4844_ = v___x_4840_;
                            v_isShared_4845_ = v_isSharedCheck_4856_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_consts_4842_);
                            crate::leanh::lean_inc(v_seen_4841_);
                            crate::leanh::lean_dec(v___x_4840_);
                            v___x_4844_ = crate::leanh::lean_box(0);
                            v_isShared_4845_ = v_isSharedCheck_4856_;
                            state = 1;
                            continue;
                        }
                    }
                }
                _ => {
                    v_pre_4857_ = crate::leanh::lean_ctor_get(v_ns_4828_, 0);
                    crate::leanh::lean_inc(v_pre_4857_);
                    crate::leanh::lean_dec_ref_known(v_ns_4828_, 2);
                    v_ns_4828_ = v_pre_4857_;
                    state = 0;
                    continue;
                }
            },
            1 => {
                v___x_4846_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_ns_4828_);
                v___x_4847_ = l_Lean_Expr_const___override(v_ns_4828_, v___x_4846_);
                v___x_4848_ = crate::leanh::lean_box(0);
                v___x_4849_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_seen_4841_, v___x_4847_, v___x_4848_);
                v___x_4850_ = l_Lean_NameSet_insert(v_consts_4842_, v_ns_4828_);
                if v_isShared_4845_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4844_, 1, v___x_4850_);
                    crate::leanh::lean_ctor_set(v___x_4844_, 0, v___x_4849_);
                    v___x_4852_ = v___x_4844_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4855_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4855_, 0, v___x_4849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4855_, 1, v___x_4850_);
                    v___x_4852_ = v_reuseFailAlloc_4855_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4853_ = lean_st_ref_set(v_a_4829_, v___x_4852_);
                v_ns_4828_ = v_pre_4834_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg___boxed(
    mut v_ns_4859_: *mut crate::leanh::LeanObject,
    mut v_a_4860_: *mut crate::leanh::LeanObject,
    mut v_a_4861_: *mut crate::leanh::LeanObject,
    mut v_a_4862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4863_ =
        l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(
            v_ns_4859_, v_a_4860_, v_a_4861_,
        );
    crate::leanh::lean_dec(v_a_4861_);
    crate::leanh::lean_dec(v_a_4860_);
    return v_res_4863_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(
    mut v_ns_4864_: *mut crate::leanh::LeanObject,
    mut v_a_4865_: *mut crate::leanh::LeanObject,
    mut v_a_4866_: *mut crate::leanh::LeanObject,
    mut v_a_4867_: *mut crate::leanh::LeanObject,
    mut v_a_4868_: *mut crate::leanh::LeanObject,
    mut v_a_4869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4871_ =
        l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(
            v_ns_4864_, v_a_4865_, v_a_4869_,
        );
    return v___x_4871_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___boxed(
    mut v_ns_4872_: *mut crate::leanh::LeanObject,
    mut v_a_4873_: *mut crate::leanh::LeanObject,
    mut v_a_4874_: *mut crate::leanh::LeanObject,
    mut v_a_4875_: *mut crate::leanh::LeanObject,
    mut v_a_4876_: *mut crate::leanh::LeanObject,
    mut v_a_4877_: *mut crate::leanh::LeanObject,
    mut v_a_4878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4879_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(
        v_ns_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_,
    );
    crate::leanh::lean_dec(v_a_4877_);
    crate::leanh::lean_dec_ref(v_a_4876_);
    crate::leanh::lean_dec(v_a_4875_);
    crate::leanh::lean_dec_ref(v_a_4874_);
    crate::leanh::lean_dec(v_a_4873_);
    return v_res_4879_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(
    mut v_e_4880_: *mut crate::leanh::LeanObject,
    mut v___y_4881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4883_: u8 = 0;
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4897_: u8 = 0;
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4903_: u8 = 0;
    let mut v_unused_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4883_ = l_Lean_Expr_hasMVar(v_e_4880_);
                if v___x_4883_ == 0 {
                    v___x_4884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4884_, 0, v_e_4880_);
                    return v___x_4884_;
                } else {
                    v___x_4885_ = lean_st_ref_get(v___y_4881_);
                    v_mctx_4886_ = crate::leanh::lean_ctor_get(v___x_4885_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_4886_);
                    crate::leanh::lean_dec(v___x_4885_);
                    v___x_4887_ = l_Lean_instantiateMVarsCore(v_mctx_4886_, v_e_4880_);
                    v_fst_4888_ = crate::leanh::lean_ctor_get(v___x_4887_, 0);
                    crate::leanh::lean_inc(v_fst_4888_);
                    v_snd_4889_ = crate::leanh::lean_ctor_get(v___x_4887_, 1);
                    crate::leanh::lean_inc(v_snd_4889_);
                    crate::leanh::lean_dec_ref(v___x_4887_);
                    v___x_4890_ = lean_st_ref_take(v___y_4881_);
                    v_cache_4891_ = crate::leanh::lean_ctor_get(v___x_4890_, 1);
                    v_zetaDeltaFVarIds_4892_ = crate::leanh::lean_ctor_get(v___x_4890_, 2);
                    v_postponed_4893_ = crate::leanh::lean_ctor_get(v___x_4890_, 3);
                    v_diag_4894_ = crate::leanh::lean_ctor_get(v___x_4890_, 4);
                    v_isSharedCheck_4903_ = (!crate::leanh::lean_is_exclusive(v___x_4890_)) as u8;
                    if v_isSharedCheck_4903_ == 0 {
                        v_unused_4904_ = crate::leanh::lean_ctor_get(v___x_4890_, 0);
                        crate::leanh::lean_dec(v_unused_4904_);
                        v___x_4896_ = v___x_4890_;
                        v_isShared_4897_ = v_isSharedCheck_4903_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_4894_);
                        crate::leanh::lean_inc(v_postponed_4893_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_4892_);
                        crate::leanh::lean_inc(v_cache_4891_);
                        crate::leanh::lean_dec(v___x_4890_);
                        v___x_4896_ = crate::leanh::lean_box(0);
                        v_isShared_4897_ = v_isSharedCheck_4903_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4897_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4896_, 0, v_snd_4889_);
                    v___x_4899_ = v___x_4896_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4902_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_snd_4889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 1, v_cache_4891_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4902_,
                        2,
                        v_zetaDeltaFVarIds_4892_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 3, v_postponed_4893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 4, v_diag_4894_);
                    v___x_4899_ = v_reuseFailAlloc_4902_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4900_ = lean_st_ref_set(v___y_4881_, v___x_4899_);
                v___x_4901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4901_, 0, v_fst_4888_);
                return v___x_4901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg___boxed(
    mut v_e_4905_: *mut crate::leanh::LeanObject,
    mut v___y_4906_: *mut crate::leanh::LeanObject,
    mut v___y_4907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4908_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_4905_, v___y_4906_);
    crate::leanh::lean_dec(v___y_4906_);
    return v_res_4908_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(
    mut v_e_4909_: *mut crate::leanh::LeanObject,
    mut v___y_4910_: *mut crate::leanh::LeanObject,
    mut v___y_4911_: *mut crate::leanh::LeanObject,
    mut v___y_4912_: *mut crate::leanh::LeanObject,
    mut v___y_4913_: *mut crate::leanh::LeanObject,
    mut v___y_4914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4916_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_4909_, v___y_4912_);
    return v___x_4916_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___boxed(
    mut v_e_4917_: *mut crate::leanh::LeanObject,
    mut v___y_4918_: *mut crate::leanh::LeanObject,
    mut v___y_4919_: *mut crate::leanh::LeanObject,
    mut v___y_4920_: *mut crate::leanh::LeanObject,
    mut v___y_4921_: *mut crate::leanh::LeanObject,
    mut v___y_4922_: *mut crate::leanh::LeanObject,
    mut v___y_4923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4924_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(v_e_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_);
    crate::leanh::lean_dec(v___y_4922_);
    crate::leanh::lean_dec_ref(v___y_4921_);
    crate::leanh::lean_dec(v___y_4920_);
    crate::leanh::lean_dec_ref(v___y_4919_);
    crate::leanh::lean_dec(v___y_4918_);
    return v_res_4924_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(
    mut v_e_4925_: *mut crate::leanh::LeanObject,
    mut v_a_4926_: *mut crate::leanh::LeanObject,
    mut v_a_4927_: *mut crate::leanh::LeanObject,
    mut v_a_4928_: *mut crate::leanh::LeanObject,
    mut v_a_4929_: *mut crate::leanh::LeanObject,
    mut v_a_4930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4932_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_4925_, v_a_4928_);
                v_a_4933_ = crate::leanh::lean_ctor_get(v___x_4932_, 0);
                crate::leanh::lean_inc(v_a_4933_);
                crate::leanh::lean_dec_ref(v___x_4932_);
                v_currNamespace_4934_ = crate::leanh::lean_ctor_get(v_a_4929_, 6);
                crate::leanh::lean_inc(v_currNamespace_4934_);
                v___x_4935_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_currNamespace_4934_, v_a_4926_, v_a_4930_);
                crate::leanh::lean_dec_ref(v___x_4935_);
                v___x_4936_ =
                    l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(
                        v_a_4933_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4936_) == 0 {
                    v_a_4937_ = crate::leanh::lean_ctor_get(v___x_4936_, 0);
                    crate::leanh::lean_inc(v_a_4937_);
                    crate::leanh::lean_dec_ref_known(v___x_4936_, 1);
                    v___x_4938_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_a_4937_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
                    return v___x_4938_;
                } else {
                    v_a_4939_ = crate::leanh::lean_ctor_get(v___x_4936_, 0);
                    v_isSharedCheck_4946_ = (!crate::leanh::lean_is_exclusive(v___x_4936_)) as u8;
                    if v_isSharedCheck_4946_ == 0 {
                        v___x_4941_ = v___x_4936_;
                        v_isShared_4942_ = v_isSharedCheck_4946_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4939_);
                        crate::leanh::lean_dec(v___x_4936_);
                        v___x_4941_ = crate::leanh::lean_box(0);
                        v_isShared_4942_ = v_isSharedCheck_4946_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4942_ == 0 {
                    v___x_4944_ = v___x_4941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4945_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_a_4939_);
                    v___x_4944_ = v_reuseFailAlloc_4945_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName___boxed(
    mut v_e_4947_: *mut crate::leanh::LeanObject,
    mut v_a_4948_: *mut crate::leanh::LeanObject,
    mut v_a_4949_: *mut crate::leanh::LeanObject,
    mut v_a_4950_: *mut crate::leanh::LeanObject,
    mut v_a_4951_: *mut crate::leanh::LeanObject,
    mut v_a_4952_: *mut crate::leanh::LeanObject,
    mut v_a_4953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4954_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(
        v_e_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_,
    );
    crate::leanh::lean_dec(v_a_4952_);
    crate::leanh::lean_dec_ref(v_a_4951_);
    crate::leanh::lean_dec(v_a_4950_);
    crate::leanh::lean_dec_ref(v_a_4949_);
    crate::leanh::lean_dec(v_a_4948_);
    return v_res_4954_;
}
pub unsafe fn l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(
    mut v_x_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: u32 = 0;
    let mut v___x_4965_: u32 = 0;
    let mut v___x_4966_: u8 = 0;
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: u32 = 0;
    let mut v___x_4970_: u8 = 0;
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: u32 = 0;
    let mut v___x_4974_: u32 = 0;
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4956_) {
                0 => {
                    v___x_4957_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0;
                    return v___x_4957_;
                }
                1 => {
                    v_pre_4958_ = crate::leanh::lean_ctor_get(v_x_4956_, 0);
                    crate::leanh::lean_inc(v_pre_4958_);
                    v_str_4959_ = crate::leanh::lean_ctor_get(v_x_4956_, 1);
                    crate::leanh::lean_inc_ref(v_str_4959_);
                    crate::leanh::lean_dec_ref_known(v_x_4956_, 2);
                    v___x_4960_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v_pre_4958_);
                    v___x_4961_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0;
                    v___x_4962_ = lean_string_append(v___x_4960_, v___x_4961_);
                    v___x_4963_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4964_ = lean_string_utf8_get(v_str_4959_, v___x_4963_);
                    v___x_4965_ = 65;
                    v___x_4966_ = lean_uint32_dec_le(v___x_4965_, v___x_4964_);
                    if v___x_4966_ == 0 {
                        v___x_4967_ = lean_string_utf8_set(v_str_4959_, v___x_4963_, v___x_4964_);
                        v___x_4968_ = lean_string_append(v___x_4962_, v___x_4967_);
                        crate::leanh::lean_dec_ref(v___x_4967_);
                        return v___x_4968_;
                    } else {
                        v___x_4969_ = 90;
                        v___x_4970_ = lean_uint32_dec_le(v___x_4964_, v___x_4969_);
                        if v___x_4970_ == 0 {
                            v___x_4971_ =
                                lean_string_utf8_set(v_str_4959_, v___x_4963_, v___x_4964_);
                            v___x_4972_ = lean_string_append(v___x_4962_, v___x_4971_);
                            crate::leanh::lean_dec_ref(v___x_4971_);
                            return v___x_4972_;
                        } else {
                            v___x_4973_ = 32;
                            v___x_4974_ = lean_uint32_add(v___x_4964_, v___x_4973_);
                            v___x_4975_ =
                                lean_string_utf8_set(v_str_4959_, v___x_4963_, v___x_4974_);
                            v___x_4976_ = lean_string_append(v___x_4962_, v___x_4975_);
                            crate::leanh::lean_dec_ref(v___x_4975_);
                            return v___x_4976_;
                        }
                    }
                }
                _ => {
                    v_pre_4977_ = crate::leanh::lean_ctor_get(v_x_4956_, 0);
                    crate::leanh::lean_inc(v_pre_4977_);
                    crate::leanh::lean_dec_ref_known(v_x_4956_, 2);
                    v_x_4956_ = v_pre_4977_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(
    mut v___y_4979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4981_ = lean_st_ref_get(v___y_4979_);
    v_env_4982_ = crate::leanh::lean_ctor_get(v___x_4981_, 0);
    crate::leanh::lean_inc_ref(v_env_4982_);
    crate::leanh::lean_dec(v___x_4981_);
    v___x_4983_ = l_Lean_Environment_header(v_env_4982_);
    crate::leanh::lean_dec_ref(v_env_4982_);
    v_mainModule_4984_ = crate::leanh::lean_ctor_get(v___x_4983_, 0);
    crate::leanh::lean_inc(v_mainModule_4984_);
    crate::leanh::lean_dec_ref(v___x_4983_);
    v___x_4985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4985_, 0, v_mainModule_4984_);
    return v___x_4985_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg___boxed(
    mut v___y_4986_: *mut crate::leanh::LeanObject,
    mut v___y_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4988_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_4986_);
    crate::leanh::lean_dec(v___y_4986_);
    return v_res_4988_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(
    mut v___y_4989_: *mut crate::leanh::LeanObject,
    mut v___y_4990_: *mut crate::leanh::LeanObject,
    mut v___y_4991_: *mut crate::leanh::LeanObject,
    mut v___y_4992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4994_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_4992_);
    return v___x_4994_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___boxed(
    mut v___y_4995_: *mut crate::leanh::LeanObject,
    mut v___y_4996_: *mut crate::leanh::LeanObject,
    mut v___y_4997_: *mut crate::leanh::LeanObject,
    mut v___y_4998_: *mut crate::leanh::LeanObject,
    mut v___y_4999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5000_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(
            v___y_4995_,
            v___y_4996_,
            v___y_4997_,
            v___y_4998_,
        );
    crate::leanh::lean_dec(v___y_4998_);
    crate::leanh::lean_dec_ref(v___y_4997_);
    crate::leanh::lean_dec(v___y_4996_);
    crate::leanh::lean_dec_ref(v___y_4995_);
    return v_res_5000_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(
    mut v_x_5001_: *mut crate::leanh::LeanObject,
    mut v_x_5002_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_5001_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_5002_) == 0 {
            let mut v___x_5003_: u8 = 0;
            v___x_5003_ = 1;
            return v___x_5003_;
        } else {
            let mut v___x_5004_: u8 = 0;
            v___x_5004_ = 0;
            return v___x_5004_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_5002_) == 0 {
            let mut v___x_5005_: u8 = 0;
            v___x_5005_ = 0;
            return v___x_5005_;
        } else {
            let mut v_val_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5008_: u8 = 0;
            v_val_5006_ = crate::leanh::lean_ctor_get(v_x_5001_, 0);
            v_val_5007_ = crate::leanh::lean_ctor_get(v_x_5002_, 0);
            v___x_5008_ = lean_name_eq(v_val_5006_, v_val_5007_);
            return v___x_5008_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2___boxed(
    mut v_x_5009_: *mut crate::leanh::LeanObject,
    mut v_x_5010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5011_: u8 = 0;
    let mut v_r_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5011_ =
        l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(
            v_x_5009_, v_x_5010_,
        );
    crate::leanh::lean_dec(v_x_5010_);
    crate::leanh::lean_dec(v_x_5009_);
    v_r_5012_ = crate::leanh::lean_box((v_res_5011_) as usize);
    return v_r_5012_;
}
pub unsafe fn l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(
    mut v_e_5013_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_5013_) == 4 {
        let mut v_declName_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5015_: u8 = 0;
        v_declName_5014_ = crate::leanh::lean_ctor_get(v_e_5013_, 0);
        v___x_5015_ = l_Lean_Name_hasMacroScopes(v_declName_5014_);
        return v___x_5015_;
    } else {
        let mut v___x_5016_: u8 = 0;
        v___x_5016_ = 0;
        return v___x_5016_;
    }
}
pub unsafe fn l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0___boxed(
    mut v_e_5017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5018_: u8 = 0;
    let mut v_r_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5018_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(v_e_5017_);
    crate::leanh::lean_dec_ref(v_e_5017_);
    v_r_5019_ = crate::leanh::lean_box((v_res_5018_) as usize);
    return v_r_5019_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(
    mut v_as_5020_: *mut crate::leanh::LeanObject,
    mut v_i_5021_: usize,
    mut v_stop_5022_: usize,
) -> u8 {
    let mut v___x_5023_: u8 = 0;
    let mut v___x_5024_: u8 = 0;
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: usize = 0;
    let mut v___x_5027_: usize = 0;
    let mut v___x_5029_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5023_ = lean_usize_dec_eq(v_i_5021_, v_stop_5022_);
                if v___x_5023_ == 0 {
                    v___x_5024_ = 1;
                    v___x_5025_ = lean_array_uget_borrowed(v_as_5020_, v_i_5021_);
                    if crate::leanh::lean_obj_tag(v___x_5025_) == 0 {
                        return v___x_5024_;
                    } else {
                        if v___x_5023_ == 0 {
                            v___x_5026_ = 1usize;
                            v___x_5027_ = lean_usize_add(v_i_5021_, v___x_5026_);
                            v_i_5021_ = v___x_5027_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_5024_;
                        }
                    }
                } else {
                    v___x_5029_ = 0;
                    return v___x_5029_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5___boxed(
    mut v_as_5030_: *mut crate::leanh::LeanObject,
    mut v_i_5031_: *mut crate::leanh::LeanObject,
    mut v_stop_5032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5033_: usize = 0;
    let mut v_stop_boxed_5034_: usize = 0;
    let mut v_res_5035_: u8 = 0;
    let mut v_r_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5033_ = crate::leanh::lean_unbox_usize(v_i_5031_);
    crate::leanh::lean_dec(v_i_5031_);
    v_stop_boxed_5034_ = crate::leanh::lean_unbox_usize(v_stop_5032_);
    crate::leanh::lean_dec(v_stop_5032_);
    v_res_5035_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_as_5030_, v_i_boxed_5033_, v_stop_boxed_5034_);
    crate::leanh::lean_dec_ref(v_as_5030_);
    v_r_5036_ = crate::leanh::lean_box((v_res_5035_) as usize);
    return v_r_5036_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(
    mut v___x_5037_: *mut crate::leanh::LeanObject,
    mut v_as_5038_: *mut crate::leanh::LeanObject,
    mut v_i_5039_: usize,
    mut v_stop_5040_: usize,
) -> u8 {
    let mut v___x_5041_: u8 = 0;
    let mut v___x_5042_: u8 = 0;
    let mut v___y_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: u8 = 0;
    let mut v___x_5047_: usize = 0;
    let mut v___x_5048_: usize = 0;
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5054_: u8 = 0;
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut v___x_5060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5041_ = lean_usize_dec_eq(v_i_5039_, v_stop_5040_);
                if v___x_5041_ == 0 {
                    v___x_5042_ = 1;
                    v___x_5050_ = lean_array_uget(v_as_5038_, v_i_5039_);
                    if crate::leanh::lean_obj_tag(v___x_5050_) == 0 {
                        v___y_5044_ = v___x_5050_;
                        state = 1;
                        continue;
                    } else {
                        v_val_5051_ = crate::leanh::lean_ctor_get(v___x_5050_, 0);
                        v_isSharedCheck_5059_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5050_)) as u8;
                        if v_isSharedCheck_5059_ == 0 {
                            v___x_5053_ = v___x_5050_;
                            v_isShared_5054_ = v_isSharedCheck_5059_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5051_);
                            crate::leanh::lean_dec(v___x_5050_);
                            v___x_5053_ = crate::leanh::lean_box(0);
                            v_isShared_5054_ = v_isSharedCheck_5059_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5037_);
                    v___x_5060_ = 0;
                    return v___x_5060_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___x_5037_);
                v___x_5045_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5045_, 0, v___x_5037_);
                v___x_5046_ = l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v___y_5044_, v___x_5045_);
                crate::leanh::lean_dec_ref_known(v___x_5045_, 1);
                crate::leanh::lean_dec(v___y_5044_);
                if v___x_5046_ == 0 {
                    v___x_5047_ = 1usize;
                    v___x_5048_ = lean_usize_add(v_i_5039_, v___x_5047_);
                    v_i_5039_ = v___x_5048_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_5037_);
                    return v___x_5042_;
                }
            }
            2 => {
                v___x_5055_ = l_Lean_Name_getRoot(v_val_5051_);
                crate::leanh::lean_dec(v_val_5051_);
                if v_isShared_5054_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5053_, 0, v___x_5055_);
                    v___x_5057_ = v___x_5053_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5058_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5055_);
                    v___x_5057_ = v_reuseFailAlloc_5058_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_5044_ = v___x_5057_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4___boxed(
    mut v___x_5061_: *mut crate::leanh::LeanObject,
    mut v_as_5062_: *mut crate::leanh::LeanObject,
    mut v_i_5063_: *mut crate::leanh::LeanObject,
    mut v_stop_5064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5065_: usize = 0;
    let mut v_stop_boxed_5066_: usize = 0;
    let mut v_res_5067_: u8 = 0;
    let mut v_r_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5065_ = crate::leanh::lean_unbox_usize(v_i_5063_);
    crate::leanh::lean_dec(v_i_5063_);
    v_stop_boxed_5066_ = crate::leanh::lean_unbox_usize(v_stop_5064_);
    crate::leanh::lean_dec(v_stop_5064_);
    v_res_5067_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_5061_, v_as_5062_, v_i_boxed_5065_, v_stop_boxed_5066_);
    crate::leanh::lean_dec_ref(v_as_5062_);
    v_r_5068_ = crate::leanh::lean_box((v_res_5067_) as usize);
    return v_r_5068_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5069_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5069_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5070_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
    v___x_5071_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5071_, 0, v___x_5070_);
    return v___x_5071_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5072_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
    v___x_5073_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5074_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5074_, 0, v___x_5073_);
    crate::leanh::lean_ctor_set(v___x_5074_, 1, v___x_5073_);
    crate::leanh::lean_ctor_set(v___x_5074_, 2, v___x_5073_);
    crate::leanh::lean_ctor_set(v___x_5074_, 3, v___x_5073_);
    crate::leanh::lean_ctor_set(v___x_5074_, 4, v___x_5072_);
    crate::leanh::lean_ctor_set(v___x_5074_, 5, v___x_5072_);
    crate::leanh::lean_ctor_set(v___x_5074_, 6, v___x_5072_);
    crate::leanh::lean_ctor_set(v___x_5074_, 7, v___x_5072_);
    crate::leanh::lean_ctor_set(v___x_5074_, 8, v___x_5072_);
    crate::leanh::lean_ctor_set(v___x_5074_, 9, v___x_5072_);
    return v___x_5074_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5075_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5076_ = lean_mk_empty_array_with_capacity(v___x_5075_);
    v___x_5077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5077_, 0, v___x_5076_);
    return v___x_5077_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5078_: usize = 0;
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5078_ = 5usize;
    v___x_5079_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5080_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5081_ = lean_mk_empty_array_with_capacity(v___x_5080_);
    v___x_5082_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
    v___x_5083_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_5083_, 0, v___x_5082_);
    crate::leanh::lean_ctor_set(v___x_5083_, 1, v___x_5081_);
    crate::leanh::lean_ctor_set(v___x_5083_, 2, v___x_5079_);
    crate::leanh::lean_ctor_set(v___x_5083_, 3, v___x_5079_);
    crate::leanh::lean_ctor_set_usize(v___x_5083_, 4, v___x_5078_);
    return v___x_5083_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5084_ = crate::leanh::lean_box(1);
    v___x_5085_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
    v___x_5086_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
    v___x_5087_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5087_, 0, v___x_5086_);
    crate::leanh::lean_ctor_set(v___x_5087_, 1, v___x_5085_);
    crate::leanh::lean_ctor_set(v___x_5087_, 2, v___x_5084_);
    return v___x_5087_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5089_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6;
    v___x_5090_ = l_Lean_stringToMessageData(v___x_5089_);
    return v___x_5090_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5092_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8;
    v___x_5093_ = l_Lean_stringToMessageData(v___x_5092_);
    return v___x_5093_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5095_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10;
    v___x_5096_ = l_Lean_stringToMessageData(v___x_5095_);
    return v___x_5096_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5098_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12;
    v___x_5099_ = l_Lean_stringToMessageData(v___x_5098_);
    return v___x_5099_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5101_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14;
    v___x_5102_ = l_Lean_stringToMessageData(v___x_5101_);
    return v___x_5102_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5104_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16;
    v___x_5105_ = l_Lean_stringToMessageData(v___x_5104_);
    return v___x_5105_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5107_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18;
    v___x_5108_ = l_Lean_stringToMessageData(v___x_5107_);
    return v___x_5108_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(
    mut v_msg_5109_: *mut crate::leanh::LeanObject,
    mut v_declHint_5110_: *mut crate::leanh::LeanObject,
    mut v___y_5111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: u8 = 0;
    let mut v_isExporting_5116_: u8 = 0;
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: u8 = 0;
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5138_: u8 = 0;
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: u8 = 0;
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5170_: u8 = 0;
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5113_ = lean_st_ref_get(v___y_5111_);
                v_env_5114_ = crate::leanh::lean_ctor_get(v___x_5113_, 0);
                crate::leanh::lean_inc_ref(v_env_5114_);
                crate::leanh::lean_dec(v___x_5113_);
                v___x_5115_ = l_Lean_Name_isAnonymous(v_declHint_5110_);
                if v___x_5115_ == 0 {
                    v_isExporting_5116_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_5114_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5116_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_5114_);
                        crate::leanh::lean_dec(v_declHint_5110_);
                        v___x_5117_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5117_, 0, v_msg_5109_);
                        return v___x_5117_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_5114_);
                        v___x_5118_ = l_Lean_Environment_setExporting(v_env_5114_, v___x_5115_);
                        crate::leanh::lean_inc(v_declHint_5110_);
                        crate::leanh::lean_inc_ref(v___x_5118_);
                        v___x_5119_ = l_Lean_Environment_contains(
                            v___x_5118_,
                            v_declHint_5110_,
                            v_isExporting_5116_,
                        );
                        if v___x_5119_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5118_);
                            crate::leanh::lean_dec_ref(v_env_5114_);
                            crate::leanh::lean_dec(v_declHint_5110_);
                            v___x_5120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5120_, 0, v_msg_5109_);
                            return v___x_5120_;
                        } else {
                            v___x_5121_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
                            v___x_5122_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
                            v___x_5123_ = l_Lean_Options_empty;
                            v___x_5124_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5124_, 0, v___x_5118_);
                            crate::leanh::lean_ctor_set(v___x_5124_, 1, v___x_5121_);
                            crate::leanh::lean_ctor_set(v___x_5124_, 2, v___x_5122_);
                            crate::leanh::lean_ctor_set(v___x_5124_, 3, v___x_5123_);
                            crate::leanh::lean_inc(v_declHint_5110_);
                            v___x_5125_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5110_, v___x_5115_);
                            v_c_5126_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_5126_, 0, v___x_5124_);
                            crate::leanh::lean_ctor_set(v_c_5126_, 1, v___x_5125_);
                            v___x_5127_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5114_,
                                v_declHint_5110_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5127_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_5114_);
                                crate::leanh::lean_dec(v_declHint_5110_);
                                v___x_5128_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
                                v___x_5129_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5129_, 0, v___x_5128_);
                                crate::leanh::lean_ctor_set(v___x_5129_, 1, v_c_5126_);
                                v___x_5130_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
                                v___x_5131_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5131_, 0, v___x_5129_);
                                crate::leanh::lean_ctor_set(v___x_5131_, 1, v___x_5130_);
                                v___x_5132_ = l_Lean_MessageData_note(v___x_5131_);
                                v___x_5133_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5133_, 0, v_msg_5109_);
                                crate::leanh::lean_ctor_set(v___x_5133_, 1, v___x_5132_);
                                v___x_5134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5134_, 0, v___x_5133_);
                                return v___x_5134_;
                            } else {
                                v_val_5135_ = crate::leanh::lean_ctor_get(v___x_5127_, 0);
                                v_isSharedCheck_5170_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5127_)) as u8;
                                if v_isSharedCheck_5170_ == 0 {
                                    v___x_5137_ = v___x_5127_;
                                    v_isShared_5138_ = v_isSharedCheck_5170_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_5135_);
                                    crate::leanh::lean_dec(v___x_5127_);
                                    v___x_5137_ = crate::leanh::lean_box(0);
                                    v_isShared_5138_ = v_isSharedCheck_5170_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_5114_);
                    crate::leanh::lean_dec(v_declHint_5110_);
                    v___x_5171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5171_, 0, v_msg_5109_);
                    return v___x_5171_;
                }
            }
            1 => {
                v___x_5139_ = crate::leanh::lean_box(0);
                v___x_5140_ = l_Lean_Environment_header(v_env_5114_);
                crate::leanh::lean_dec_ref(v_env_5114_);
                v___x_5141_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5140_);
                v_mod_5142_ = lean_array_get(v___x_5139_, v___x_5141_, v_val_5135_);
                crate::leanh::lean_dec(v_val_5135_);
                crate::leanh::lean_dec_ref(v___x_5141_);
                v___x_5143_ = l_Lean_isPrivateName(v_declHint_5110_);
                crate::leanh::lean_dec(v_declHint_5110_);
                if v___x_5143_ == 0 {
                    v___x_5144_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
                    v___x_5145_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5145_, 0, v___x_5144_);
                    crate::leanh::lean_ctor_set(v___x_5145_, 1, v_c_5126_);
                    v___x_5146_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
                    v___x_5147_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5147_, 0, v___x_5145_);
                    crate::leanh::lean_ctor_set(v___x_5147_, 1, v___x_5146_);
                    v___x_5148_ = l_Lean_MessageData_ofName(v_mod_5142_);
                    v___x_5149_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5149_, 0, v___x_5147_);
                    crate::leanh::lean_ctor_set(v___x_5149_, 1, v___x_5148_);
                    v___x_5150_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
                    v___x_5151_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5151_, 0, v___x_5149_);
                    crate::leanh::lean_ctor_set(v___x_5151_, 1, v___x_5150_);
                    v___x_5152_ = l_Lean_MessageData_note(v___x_5151_);
                    v___x_5153_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5153_, 0, v_msg_5109_);
                    crate::leanh::lean_ctor_set(v___x_5153_, 1, v___x_5152_);
                    if v_isShared_5138_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5137_, 0);
                        crate::leanh::lean_ctor_set(v___x_5137_, 0, v___x_5153_);
                        v___x_5155_ = v___x_5137_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5156_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5153_);
                        v___x_5155_ = v_reuseFailAlloc_5156_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5157_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
                    v___x_5158_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5158_, 0, v___x_5157_);
                    crate::leanh::lean_ctor_set(v___x_5158_, 1, v_c_5126_);
                    v___x_5159_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
                    v___x_5160_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5160_, 0, v___x_5158_);
                    crate::leanh::lean_ctor_set(v___x_5160_, 1, v___x_5159_);
                    v___x_5161_ = l_Lean_MessageData_ofName(v_mod_5142_);
                    v___x_5162_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5162_, 0, v___x_5160_);
                    crate::leanh::lean_ctor_set(v___x_5162_, 1, v___x_5161_);
                    v___x_5163_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
                    v___x_5164_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5164_, 0, v___x_5162_);
                    crate::leanh::lean_ctor_set(v___x_5164_, 1, v___x_5163_);
                    v___x_5165_ = l_Lean_MessageData_note(v___x_5164_);
                    v___x_5166_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5166_, 0, v_msg_5109_);
                    crate::leanh::lean_ctor_set(v___x_5166_, 1, v___x_5165_);
                    if v_isShared_5138_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5137_, 0);
                        crate::leanh::lean_ctor_set(v___x_5137_, 0, v___x_5166_);
                        v___x_5168_ = v___x_5137_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5169_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5166_);
                        v___x_5168_ = v_reuseFailAlloc_5169_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5155_;
            }
            3 => {
                return v___x_5168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___boxed(
    mut v_msg_5172_: *mut crate::leanh::LeanObject,
    mut v_declHint_5173_: *mut crate::leanh::LeanObject,
    mut v___y_5174_: *mut crate::leanh::LeanObject,
    mut v___y_5175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5176_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_5172_, v_declHint_5173_, v___y_5174_);
    crate::leanh::lean_dec(v___y_5174_);
    return v_res_5176_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(
    mut v_msg_5177_: *mut crate::leanh::LeanObject,
    mut v_declHint_5178_: *mut crate::leanh::LeanObject,
    mut v___y_5179_: *mut crate::leanh::LeanObject,
    mut v___y_5180_: *mut crate::leanh::LeanObject,
    mut v___y_5181_: *mut crate::leanh::LeanObject,
    mut v___y_5182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5188_: u8 = 0;
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5184_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_5177_, v_declHint_5178_, v___y_5182_);
                v_a_5185_ = crate::leanh::lean_ctor_get(v___x_5184_, 0);
                v_isSharedCheck_5194_ = (!crate::leanh::lean_is_exclusive(v___x_5184_)) as u8;
                if v_isSharedCheck_5194_ == 0 {
                    v___x_5187_ = v___x_5184_;
                    v_isShared_5188_ = v_isSharedCheck_5194_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5185_);
                    crate::leanh::lean_dec(v___x_5184_);
                    v___x_5187_ = crate::leanh::lean_box(0);
                    v_isShared_5188_ = v_isSharedCheck_5194_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5189_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5190_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5190_, 0, v___x_5189_);
                crate::leanh::lean_ctor_set(v___x_5190_, 1, v_a_5185_);
                if v_isShared_5188_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5187_, 0, v___x_5190_);
                    v___x_5192_ = v___x_5187_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5193_, 0, v___x_5190_);
                    v___x_5192_ = v_reuseFailAlloc_5193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(
    mut v_msg_5195_: *mut crate::leanh::LeanObject,
    mut v_declHint_5196_: *mut crate::leanh::LeanObject,
    mut v___y_5197_: *mut crate::leanh::LeanObject,
    mut v___y_5198_: *mut crate::leanh::LeanObject,
    mut v___y_5199_: *mut crate::leanh::LeanObject,
    mut v___y_5200_: *mut crate::leanh::LeanObject,
    mut v___y_5201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5202_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_5195_, v_declHint_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
    crate::leanh::lean_dec(v___y_5200_);
    crate::leanh::lean_dec_ref(v___y_5199_);
    crate::leanh::lean_dec(v___y_5198_);
    crate::leanh::lean_dec_ref(v___y_5197_);
    return v_res_5202_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(
    mut v_ref_5203_: *mut crate::leanh::LeanObject,
    mut v_msg_5204_: *mut crate::leanh::LeanObject,
    mut v___y_5205_: *mut crate::leanh::LeanObject,
    mut v___y_5206_: *mut crate::leanh::LeanObject,
    mut v___y_5207_: *mut crate::leanh::LeanObject,
    mut v___y_5208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5222_: u8 = 0;
    let mut v_cancelTk_x3f_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5224_: u8 = 0;
    let mut v_inheritedTraceOptions_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5210_ = crate::leanh::lean_ctor_get(v___y_5207_, 0);
    v_fileMap_5211_ = crate::leanh::lean_ctor_get(v___y_5207_, 1);
    v_options_5212_ = crate::leanh::lean_ctor_get(v___y_5207_, 2);
    v_currRecDepth_5213_ = crate::leanh::lean_ctor_get(v___y_5207_, 3);
    v_maxRecDepth_5214_ = crate::leanh::lean_ctor_get(v___y_5207_, 4);
    v_ref_5215_ = crate::leanh::lean_ctor_get(v___y_5207_, 5);
    v_currNamespace_5216_ = crate::leanh::lean_ctor_get(v___y_5207_, 6);
    v_openDecls_5217_ = crate::leanh::lean_ctor_get(v___y_5207_, 7);
    v_initHeartbeats_5218_ = crate::leanh::lean_ctor_get(v___y_5207_, 8);
    v_maxHeartbeats_5219_ = crate::leanh::lean_ctor_get(v___y_5207_, 9);
    v_quotContext_5220_ = crate::leanh::lean_ctor_get(v___y_5207_, 10);
    v_currMacroScope_5221_ = crate::leanh::lean_ctor_get(v___y_5207_, 11);
    v_diag_5222_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5207_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5223_ = crate::leanh::lean_ctor_get(v___y_5207_, 12);
    v_suppressElabErrors_5224_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5207_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5225_ = crate::leanh::lean_ctor_get(v___y_5207_, 13);
    v_ref_5226_ = l_Lean_replaceRef(v_ref_5203_, v_ref_5215_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5225_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5223_);
    crate::leanh::lean_inc(v_currMacroScope_5221_);
    crate::leanh::lean_inc(v_quotContext_5220_);
    crate::leanh::lean_inc(v_maxHeartbeats_5219_);
    crate::leanh::lean_inc(v_initHeartbeats_5218_);
    crate::leanh::lean_inc(v_openDecls_5217_);
    crate::leanh::lean_inc(v_currNamespace_5216_);
    crate::leanh::lean_inc(v_maxRecDepth_5214_);
    crate::leanh::lean_inc(v_currRecDepth_5213_);
    crate::leanh::lean_inc_ref(v_options_5212_);
    crate::leanh::lean_inc_ref(v_fileMap_5211_);
    crate::leanh::lean_inc_ref(v_fileName_5210_);
    v___x_5227_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5227_, 0, v_fileName_5210_);
    crate::leanh::lean_ctor_set(v___x_5227_, 1, v_fileMap_5211_);
    crate::leanh::lean_ctor_set(v___x_5227_, 2, v_options_5212_);
    crate::leanh::lean_ctor_set(v___x_5227_, 3, v_currRecDepth_5213_);
    crate::leanh::lean_ctor_set(v___x_5227_, 4, v_maxRecDepth_5214_);
    crate::leanh::lean_ctor_set(v___x_5227_, 5, v_ref_5226_);
    crate::leanh::lean_ctor_set(v___x_5227_, 6, v_currNamespace_5216_);
    crate::leanh::lean_ctor_set(v___x_5227_, 7, v_openDecls_5217_);
    crate::leanh::lean_ctor_set(v___x_5227_, 8, v_initHeartbeats_5218_);
    crate::leanh::lean_ctor_set(v___x_5227_, 9, v_maxHeartbeats_5219_);
    crate::leanh::lean_ctor_set(v___x_5227_, 10, v_quotContext_5220_);
    crate::leanh::lean_ctor_set(v___x_5227_, 11, v_currMacroScope_5221_);
    crate::leanh::lean_ctor_set(v___x_5227_, 12, v_cancelTk_x3f_5223_);
    crate::leanh::lean_ctor_set(v___x_5227_, 13, v_inheritedTraceOptions_5225_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5227_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5222_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5227_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5224_,
    );
    v___x_5228_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_5204_, v___y_5205_, v___y_5206_, v___x_5227_, v___y_5208_);
    crate::leanh::lean_dec_ref_known(v___x_5227_, 14);
    return v___x_5228_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg___boxed(
    mut v_ref_5229_: *mut crate::leanh::LeanObject,
    mut v_msg_5230_: *mut crate::leanh::LeanObject,
    mut v___y_5231_: *mut crate::leanh::LeanObject,
    mut v___y_5232_: *mut crate::leanh::LeanObject,
    mut v___y_5233_: *mut crate::leanh::LeanObject,
    mut v___y_5234_: *mut crate::leanh::LeanObject,
    mut v___y_5235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5236_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_5229_, v_msg_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_);
    crate::leanh::lean_dec(v___y_5234_);
    crate::leanh::lean_dec_ref(v___y_5233_);
    crate::leanh::lean_dec(v___y_5232_);
    crate::leanh::lean_dec_ref(v___y_5231_);
    crate::leanh::lean_dec(v_ref_5229_);
    return v_res_5236_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(
    mut v_ref_5237_: *mut crate::leanh::LeanObject,
    mut v_msg_5238_: *mut crate::leanh::LeanObject,
    mut v_declHint_5239_: *mut crate::leanh::LeanObject,
    mut v___y_5240_: *mut crate::leanh::LeanObject,
    mut v___y_5241_: *mut crate::leanh::LeanObject,
    mut v___y_5242_: *mut crate::leanh::LeanObject,
    mut v___y_5243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5245_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_5238_, v_declHint_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
    v_a_5246_ = crate::leanh::lean_ctor_get(v___x_5245_, 0);
    crate::leanh::lean_inc(v_a_5246_);
    crate::leanh::lean_dec_ref(v___x_5245_);
    v___x_5247_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_5237_, v_a_5246_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
    return v___x_5247_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg___boxed(
    mut v_ref_5248_: *mut crate::leanh::LeanObject,
    mut v_msg_5249_: *mut crate::leanh::LeanObject,
    mut v_declHint_5250_: *mut crate::leanh::LeanObject,
    mut v___y_5251_: *mut crate::leanh::LeanObject,
    mut v___y_5252_: *mut crate::leanh::LeanObject,
    mut v___y_5253_: *mut crate::leanh::LeanObject,
    mut v___y_5254_: *mut crate::leanh::LeanObject,
    mut v___y_5255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5256_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_5248_, v_msg_5249_, v_declHint_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
    crate::leanh::lean_dec(v___y_5254_);
    crate::leanh::lean_dec_ref(v___y_5253_);
    crate::leanh::lean_dec(v___y_5252_);
    crate::leanh::lean_dec_ref(v___y_5251_);
    crate::leanh::lean_dec(v_ref_5248_);
    return v_res_5256_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5258_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0;
    v___x_5259_ = l_Lean_stringToMessageData(v___x_5258_);
    return v___x_5259_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5261_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2;
    v___x_5262_ = l_Lean_stringToMessageData(v___x_5261_);
    return v___x_5262_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(
    mut v_ref_5263_: *mut crate::leanh::LeanObject,
    mut v_constName_5264_: *mut crate::leanh::LeanObject,
    mut v___y_5265_: *mut crate::leanh::LeanObject,
    mut v___y_5266_: *mut crate::leanh::LeanObject,
    mut v___y_5267_: *mut crate::leanh::LeanObject,
    mut v___y_5268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: u8 = 0;
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5270_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1);
    v___x_5271_ = 0;
    crate::leanh::lean_inc(v_constName_5264_);
    v___x_5272_ = l_Lean_MessageData_ofConstName(v_constName_5264_, v___x_5271_);
    v___x_5273_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5273_, 0, v___x_5270_);
    crate::leanh::lean_ctor_set(v___x_5273_, 1, v___x_5272_);
    v___x_5274_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3);
    v___x_5275_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5275_, 0, v___x_5273_);
    crate::leanh::lean_ctor_set(v___x_5275_, 1, v___x_5274_);
    v___x_5276_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_5263_, v___x_5275_, v_constName_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
    return v___x_5276_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___boxed(
    mut v_ref_5277_: *mut crate::leanh::LeanObject,
    mut v_constName_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
    mut v___y_5280_: *mut crate::leanh::LeanObject,
    mut v___y_5281_: *mut crate::leanh::LeanObject,
    mut v___y_5282_: *mut crate::leanh::LeanObject,
    mut v___y_5283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5284_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_5277_, v_constName_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_);
    crate::leanh::lean_dec(v___y_5282_);
    crate::leanh::lean_dec_ref(v___y_5281_);
    crate::leanh::lean_dec(v___y_5280_);
    crate::leanh::lean_dec_ref(v___y_5279_);
    crate::leanh::lean_dec(v_ref_5277_);
    return v_res_5284_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(
    mut v_constName_5285_: *mut crate::leanh::LeanObject,
    mut v___y_5286_: *mut crate::leanh::LeanObject,
    mut v___y_5287_: *mut crate::leanh::LeanObject,
    mut v___y_5288_: *mut crate::leanh::LeanObject,
    mut v___y_5289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_5291_ = crate::leanh::lean_ctor_get(v___y_5288_, 5);
    v___x_5292_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_5291_, v_constName_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_);
    return v___x_5292_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_constName_5293_: *mut crate::leanh::LeanObject,
    mut v___y_5294_: *mut crate::leanh::LeanObject,
    mut v___y_5295_: *mut crate::leanh::LeanObject,
    mut v___y_5296_: *mut crate::leanh::LeanObject,
    mut v___y_5297_: *mut crate::leanh::LeanObject,
    mut v___y_5298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5299_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_);
    crate::leanh::lean_dec(v___y_5297_);
    crate::leanh::lean_dec_ref(v___y_5296_);
    crate::leanh::lean_dec(v___y_5295_);
    crate::leanh::lean_dec_ref(v___y_5294_);
    return v_res_5299_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(
    mut v_constName_5300_: *mut crate::leanh::LeanObject,
    mut v___y_5301_: *mut crate::leanh::LeanObject,
    mut v___y_5302_: *mut crate::leanh::LeanObject,
    mut v___y_5303_: *mut crate::leanh::LeanObject,
    mut v___y_5304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: u8 = 0;
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5314_: u8 = 0;
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5306_ = lean_st_ref_get(v___y_5304_);
                v_env_5307_ = crate::leanh::lean_ctor_get(v___x_5306_, 0);
                crate::leanh::lean_inc_ref(v_env_5307_);
                crate::leanh::lean_dec(v___x_5306_);
                v___x_5308_ = 0;
                crate::leanh::lean_inc(v_constName_5300_);
                v___x_5309_ =
                    l_Lean_Environment_find_x3f(v_env_5307_, v_constName_5300_, v___x_5308_);
                if crate::leanh::lean_obj_tag(v___x_5309_) == 0 {
                    v___x_5310_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
                    return v___x_5310_;
                } else {
                    crate::leanh::lean_dec(v_constName_5300_);
                    v_val_5311_ = crate::leanh::lean_ctor_get(v___x_5309_, 0);
                    v_isSharedCheck_5318_ = (!crate::leanh::lean_is_exclusive(v___x_5309_)) as u8;
                    if v_isSharedCheck_5318_ == 0 {
                        v___x_5313_ = v___x_5309_;
                        v_isShared_5314_ = v_isSharedCheck_5318_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5311_);
                        crate::leanh::lean_dec(v___x_5309_);
                        v___x_5313_ = crate::leanh::lean_box(0);
                        v_isShared_5314_ = v_isSharedCheck_5318_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5314_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5313_, 0);
                    v___x_5316_ = v___x_5313_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5317_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_val_5311_);
                    v___x_5316_ = v_reuseFailAlloc_5317_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0___boxed(
    mut v_constName_5319_: *mut crate::leanh::LeanObject,
    mut v___y_5320_: *mut crate::leanh::LeanObject,
    mut v___y_5321_: *mut crate::leanh::LeanObject,
    mut v___y_5322_: *mut crate::leanh::LeanObject,
    mut v___y_5323_: *mut crate::leanh::LeanObject,
    mut v___y_5324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5325_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_constName_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
    crate::leanh::lean_dec(v___y_5323_);
    crate::leanh::lean_dec_ref(v___y_5322_);
    crate::leanh::lean_dec(v___y_5321_);
    crate::leanh::lean_dec_ref(v___y_5320_);
    return v_res_5325_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(
    mut v_declName_5326_: *mut crate::leanh::LeanObject,
    mut v___y_5327_: *mut crate::leanh::LeanObject,
    mut v___y_5328_: *mut crate::leanh::LeanObject,
    mut v___y_5329_: *mut crate::leanh::LeanObject,
    mut v___y_5330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5335_: u8 = 0;
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5346_: u8 = 0;
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5358_: u8 = 0;
    let mut v_isSharedCheck_5359_: u8 = 0;
    let mut v_unused_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5364_: u8 = 0;
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5368_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_5326_);
                v___x_5332_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_declName_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_);
                if crate::leanh::lean_obj_tag(v___x_5332_) == 0 {
                    v_isSharedCheck_5359_ = (!crate::leanh::lean_is_exclusive(v___x_5332_)) as u8;
                    if v_isSharedCheck_5359_ == 0 {
                        v_unused_5360_ = crate::leanh::lean_ctor_get(v___x_5332_, 0);
                        crate::leanh::lean_dec(v_unused_5360_);
                        v___x_5334_ = v___x_5332_;
                        v_isShared_5335_ = v_isSharedCheck_5359_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5332_);
                        v___x_5334_ = crate::leanh::lean_box(0);
                        v_isShared_5335_ = v_isSharedCheck_5359_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_5326_);
                    v_a_5361_ = crate::leanh::lean_ctor_get(v___x_5332_, 0);
                    v_isSharedCheck_5368_ = (!crate::leanh::lean_is_exclusive(v___x_5332_)) as u8;
                    if v_isSharedCheck_5368_ == 0 {
                        v___x_5363_ = v___x_5332_;
                        v_isShared_5364_ = v_isSharedCheck_5368_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5361_);
                        crate::leanh::lean_dec(v___x_5332_);
                        v___x_5363_ = crate::leanh::lean_box(0);
                        v_isShared_5364_ = v_isSharedCheck_5368_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5336_ = lean_st_ref_get(v___y_5330_);
                v_env_5337_ = crate::leanh::lean_ctor_get(v___x_5336_, 0);
                crate::leanh::lean_inc_ref(v_env_5337_);
                crate::leanh::lean_dec(v___x_5336_);
                v___x_5338_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5337_, v_declName_5326_);
                crate::leanh::lean_dec(v_declName_5326_);
                crate::leanh::lean_dec_ref(v_env_5337_);
                if crate::leanh::lean_obj_tag(v___x_5338_) == 0 {
                    v___x_5339_ = crate::leanh::lean_box(0);
                    if v_isShared_5335_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5334_, 0, v___x_5339_);
                        v___x_5341_ = v___x_5334_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5342_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5342_, 0, v___x_5339_);
                        v___x_5341_ = v_reuseFailAlloc_5342_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_5343_ = crate::leanh::lean_ctor_get(v___x_5338_, 0);
                    v_isSharedCheck_5358_ = (!crate::leanh::lean_is_exclusive(v___x_5338_)) as u8;
                    if v_isSharedCheck_5358_ == 0 {
                        v___x_5345_ = v___x_5338_;
                        v_isShared_5346_ = v_isSharedCheck_5358_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5343_);
                        crate::leanh::lean_dec(v___x_5338_);
                        v___x_5345_ = crate::leanh::lean_box(0);
                        v_isShared_5346_ = v_isSharedCheck_5358_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5341_;
            }
            3 => {
                v___x_5347_ = lean_st_ref_get(v___y_5330_);
                v_env_5348_ = crate::leanh::lean_ctor_get(v___x_5347_, 0);
                crate::leanh::lean_inc_ref(v_env_5348_);
                crate::leanh::lean_dec(v___x_5347_);
                v___x_5349_ = crate::leanh::lean_box(0);
                v___x_5350_ = l_Lean_Environment_allImportedModuleNames(v_env_5348_);
                crate::leanh::lean_dec_ref(v_env_5348_);
                v___x_5351_ = lean_array_get(v___x_5349_, v___x_5350_, v_val_5343_);
                crate::leanh::lean_dec(v_val_5343_);
                crate::leanh::lean_dec_ref(v___x_5350_);
                if v_isShared_5346_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5345_, 0, v___x_5351_);
                    v___x_5353_ = v___x_5345_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5357_, 0, v___x_5351_);
                    v___x_5353_ = v_reuseFailAlloc_5357_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5335_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5334_, 0, v___x_5353_);
                    v___x_5355_ = v___x_5334_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5356_, 0, v___x_5353_);
                    v___x_5355_ = v_reuseFailAlloc_5356_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5355_;
            }
            6 => {
                if v_isShared_5364_ == 0 {
                    v___x_5366_ = v___x_5363_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
                    v___x_5366_ = v_reuseFailAlloc_5367_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5366_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0___boxed(
    mut v_declName_5369_: *mut crate::leanh::LeanObject,
    mut v___y_5370_: *mut crate::leanh::LeanObject,
    mut v___y_5371_: *mut crate::leanh::LeanObject,
    mut v___y_5372_: *mut crate::leanh::LeanObject,
    mut v___y_5373_: *mut crate::leanh::LeanObject,
    mut v___y_5374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5375_ =
        l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(
            v_declName_5369_,
            v___y_5370_,
            v___y_5371_,
            v___y_5372_,
            v___y_5373_,
        );
    crate::leanh::lean_dec(v___y_5373_);
    crate::leanh::lean_dec_ref(v___y_5372_);
    crate::leanh::lean_dec(v___y_5371_);
    crate::leanh::lean_dec_ref(v___y_5370_);
    return v_res_5375_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(
    mut v_init_5376_: *mut crate::leanh::LeanObject,
    mut v_x_5377_: *mut crate::leanh::LeanObject,
    mut v___y_5378_: *mut crate::leanh::LeanObject,
    mut v___y_5379_: *mut crate::leanh::LeanObject,
    mut v___y_5380_: *mut crate::leanh::LeanObject,
    mut v___y_5381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5395_: u8 = 0;
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5399_: u8 = 0;
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5377_) == 0 {
                    v_k_5383_ = crate::leanh::lean_ctor_get(v_x_5377_, 1);
                    crate::leanh::lean_inc(v_k_5383_);
                    v_l_5384_ = crate::leanh::lean_ctor_get(v_x_5377_, 3);
                    crate::leanh::lean_inc(v_l_5384_);
                    v_r_5385_ = crate::leanh::lean_ctor_get(v_x_5377_, 4);
                    crate::leanh::lean_inc(v_r_5385_);
                    crate::leanh::lean_dec_ref_known(v_x_5377_, 5);
                    v___x_5386_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_5376_, v_l_5384_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_);
                    if crate::leanh::lean_obj_tag(v___x_5386_) == 0 {
                        v_a_5387_ = crate::leanh::lean_ctor_get(v___x_5386_, 0);
                        crate::leanh::lean_inc(v_a_5387_);
                        crate::leanh::lean_dec_ref_known(v___x_5386_, 1);
                        v___x_5388_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_k_5383_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_);
                        if crate::leanh::lean_obj_tag(v___x_5388_) == 0 {
                            v_a_5389_ = crate::leanh::lean_ctor_get(v___x_5388_, 0);
                            crate::leanh::lean_inc(v_a_5389_);
                            crate::leanh::lean_dec_ref_known(v___x_5388_, 1);
                            v___x_5390_ = lean_array_push(v_a_5387_, v_a_5389_);
                            v_init_5376_ = v___x_5390_;
                            v_x_5377_ = v_r_5385_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_5387_);
                            crate::leanh::lean_dec(v_r_5385_);
                            v_a_5392_ = crate::leanh::lean_ctor_get(v___x_5388_, 0);
                            v_isSharedCheck_5399_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5388_)) as u8;
                            if v_isSharedCheck_5399_ == 0 {
                                v___x_5394_ = v___x_5388_;
                                v_isShared_5395_ = v_isSharedCheck_5399_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5392_);
                                crate::leanh::lean_dec(v___x_5388_);
                                v___x_5394_ = crate::leanh::lean_box(0);
                                v_isShared_5395_ = v_isSharedCheck_5399_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_r_5385_);
                        crate::leanh::lean_dec(v_k_5383_);
                        return v___x_5386_;
                    }
                } else {
                    v___x_5400_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5400_, 0, v_init_5376_);
                    return v___x_5400_;
                }
            }
            1 => {
                if v_isShared_5395_ == 0 {
                    v___x_5397_ = v___x_5394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5398_, 0, v_a_5392_);
                    v___x_5397_ = v_reuseFailAlloc_5398_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5397_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3___boxed(
    mut v_init_5401_: *mut crate::leanh::LeanObject,
    mut v_x_5402_: *mut crate::leanh::LeanObject,
    mut v___y_5403_: *mut crate::leanh::LeanObject,
    mut v___y_5404_: *mut crate::leanh::LeanObject,
    mut v___y_5405_: *mut crate::leanh::LeanObject,
    mut v___y_5406_: *mut crate::leanh::LeanObject,
    mut v___y_5407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5408_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_5401_, v_x_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_);
    crate::leanh::lean_dec(v___y_5406_);
    crate::leanh::lean_dec_ref(v___y_5405_);
    crate::leanh::lean_dec(v___y_5404_);
    crate::leanh::lean_dec_ref(v___y_5403_);
    return v_res_5408_;
}
pub unsafe fn _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5409_ = l_Lean_NameSet_empty;
    v___x_5410_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once), _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
    v___x_5411_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5411_, 0, v___x_5410_);
    crate::leanh::lean_ctor_set(v___x_5411_, 1, v___x_5409_);
    return v___x_5411_;
}
pub unsafe fn l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(
    mut v_pre_5413_: *mut crate::leanh::LeanObject,
    mut v_type_5414_: *mut crate::leanh::LeanObject,
    mut v_a_5415_: *mut crate::leanh::LeanObject,
    mut v_a_5416_: *mut crate::leanh::LeanObject,
    mut v_a_5417_: *mut crate::leanh::LeanObject,
    mut v_a_5418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5430_: u8 = 0;
    let mut v_consts_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: u8 = 0;
    let mut v___x_5451_: usize = 0;
    let mut v___x_5452_: usize = 0;
    let mut v___x_5453_: u8 = 0;
    let mut v___y_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: u8 = 0;
    let mut v___x_5461_: usize = 0;
    let mut v___x_5462_: usize = 0;
    let mut v___x_5463_: u8 = 0;
    let mut v_a_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5467_: u8 = 0;
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5471_: u8 = 0;
    let mut v_size_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5473_: u8 = 0;
    let mut v_a_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5477_: u8 = 0;
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5420_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5421_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0_once
                    ),
                    _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0,
                );
                v___x_5422_ = lean_st_mk_ref(v___x_5421_);
                crate::leanh::lean_inc_ref(v_type_5414_);
                v___x_5423_ =
                    l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(
                        v_type_5414_,
                        v___x_5422_,
                        v_a_5415_,
                        v_a_5416_,
                        v_a_5417_,
                        v_a_5418_,
                    );
                if crate::leanh::lean_obj_tag(v___x_5423_) == 0 {
                    v_a_5424_ = crate::leanh::lean_ctor_get(v___x_5423_, 0);
                    crate::leanh::lean_inc(v_a_5424_);
                    crate::leanh::lean_dec_ref_known(v___x_5423_, 1);
                    v___x_5425_ = lean_st_ref_get(v___x_5422_);
                    crate::leanh::lean_dec(v___x_5422_);
                    v___x_5426_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v_a_5418_);
                    v_a_5427_ = crate::leanh::lean_ctor_get(v___x_5426_, 0);
                    v_isSharedCheck_5473_ = (!crate::leanh::lean_is_exclusive(v___x_5426_)) as u8;
                    if v_isSharedCheck_5473_ == 0 {
                        v___x_5429_ = v___x_5426_;
                        v_isShared_5430_ = v_isSharedCheck_5473_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5427_);
                        crate::leanh::lean_dec(v___x_5426_);
                        v___x_5429_ = crate::leanh::lean_box(0);
                        v_isShared_5430_ = v_isSharedCheck_5473_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5422_);
                    crate::leanh::lean_dec_ref(v_type_5414_);
                    crate::leanh::lean_dec_ref(v_pre_5413_);
                    v_a_5474_ = crate::leanh::lean_ctor_get(v___x_5423_, 0);
                    v_isSharedCheck_5481_ = (!crate::leanh::lean_is_exclusive(v___x_5423_)) as u8;
                    if v_isSharedCheck_5481_ == 0 {
                        v___x_5476_ = v___x_5423_;
                        v_isShared_5477_ = v_isSharedCheck_5481_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5474_);
                        crate::leanh::lean_dec(v___x_5423_);
                        v___x_5476_ = crate::leanh::lean_box(0);
                        v_isShared_5477_ = v_isSharedCheck_5481_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_consts_5431_ = crate::leanh::lean_ctor_get(v___x_5425_, 1);
                crate::leanh::lean_inc(v_consts_5431_);
                crate::leanh::lean_dec(v___x_5425_);
                v___f_5432_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1;
                v___x_5442_ = lean_string_append(v_pre_5413_, v_a_5424_);
                crate::leanh::lean_dec(v_a_5424_);
                v___x_5443_ = l_Lean_Name_getRoot(v_a_5427_);
                crate::leanh::lean_dec(v_a_5427_);
                if crate::leanh::lean_obj_tag(v_consts_5431_) == 0 {
                    v_size_5472_ = crate::leanh::lean_ctor_get(v_consts_5431_, 0);
                    crate::leanh::lean_inc(v_size_5472_);
                    v___y_5455_ = v_size_5472_;
                    state = 6;
                    continue;
                } else {
                    v___y_5455_ = v___x_5420_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v___x_5435_ = crate::leanh::lean_box(0);
                v___x_5436_ = l_Lean_Name_str___override(v___x_5435_, v___y_5434_);
                v___x_5437_ = lean_find_expr(v___f_5432_, v_type_5414_);
                crate::leanh::lean_dec_ref(v_type_5414_);
                if crate::leanh::lean_obj_tag(v___x_5437_) == 0 {
                    if v_isShared_5430_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5429_, 0, v___x_5436_);
                        v___x_5439_ = v___x_5429_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5440_, 0, v___x_5436_);
                        v___x_5439_ = v_reuseFailAlloc_5440_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_5437_, 1);
                    crate::leanh::lean_del_object(v___x_5429_);
                    v___x_5441_ = l_Lean_Core_mkFreshUserName(v___x_5436_, v_a_5417_, v_a_5418_);
                    return v___x_5441_;
                }
            }
            3 => {
                return v___x_5439_;
            }
            4 => {
                v___x_5445_ =
                    l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(
                        v___x_5443_,
                    );
                v___x_5446_ = lean_string_append(v___x_5442_, v___x_5445_);
                crate::leanh::lean_dec_ref(v___x_5445_);
                v___y_5434_ = v___x_5446_;
                state = 2;
                continue;
            }
            5 => {
                v___x_5450_ = lean_nat_dec_lt(v___x_5420_, v___y_5448_);
                if v___x_5450_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_5449_);
                    crate::leanh::lean_dec(v___y_5448_);
                    state = 4;
                    continue;
                } else {
                    if v___x_5450_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_5449_);
                        crate::leanh::lean_dec(v___y_5448_);
                        state = 4;
                        continue;
                    } else {
                        v___x_5451_ = 0usize;
                        v___x_5452_ = lean_usize_of_nat(v___y_5448_);
                        crate::leanh::lean_dec(v___y_5448_);
                        crate::leanh::lean_inc(v___x_5443_);
                        v___x_5453_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_5443_, v___y_5449_, v___x_5451_, v___x_5452_);
                        crate::leanh::lean_dec_ref(v___y_5449_);
                        if v___x_5453_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5443_);
                            v___y_5434_ = v___x_5442_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___x_5456_ = lean_mk_empty_array_with_capacity(v___y_5455_);
                crate::leanh::lean_dec(v___y_5455_);
                v___x_5457_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v___x_5456_, v_consts_5431_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_);
                if crate::leanh::lean_obj_tag(v___x_5457_) == 0 {
                    v_a_5458_ = crate::leanh::lean_ctor_get(v___x_5457_, 0);
                    crate::leanh::lean_inc(v_a_5458_);
                    crate::leanh::lean_dec_ref_known(v___x_5457_, 1);
                    v___x_5459_ = lean_array_get_size(v_a_5458_);
                    v___x_5460_ = lean_nat_dec_lt(v___x_5420_, v___x_5459_);
                    if v___x_5460_ == 0 {
                        v___y_5448_ = v___x_5459_;
                        v___y_5449_ = v_a_5458_;
                        state = 5;
                        continue;
                    } else {
                        if v___x_5460_ == 0 {
                            v___y_5448_ = v___x_5459_;
                            v___y_5449_ = v_a_5458_;
                            state = 5;
                            continue;
                        } else {
                            v___x_5461_ = 0usize;
                            v___x_5462_ = lean_usize_of_nat(v___x_5459_);
                            v___x_5463_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_a_5458_, v___x_5461_, v___x_5462_);
                            if v___x_5463_ == 0 {
                                v___y_5448_ = v___x_5459_;
                                v___y_5449_ = v_a_5458_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_5458_);
                                crate::leanh::lean_dec(v___x_5443_);
                                v___y_5434_ = v___x_5442_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5443_);
                    crate::leanh::lean_dec_ref(v___x_5442_);
                    crate::leanh::lean_del_object(v___x_5429_);
                    crate::leanh::lean_dec_ref(v_type_5414_);
                    v_a_5464_ = crate::leanh::lean_ctor_get(v___x_5457_, 0);
                    v_isSharedCheck_5471_ = (!crate::leanh::lean_is_exclusive(v___x_5457_)) as u8;
                    if v_isSharedCheck_5471_ == 0 {
                        v___x_5466_ = v___x_5457_;
                        v_isShared_5467_ = v_isSharedCheck_5471_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5464_);
                        crate::leanh::lean_dec(v___x_5457_);
                        v___x_5466_ = crate::leanh::lean_box(0);
                        v_isShared_5467_ = v_isSharedCheck_5471_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_5467_ == 0 {
                    v___x_5469_ = v___x_5466_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5470_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5464_);
                    v___x_5469_ = v_reuseFailAlloc_5470_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5469_;
            }
            9 => {
                if v_isShared_5477_ == 0 {
                    v___x_5479_ = v___x_5476_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5480_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5474_);
                    v___x_5479_ = v_reuseFailAlloc_5480_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___boxed(
    mut v_pre_5482_: *mut crate::leanh::LeanObject,
    mut v_type_5483_: *mut crate::leanh::LeanObject,
    mut v_a_5484_: *mut crate::leanh::LeanObject,
    mut v_a_5485_: *mut crate::leanh::LeanObject,
    mut v_a_5486_: *mut crate::leanh::LeanObject,
    mut v_a_5487_: *mut crate::leanh::LeanObject,
    mut v_a_5488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5489_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(
        v_pre_5482_,
        v_type_5483_,
        v_a_5484_,
        v_a_5485_,
        v_a_5486_,
        v_a_5487_,
    );
    crate::leanh::lean_dec(v_a_5487_);
    crate::leanh::lean_dec_ref(v_a_5486_);
    crate::leanh::lean_dec(v_a_5485_);
    crate::leanh::lean_dec_ref(v_a_5484_);
    return v_res_5489_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(
    mut v_00_u03b1_5490_: *mut crate::leanh::LeanObject,
    mut v_constName_5491_: *mut crate::leanh::LeanObject,
    mut v___y_5492_: *mut crate::leanh::LeanObject,
    mut v___y_5493_: *mut crate::leanh::LeanObject,
    mut v___y_5494_: *mut crate::leanh::LeanObject,
    mut v___y_5495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5497_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_);
    return v___x_5497_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b1_5498_: *mut crate::leanh::LeanObject,
    mut v_constName_5499_: *mut crate::leanh::LeanObject,
    mut v___y_5500_: *mut crate::leanh::LeanObject,
    mut v___y_5501_: *mut crate::leanh::LeanObject,
    mut v___y_5502_: *mut crate::leanh::LeanObject,
    mut v___y_5503_: *mut crate::leanh::LeanObject,
    mut v___y_5504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5505_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(v_00_u03b1_5498_, v_constName_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_);
    crate::leanh::lean_dec(v___y_5503_);
    crate::leanh::lean_dec_ref(v___y_5502_);
    crate::leanh::lean_dec(v___y_5501_);
    crate::leanh::lean_dec_ref(v___y_5500_);
    return v_res_5505_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(
    mut v_00_u03b1_5506_: *mut crate::leanh::LeanObject,
    mut v_ref_5507_: *mut crate::leanh::LeanObject,
    mut v_constName_5508_: *mut crate::leanh::LeanObject,
    mut v___y_5509_: *mut crate::leanh::LeanObject,
    mut v___y_5510_: *mut crate::leanh::LeanObject,
    mut v___y_5511_: *mut crate::leanh::LeanObject,
    mut v___y_5512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5514_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_5507_, v_constName_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_);
    return v___x_5514_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___boxed(
    mut v_00_u03b1_5515_: *mut crate::leanh::LeanObject,
    mut v_ref_5516_: *mut crate::leanh::LeanObject,
    mut v_constName_5517_: *mut crate::leanh::LeanObject,
    mut v___y_5518_: *mut crate::leanh::LeanObject,
    mut v___y_5519_: *mut crate::leanh::LeanObject,
    mut v___y_5520_: *mut crate::leanh::LeanObject,
    mut v___y_5521_: *mut crate::leanh::LeanObject,
    mut v___y_5522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5523_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_5515_, v_ref_5516_, v_constName_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
    crate::leanh::lean_dec(v___y_5521_);
    crate::leanh::lean_dec_ref(v___y_5520_);
    crate::leanh::lean_dec(v___y_5519_);
    crate::leanh::lean_dec_ref(v___y_5518_);
    crate::leanh::lean_dec(v_ref_5516_);
    return v_res_5523_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(
    mut v_00_u03b1_5524_: *mut crate::leanh::LeanObject,
    mut v_ref_5525_: *mut crate::leanh::LeanObject,
    mut v_msg_5526_: *mut crate::leanh::LeanObject,
    mut v_declHint_5527_: *mut crate::leanh::LeanObject,
    mut v___y_5528_: *mut crate::leanh::LeanObject,
    mut v___y_5529_: *mut crate::leanh::LeanObject,
    mut v___y_5530_: *mut crate::leanh::LeanObject,
    mut v___y_5531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5533_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_5525_, v_msg_5526_, v_declHint_5527_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_);
    return v___x_5533_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(
    mut v_00_u03b1_5534_: *mut crate::leanh::LeanObject,
    mut v_ref_5535_: *mut crate::leanh::LeanObject,
    mut v_msg_5536_: *mut crate::leanh::LeanObject,
    mut v_declHint_5537_: *mut crate::leanh::LeanObject,
    mut v___y_5538_: *mut crate::leanh::LeanObject,
    mut v___y_5539_: *mut crate::leanh::LeanObject,
    mut v___y_5540_: *mut crate::leanh::LeanObject,
    mut v___y_5541_: *mut crate::leanh::LeanObject,
    mut v___y_5542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5543_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(v_00_u03b1_5534_, v_ref_5535_, v_msg_5536_, v_declHint_5537_, v___y_5538_, v___y_5539_, v___y_5540_, v___y_5541_);
    crate::leanh::lean_dec(v___y_5541_);
    crate::leanh::lean_dec_ref(v___y_5540_);
    crate::leanh::lean_dec(v___y_5539_);
    crate::leanh::lean_dec_ref(v___y_5538_);
    crate::leanh::lean_dec(v_ref_5535_);
    return v_res_5543_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(
    mut v_msg_5544_: *mut crate::leanh::LeanObject,
    mut v_declHint_5545_: *mut crate::leanh::LeanObject,
    mut v___y_5546_: *mut crate::leanh::LeanObject,
    mut v___y_5547_: *mut crate::leanh::LeanObject,
    mut v___y_5548_: *mut crate::leanh::LeanObject,
    mut v___y_5549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5551_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_5544_, v_declHint_5545_, v___y_5549_);
    return v___x_5551_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___boxed(
    mut v_msg_5552_: *mut crate::leanh::LeanObject,
    mut v_declHint_5553_: *mut crate::leanh::LeanObject,
    mut v___y_5554_: *mut crate::leanh::LeanObject,
    mut v___y_5555_: *mut crate::leanh::LeanObject,
    mut v___y_5556_: *mut crate::leanh::LeanObject,
    mut v___y_5557_: *mut crate::leanh::LeanObject,
    mut v___y_5558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5559_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(v_msg_5552_, v_declHint_5553_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_);
    crate::leanh::lean_dec(v___y_5557_);
    crate::leanh::lean_dec_ref(v___y_5556_);
    crate::leanh::lean_dec(v___y_5555_);
    crate::leanh::lean_dec_ref(v___y_5554_);
    return v_res_5559_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(
    mut v_00_u03b1_5560_: *mut crate::leanh::LeanObject,
    mut v_ref_5561_: *mut crate::leanh::LeanObject,
    mut v_msg_5562_: *mut crate::leanh::LeanObject,
    mut v___y_5563_: *mut crate::leanh::LeanObject,
    mut v___y_5564_: *mut crate::leanh::LeanObject,
    mut v___y_5565_: *mut crate::leanh::LeanObject,
    mut v___y_5566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5568_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_5561_, v_msg_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_);
    return v___x_5568_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___boxed(
    mut v_00_u03b1_5569_: *mut crate::leanh::LeanObject,
    mut v_ref_5570_: *mut crate::leanh::LeanObject,
    mut v_msg_5571_: *mut crate::leanh::LeanObject,
    mut v___y_5572_: *mut crate::leanh::LeanObject,
    mut v___y_5573_: *mut crate::leanh::LeanObject,
    mut v___y_5574_: *mut crate::leanh::LeanObject,
    mut v___y_5575_: *mut crate::leanh::LeanObject,
    mut v___y_5576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5577_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(v_00_u03b1_5569_, v_ref_5570_, v_msg_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
    crate::leanh::lean_dec(v___y_5575_);
    crate::leanh::lean_dec_ref(v___y_5574_);
    crate::leanh::lean_dec(v___y_5573_);
    crate::leanh::lean_dec_ref(v___y_5572_);
    crate::leanh::lean_dec(v_ref_5570_);
    return v_res_5577_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(
    mut v_a_5578_: *mut crate::leanh::LeanObject,
    mut v___y_5579_: *mut crate::leanh::LeanObject,
    mut v___y_5580_: *mut crate::leanh::LeanObject,
    mut v___y_5581_: *mut crate::leanh::LeanObject,
    mut v___y_5582_: *mut crate::leanh::LeanObject,
    mut v___y_5583_: *mut crate::leanh::LeanObject,
    mut v___y_5584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5586_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_5578_,
        v___y_5579_,
        v___y_5580_,
        v___y_5581_,
        v___y_5582_,
        v___y_5583_,
        v___y_5584_,
    );
    return v___x_5586_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg___boxed(
    mut v_a_5587_: *mut crate::leanh::LeanObject,
    mut v___y_5588_: *mut crate::leanh::LeanObject,
    mut v___y_5589_: *mut crate::leanh::LeanObject,
    mut v___y_5590_: *mut crate::leanh::LeanObject,
    mut v___y_5591_: *mut crate::leanh::LeanObject,
    mut v___y_5592_: *mut crate::leanh::LeanObject,
    mut v___y_5593_: *mut crate::leanh::LeanObject,
    mut v___y_5594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5595_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(v_a_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
    crate::leanh::lean_dec(v___y_5593_);
    crate::leanh::lean_dec_ref(v___y_5592_);
    crate::leanh::lean_dec(v___y_5591_);
    crate::leanh::lean_dec_ref(v___y_5590_);
    crate::leanh::lean_dec(v___y_5589_);
    crate::leanh::lean_dec_ref(v___y_5588_);
    return v_res_5595_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(
    mut v_00_u03b1_5596_: *mut crate::leanh::LeanObject,
    mut v_a_5597_: *mut crate::leanh::LeanObject,
    mut v___y_5598_: *mut crate::leanh::LeanObject,
    mut v___y_5599_: *mut crate::leanh::LeanObject,
    mut v___y_5600_: *mut crate::leanh::LeanObject,
    mut v___y_5601_: *mut crate::leanh::LeanObject,
    mut v___y_5602_: *mut crate::leanh::LeanObject,
    mut v___y_5603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5605_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_5597_,
        v___y_5598_,
        v___y_5599_,
        v___y_5600_,
        v___y_5601_,
        v___y_5602_,
        v___y_5603_,
    );
    return v___x_5605_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___boxed(
    mut v_00_u03b1_5606_: *mut crate::leanh::LeanObject,
    mut v_a_5607_: *mut crate::leanh::LeanObject,
    mut v___y_5608_: *mut crate::leanh::LeanObject,
    mut v___y_5609_: *mut crate::leanh::LeanObject,
    mut v___y_5610_: *mut crate::leanh::LeanObject,
    mut v___y_5611_: *mut crate::leanh::LeanObject,
    mut v___y_5612_: *mut crate::leanh::LeanObject,
    mut v___y_5613_: *mut crate::leanh::LeanObject,
    mut v___y_5614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5615_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(v_00_u03b1_5606_, v_a_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_);
    crate::leanh::lean_dec(v___y_5613_);
    crate::leanh::lean_dec_ref(v___y_5612_);
    crate::leanh::lean_dec(v___y_5611_);
    crate::leanh::lean_dec_ref(v___y_5610_);
    crate::leanh::lean_dec(v___y_5609_);
    crate::leanh::lean_dec_ref(v___y_5608_);
    return v_res_5615_;
}
pub unsafe fn l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(
    mut v_type_5616_: *mut crate::leanh::LeanObject,
    mut v_binds_5617_: *mut crate::leanh::LeanObject,
    mut v_pre_5618_: *mut crate::leanh::LeanObject,
    mut v___y_5619_: *mut crate::leanh::LeanObject,
    mut v___y_5620_: *mut crate::leanh::LeanObject,
    mut v___y_5621_: *mut crate::leanh::LeanObject,
    mut v___y_5622_: *mut crate::leanh::LeanObject,
    mut v___y_5623_: *mut crate::leanh::LeanObject,
    mut v___y_5624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: u8 = 0;
    let mut v___x_5629_: u8 = 0;
    let mut v___x_5630_: u8 = 0;
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5637_: u8 = 0;
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5641_: u8 = 0;
    let mut v_a_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5645_: u8 = 0;
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5626_ = l_Lean_Elab_Term_elabType(
                    v_type_5616_,
                    v___y_5619_,
                    v___y_5620_,
                    v___y_5621_,
                    v___y_5622_,
                    v___y_5623_,
                    v___y_5624_,
                );
                if crate::leanh::lean_obj_tag(v___x_5626_) == 0 {
                    v_a_5627_ = crate::leanh::lean_ctor_get(v___x_5626_, 0);
                    crate::leanh::lean_inc(v_a_5627_);
                    crate::leanh::lean_dec_ref_known(v___x_5626_, 1);
                    v___x_5628_ = 0;
                    v___x_5629_ = 1;
                    v___x_5630_ = 1;
                    v___x_5631_ = l_Lean_Meta_mkForallFVars(
                        v_binds_5617_,
                        v_a_5627_,
                        v___x_5628_,
                        v___x_5629_,
                        v___x_5629_,
                        v___x_5630_,
                        v___y_5621_,
                        v___y_5622_,
                        v___y_5623_,
                        v___y_5624_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5631_) == 0 {
                        v_a_5632_ = crate::leanh::lean_ctor_get(v___x_5631_, 0);
                        crate::leanh::lean_inc(v_a_5632_);
                        crate::leanh::lean_dec_ref_known(v___x_5631_, 1);
                        v___x_5633_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(
                            v_pre_5618_,
                            v_a_5632_,
                            v___y_5621_,
                            v___y_5622_,
                            v___y_5623_,
                            v___y_5624_,
                        );
                        return v___x_5633_;
                    } else {
                        crate::leanh::lean_dec_ref(v_pre_5618_);
                        v_a_5634_ = crate::leanh::lean_ctor_get(v___x_5631_, 0);
                        v_isSharedCheck_5641_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5631_)) as u8;
                        if v_isSharedCheck_5641_ == 0 {
                            v___x_5636_ = v___x_5631_;
                            v_isShared_5637_ = v_isSharedCheck_5641_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5634_);
                            crate::leanh::lean_dec(v___x_5631_);
                            v___x_5636_ = crate::leanh::lean_box(0);
                            v_isShared_5637_ = v_isSharedCheck_5641_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_pre_5618_);
                    v_a_5642_ = crate::leanh::lean_ctor_get(v___x_5626_, 0);
                    v_isSharedCheck_5649_ = (!crate::leanh::lean_is_exclusive(v___x_5626_)) as u8;
                    if v_isSharedCheck_5649_ == 0 {
                        v___x_5644_ = v___x_5626_;
                        v_isShared_5645_ = v_isSharedCheck_5649_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5642_);
                        crate::leanh::lean_dec(v___x_5626_);
                        v___x_5644_ = crate::leanh::lean_box(0);
                        v_isShared_5645_ = v_isSharedCheck_5649_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5637_ == 0 {
                    v___x_5639_ = v___x_5636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5640_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_a_5634_);
                    v___x_5639_ = v_reuseFailAlloc_5640_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5639_;
            }
            3 => {
                if v_isShared_5645_ == 0 {
                    v___x_5647_ = v___x_5644_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5648_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_a_5642_);
                    v___x_5647_ = v_reuseFailAlloc_5648_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed(
    mut v_type_5650_: *mut crate::leanh::LeanObject,
    mut v_binds_5651_: *mut crate::leanh::LeanObject,
    mut v_pre_5652_: *mut crate::leanh::LeanObject,
    mut v___y_5653_: *mut crate::leanh::LeanObject,
    mut v___y_5654_: *mut crate::leanh::LeanObject,
    mut v___y_5655_: *mut crate::leanh::LeanObject,
    mut v___y_5656_: *mut crate::leanh::LeanObject,
    mut v___y_5657_: *mut crate::leanh::LeanObject,
    mut v___y_5658_: *mut crate::leanh::LeanObject,
    mut v___y_5659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5660_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(
        v_type_5650_,
        v_binds_5651_,
        v_pre_5652_,
        v___y_5653_,
        v___y_5654_,
        v___y_5655_,
        v___y_5656_,
        v___y_5657_,
        v___y_5658_,
    );
    crate::leanh::lean_dec(v___y_5658_);
    crate::leanh::lean_dec_ref(v___y_5657_);
    crate::leanh::lean_dec(v___y_5656_);
    crate::leanh::lean_dec_ref(v___y_5655_);
    crate::leanh::lean_dec(v___y_5654_);
    crate::leanh::lean_dec_ref(v___y_5653_);
    crate::leanh::lean_dec_ref(v_binds_5651_);
    return v_res_5660_;
}
pub unsafe fn l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(
    mut v_type_5661_: *mut crate::leanh::LeanObject,
    mut v_pre_5662_: *mut crate::leanh::LeanObject,
    mut v_binds_5663_: *mut crate::leanh::LeanObject,
    mut v___y_5664_: *mut crate::leanh::LeanObject,
    mut v___y_5665_: *mut crate::leanh::LeanObject,
    mut v___y_5666_: *mut crate::leanh::LeanObject,
    mut v___y_5667_: *mut crate::leanh::LeanObject,
    mut v___y_5668_: *mut crate::leanh::LeanObject,
    mut v___y_5669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5671_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed
            as *mut core::ffi::c_void,
        10,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5671_, 0, v_type_5661_);
    crate::leanh::lean_closure_set(v___f_5671_, 1, v_binds_5663_);
    crate::leanh::lean_closure_set(v___f_5671_, 2, v_pre_5662_);
    v___x_5672_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v___f_5671_,
        v___y_5664_,
        v___y_5665_,
        v___y_5666_,
        v___y_5667_,
        v___y_5668_,
        v___y_5669_,
    );
    return v___x_5672_;
}
pub unsafe fn l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed(
    mut v_type_5673_: *mut crate::leanh::LeanObject,
    mut v_pre_5674_: *mut crate::leanh::LeanObject,
    mut v_binds_5675_: *mut crate::leanh::LeanObject,
    mut v___y_5676_: *mut crate::leanh::LeanObject,
    mut v___y_5677_: *mut crate::leanh::LeanObject,
    mut v___y_5678_: *mut crate::leanh::LeanObject,
    mut v___y_5679_: *mut crate::leanh::LeanObject,
    mut v___y_5680_: *mut crate::leanh::LeanObject,
    mut v___y_5681_: *mut crate::leanh::LeanObject,
    mut v___y_5682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5683_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(
        v_type_5673_,
        v_pre_5674_,
        v_binds_5675_,
        v___y_5676_,
        v___y_5677_,
        v___y_5678_,
        v___y_5679_,
        v___y_5680_,
        v___y_5681_,
    );
    crate::leanh::lean_dec(v___y_5681_);
    crate::leanh::lean_dec_ref(v___y_5680_);
    crate::leanh::lean_dec(v___y_5679_);
    crate::leanh::lean_dec_ref(v___y_5678_);
    crate::leanh::lean_dec(v___y_5677_);
    crate::leanh::lean_dec_ref(v___y_5676_);
    return v_res_5683_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(
    mut v_currNamespace_5684_: *mut crate::leanh::LeanObject,
    mut v___y_5685_: *mut crate::leanh::LeanObject,
    mut v___y_5686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5687_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5687_, 0, v_currNamespace_5684_);
    crate::leanh::lean_ctor_set(v___x_5687_, 1, v___y_5686_);
    return v___x_5687_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed(
    mut v_currNamespace_5688_: *mut crate::leanh::LeanObject,
    mut v___y_5689_: *mut crate::leanh::LeanObject,
    mut v___y_5690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5691_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(v_currNamespace_5688_, v___y_5689_, v___y_5690_);
    crate::leanh::lean_dec_ref(v___y_5689_);
    return v_res_5691_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(
    mut v_env_5692_: *mut crate::leanh::LeanObject,
    mut v_declName_5693_: *mut crate::leanh::LeanObject,
    mut v___y_5694_: *mut crate::leanh::LeanObject,
    mut v___y_5695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5696_: u8 = 0;
    let mut v_env_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: u8 = 0;
    let mut v___x_5700_: u8 = 0;
    v___x_5696_ = 0;
    v_env_5697_ = l_Lean_Environment_setExporting(v_env_5692_, v___x_5696_);
    crate::leanh::lean_inc(v_declName_5693_);
    v___x_5698_ = l_Lean_mkPrivateName(v_env_5697_, v_declName_5693_);
    v___x_5699_ = 1;
    crate::leanh::lean_inc_ref(v_env_5697_);
    v___x_5700_ = l_Lean_Environment_contains(v_env_5697_, v___x_5698_, v___x_5699_);
    if v___x_5700_ == 0 {
        let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5702_: u8 = 0;
        let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5701_ = l_Lean_privateToUserName(v_declName_5693_);
        v___x_5702_ = l_Lean_Environment_contains(v_env_5697_, v___x_5701_, v___x_5699_);
        v___x_5703_ = crate::leanh::lean_box((v___x_5702_) as usize);
        v___x_5704_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5704_, 0, v___x_5703_);
        crate::leanh::lean_ctor_set(v___x_5704_, 1, v___y_5695_);
        return v___x_5704_;
    } else {
        let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_5697_);
        crate::leanh::lean_dec(v_declName_5693_);
        v___x_5705_ = crate::leanh::lean_box((v___x_5700_) as usize);
        v___x_5706_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5706_, 0, v___x_5705_);
        crate::leanh::lean_ctor_set(v___x_5706_, 1, v___y_5695_);
        return v___x_5706_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed(
    mut v_env_5707_: *mut crate::leanh::LeanObject,
    mut v_declName_5708_: *mut crate::leanh::LeanObject,
    mut v___y_5709_: *mut crate::leanh::LeanObject,
    mut v___y_5710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5711_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(v_env_5707_, v_declName_5708_, v___y_5709_, v___y_5710_);
    crate::leanh::lean_dec_ref(v___y_5709_);
    return v_res_5711_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(
    mut v_x_5712_: *mut crate::leanh::LeanObject,
    mut v___y_5713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5712_) == 0 {
        let mut v_a_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5714_ = crate::leanh::lean_ctor_get(v_x_5712_, 0);
        crate::leanh::lean_inc(v_a_5714_);
        v___x_5715_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5715_, 0, v_a_5714_);
        crate::leanh::lean_ctor_set(v___x_5715_, 1, v___y_5713_);
        return v___x_5715_;
    } else {
        let mut v_a_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5716_ = crate::leanh::lean_ctor_get(v_x_5712_, 0);
        crate::leanh::lean_inc(v_a_5716_);
        v___x_5717_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5717_, 0, v_a_5716_);
        crate::leanh::lean_ctor_set(v___x_5717_, 1, v___y_5713_);
        return v___x_5717_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg___boxed(
    mut v_x_5718_: *mut crate::leanh::LeanObject,
    mut v___y_5719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5720_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_5718_, v___y_5719_);
    crate::leanh::lean_dec_ref(v_x_5718_);
    return v_res_5720_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(
    mut v_env_5721_: *mut crate::leanh::LeanObject,
    mut v_stx_5722_: *mut crate::leanh::LeanObject,
    mut v___y_5723_: *mut crate::leanh::LeanObject,
    mut v___y_5724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5730_: u8 = 0;
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5735_: u8 = 0;
    let mut v_unused_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5740_: u8 = 0;
    let mut v_snd_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5746_: u8 = 0;
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5751_: u8 = 0;
    let mut v_a_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5756_: u8 = 0;
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5764_: u8 = 0;
    let mut v_isSharedCheck_5765_: u8 = 0;
    let mut v_a_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5770_: u8 = 0;
    let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5725_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_5721_,
                    v_stx_5722_,
                    v___y_5723_,
                    v___y_5724_,
                );
                if crate::leanh::lean_obj_tag(v___x_5725_) == 0 {
                    v_a_5726_ = crate::leanh::lean_ctor_get(v___x_5725_, 0);
                    crate::leanh::lean_inc(v_a_5726_);
                    if crate::leanh::lean_obj_tag(v_a_5726_) == 0 {
                        v_a_5727_ = crate::leanh::lean_ctor_get(v___x_5725_, 1);
                        v_isSharedCheck_5735_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5725_)) as u8;
                        if v_isSharedCheck_5735_ == 0 {
                            v_unused_5736_ = crate::leanh::lean_ctor_get(v___x_5725_, 0);
                            crate::leanh::lean_dec(v_unused_5736_);
                            v___x_5729_ = v___x_5725_;
                            v_isShared_5730_ = v_isSharedCheck_5735_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5727_);
                            crate::leanh::lean_dec(v___x_5725_);
                            v___x_5729_ = crate::leanh::lean_box(0);
                            v_isShared_5730_ = v_isSharedCheck_5735_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_5737_ = crate::leanh::lean_ctor_get(v_a_5726_, 0);
                        v_isSharedCheck_5765_ = (!crate::leanh::lean_is_exclusive(v_a_5726_)) as u8;
                        if v_isSharedCheck_5765_ == 0 {
                            v___x_5739_ = v_a_5726_;
                            v_isShared_5740_ = v_isSharedCheck_5765_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5737_);
                            crate::leanh::lean_dec(v_a_5726_);
                            v___x_5739_ = crate::leanh::lean_box(0);
                            v_isShared_5740_ = v_isSharedCheck_5765_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_5766_ = crate::leanh::lean_ctor_get(v___x_5725_, 0);
                    v_a_5767_ = crate::leanh::lean_ctor_get(v___x_5725_, 1);
                    v_isSharedCheck_5774_ = (!crate::leanh::lean_is_exclusive(v___x_5725_)) as u8;
                    if v_isSharedCheck_5774_ == 0 {
                        v___x_5769_ = v___x_5725_;
                        v_isShared_5770_ = v_isSharedCheck_5774_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5767_);
                        crate::leanh::lean_inc(v_a_5766_);
                        crate::leanh::lean_dec(v___x_5725_);
                        v___x_5769_ = crate::leanh::lean_box(0);
                        v_isShared_5770_ = v_isSharedCheck_5774_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5731_ = crate::leanh::lean_box(0);
                if v_isShared_5730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5729_, 0, v___x_5731_);
                    v___x_5733_ = v___x_5729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5734_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5734_, 0, v___x_5731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5734_, 1, v_a_5727_);
                    v___x_5733_ = v_reuseFailAlloc_5734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5733_;
            }
            3 => {
                v_snd_5741_ = crate::leanh::lean_ctor_get(v_val_5737_, 1);
                crate::leanh::lean_inc(v_snd_5741_);
                crate::leanh::lean_dec(v_val_5737_);
                if crate::leanh::lean_obj_tag(v_snd_5741_) == 0 {
                    crate::leanh::lean_del_object(v___x_5739_);
                    v_a_5742_ = crate::leanh::lean_ctor_get(v___x_5725_, 1);
                    crate::leanh::lean_inc(v_a_5742_);
                    crate::leanh::lean_dec_ref_known(v___x_5725_, 2);
                    v_a_5743_ = crate::leanh::lean_ctor_get(v_snd_5741_, 0);
                    v_isSharedCheck_5751_ = (!crate::leanh::lean_is_exclusive(v_snd_5741_)) as u8;
                    if v_isSharedCheck_5751_ == 0 {
                        v___x_5745_ = v_snd_5741_;
                        v_isShared_5746_ = v_isSharedCheck_5751_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5743_);
                        crate::leanh::lean_dec(v_snd_5741_);
                        v___x_5745_ = crate::leanh::lean_box(0);
                        v_isShared_5746_ = v_isSharedCheck_5751_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_5752_ = crate::leanh::lean_ctor_get(v___x_5725_, 1);
                    crate::leanh::lean_inc(v_a_5752_);
                    crate::leanh::lean_dec_ref_known(v___x_5725_, 2);
                    v_a_5753_ = crate::leanh::lean_ctor_get(v_snd_5741_, 0);
                    v_isSharedCheck_5764_ = (!crate::leanh::lean_is_exclusive(v_snd_5741_)) as u8;
                    if v_isSharedCheck_5764_ == 0 {
                        v___x_5755_ = v_snd_5741_;
                        v_isShared_5756_ = v_isSharedCheck_5764_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5753_);
                        crate::leanh::lean_dec(v_snd_5741_);
                        v___x_5755_ = crate::leanh::lean_box(0);
                        v_isShared_5756_ = v_isSharedCheck_5764_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5746_ == 0 {
                    v___x_5748_ = v___x_5745_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_a_5743_);
                    v___x_5748_ = v_reuseFailAlloc_5750_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5749_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_5748_, v_a_5742_);
                crate::leanh::lean_dec_ref(v___x_5748_);
                return v___x_5749_;
            }
            6 => {
                if v_isShared_5740_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5739_, 0, v_a_5753_);
                    v___x_5758_ = v___x_5739_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5753_);
                    v___x_5758_ = v_reuseFailAlloc_5763_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5756_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5755_, 0, v___x_5758_);
                    v___x_5760_ = v___x_5755_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5762_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5762_, 0, v___x_5758_);
                    v___x_5760_ = v_reuseFailAlloc_5762_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5761_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_5760_, v_a_5752_);
                crate::leanh::lean_dec_ref(v___x_5760_);
                return v___x_5761_;
            }
            9 => {
                if v_isShared_5770_ == 0 {
                    v___x_5772_ = v___x_5769_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5773_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5773_, 0, v_a_5766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5773_, 1, v_a_5767_);
                    v___x_5772_ = v_reuseFailAlloc_5773_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5772_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed(
    mut v_env_5775_: *mut crate::leanh::LeanObject,
    mut v_stx_5776_: *mut crate::leanh::LeanObject,
    mut v___y_5777_: *mut crate::leanh::LeanObject,
    mut v___y_5778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5779_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(v_env_5775_, v_stx_5776_, v___y_5777_, v___y_5778_);
    crate::leanh::lean_dec_ref(v___y_5777_);
    return v_res_5779_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(
    mut v_opts_5780_: *mut crate::leanh::LeanObject,
    mut v_opt_5781_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5782_ = crate::leanh::lean_ctor_get(v_opt_5781_, 0);
    v_defValue_5783_ = crate::leanh::lean_ctor_get(v_opt_5781_, 1);
    v_map_5784_ = crate::leanh::lean_ctor_get(v_opts_5780_, 0);
    v___x_5785_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5784_,
            v_name_5782_,
        );
    if crate::leanh::lean_obj_tag(v___x_5785_) == 0 {
        let mut v___x_5786_: u8 = 0;
        v___x_5786_ = (crate::leanh::lean_unbox(v_defValue_5783_) as u8);
        return v___x_5786_;
    } else {
        let mut v_val_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5787_ = crate::leanh::lean_ctor_get(v___x_5785_, 0);
        crate::leanh::lean_inc(v_val_5787_);
        crate::leanh::lean_dec_ref_known(v___x_5785_, 1);
        if crate::leanh::lean_obj_tag(v_val_5787_) == 1 {
            let mut v_v_5788_: u8 = 0;
            v_v_5788_ = crate::leanh::lean_ctor_get_uint8(v_val_5787_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_5787_, 0);
            return v_v_5788_;
        } else {
            let mut v___x_5789_: u8 = 0;
            crate::leanh::lean_dec(v_val_5787_);
            v___x_5789_ = (crate::leanh::lean_unbox(v_defValue_5783_) as u8);
            return v___x_5789_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17___boxed(
    mut v_opts_5790_: *mut crate::leanh::LeanObject,
    mut v_opt_5791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5792_: u8 = 0;
    let mut v_r_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5792_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v_opts_5790_, v_opt_5791_);
    crate::leanh::lean_dec_ref(v_opt_5791_);
    crate::leanh::lean_dec_ref(v_opts_5790_);
    v_r_5793_ = crate::leanh::lean_box((v_res_5792_) as usize);
    return v_r_5793_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5794_ = crate::leanh::lean_box(1);
    v___x_5795_ = l_Lean_MessageData_ofFormat(v___x_5794_);
    return v___x_5795_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5799_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__2;
    v___x_5800_ = l_Lean_MessageData_ofFormat(v___x_5799_);
    return v___x_5800_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(
    mut v_x_5801_: *mut crate::leanh::LeanObject,
    mut v_x_5802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5807_: u8 = 0;
    let mut v_before_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5811_: u8 = 0;
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5824_: u8 = 0;
    let mut v_unused_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5826_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5802_) == 0 {
                    return v_x_5801_;
                } else {
                    v_head_5803_ = crate::leanh::lean_ctor_get(v_x_5802_, 0);
                    v_tail_5804_ = crate::leanh::lean_ctor_get(v_x_5802_, 1);
                    v_isSharedCheck_5826_ = (!crate::leanh::lean_is_exclusive(v_x_5802_)) as u8;
                    if v_isSharedCheck_5826_ == 0 {
                        v___x_5806_ = v_x_5802_;
                        v_isShared_5807_ = v_isSharedCheck_5826_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5804_);
                        crate::leanh::lean_inc(v_head_5803_);
                        crate::leanh::lean_dec(v_x_5802_);
                        v___x_5806_ = crate::leanh::lean_box(0);
                        v_isShared_5807_ = v_isSharedCheck_5826_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_5808_ = crate::leanh::lean_ctor_get(v_head_5803_, 0);
                v_isSharedCheck_5824_ = (!crate::leanh::lean_is_exclusive(v_head_5803_)) as u8;
                if v_isSharedCheck_5824_ == 0 {
                    v_unused_5825_ = crate::leanh::lean_ctor_get(v_head_5803_, 1);
                    crate::leanh::lean_dec(v_unused_5825_);
                    v___x_5810_ = v_head_5803_;
                    v_isShared_5811_ = v_isSharedCheck_5824_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_5808_);
                    crate::leanh::lean_dec(v_head_5803_);
                    v___x_5810_ = crate::leanh::lean_box(0);
                    v_isShared_5811_ = v_isSharedCheck_5824_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5812_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0);
                if v_isShared_5811_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5810_, 7);
                    crate::leanh::lean_ctor_set(v___x_5810_, 1, v___x_5812_);
                    crate::leanh::lean_ctor_set(v___x_5810_, 0, v_x_5801_);
                    v___x_5814_ = v___x_5810_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5823_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5823_, 0, v_x_5801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5823_, 1, v___x_5812_);
                    v___x_5814_ = v_reuseFailAlloc_5823_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5815_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3);
                if v_isShared_5807_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5806_, 7);
                    crate::leanh::lean_ctor_set(v___x_5806_, 1, v___x_5815_);
                    crate::leanh::lean_ctor_set(v___x_5806_, 0, v___x_5814_);
                    v___x_5817_ = v___x_5806_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5822_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5822_, 0, v___x_5814_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5822_, 1, v___x_5815_);
                    v___x_5817_ = v_reuseFailAlloc_5822_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5818_ = l_Lean_MessageData_ofSyntax(v_before_5808_);
                v___x_5819_ = l_Lean_indentD(v___x_5818_);
                v___x_5820_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5820_, 0, v___x_5817_);
                crate::leanh::lean_ctor_set(v___x_5820_, 1, v___x_5819_);
                v_x_5801_ = v___x_5820_;
                v_x_5802_ = v_tail_5804_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5830_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1;
    v___x_5831_ = l_Lean_MessageData_ofFormat(v___x_5830_);
    return v___x_5831_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(
    mut v_msgData_5832_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5833_: *mut crate::leanh::LeanObject,
    mut v___y_5834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: u8 = 0;
    let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5845_: u8 = 0;
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5857_: u8 = 0;
    let mut v_unused_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5836_ = crate::leanh::lean_ctor_get(v___y_5834_, 2);
                v___x_5837_ = l_Lean_Elab_pp_macroStack;
                v___x_5838_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v_options_5836_, v___x_5837_);
                if v___x_5838_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_5833_);
                    v___x_5839_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5839_, 0, v_msgData_5832_);
                    return v___x_5839_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_5833_) == 0 {
                        v___x_5840_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5840_, 0, v_msgData_5832_);
                        return v___x_5840_;
                    } else {
                        v_head_5841_ = crate::leanh::lean_ctor_get(v_macroStack_5833_, 0);
                        crate::leanh::lean_inc(v_head_5841_);
                        v_after_5842_ = crate::leanh::lean_ctor_get(v_head_5841_, 1);
                        v_isSharedCheck_5857_ =
                            (!crate::leanh::lean_is_exclusive(v_head_5841_)) as u8;
                        if v_isSharedCheck_5857_ == 0 {
                            v_unused_5858_ = crate::leanh::lean_ctor_get(v_head_5841_, 0);
                            crate::leanh::lean_dec(v_unused_5858_);
                            v___x_5844_ = v_head_5841_;
                            v_isShared_5845_ = v_isSharedCheck_5857_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_5842_);
                            crate::leanh::lean_dec(v_head_5841_);
                            v___x_5844_ = crate::leanh::lean_box(0);
                            v_isShared_5845_ = v_isSharedCheck_5857_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5846_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0);
                if v_isShared_5845_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5844_, 7);
                    crate::leanh::lean_ctor_set(v___x_5844_, 1, v___x_5846_);
                    crate::leanh::lean_ctor_set(v___x_5844_, 0, v_msgData_5832_);
                    v___x_5848_ = v___x_5844_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5856_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5856_, 0, v_msgData_5832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5856_, 1, v___x_5846_);
                    v___x_5848_ = v_reuseFailAlloc_5856_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5849_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2);
                v___x_5850_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5850_, 0, v___x_5848_);
                crate::leanh::lean_ctor_set(v___x_5850_, 1, v___x_5849_);
                v___x_5851_ = l_Lean_MessageData_ofSyntax(v_after_5842_);
                v___x_5852_ = l_Lean_indentD(v___x_5851_);
                v_msgData_5853_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_5853_, 0, v___x_5850_);
                crate::leanh::lean_ctor_set(v_msgData_5853_, 1, v___x_5852_);
                v___x_5854_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(v_msgData_5853_, v_macroStack_5833_);
                v___x_5855_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5855_, 0, v___x_5854_);
                return v___x_5855_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___boxed(
    mut v_msgData_5859_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5860_: *mut crate::leanh::LeanObject,
    mut v___y_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5863_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_5859_, v_macroStack_5860_, v___y_5861_);
    crate::leanh::lean_dec_ref(v___y_5861_);
    return v_res_5863_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(
    mut v_msg_5864_: *mut crate::leanh::LeanObject,
    mut v___y_5865_: *mut crate::leanh::LeanObject,
    mut v___y_5866_: *mut crate::leanh::LeanObject,
    mut v___y_5867_: *mut crate::leanh::LeanObject,
    mut v___y_5868_: *mut crate::leanh::LeanObject,
    mut v___y_5869_: *mut crate::leanh::LeanObject,
    mut v___y_5870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5881_: u8 = 0;
    let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5872_ = crate::leanh::lean_ctor_get(v___y_5869_, 5);
                v___x_5873_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_5864_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
                v_a_5874_ = crate::leanh::lean_ctor_get(v___x_5873_, 0);
                crate::leanh::lean_inc(v_a_5874_);
                crate::leanh::lean_dec_ref(v___x_5873_);
                v_macroStack_5875_ = crate::leanh::lean_ctor_get(v___y_5865_, 1);
                v___x_5876_ = l_Lean_Elab_getBetterRef(v_ref_5872_, v_macroStack_5875_);
                crate::leanh::lean_inc(v_macroStack_5875_);
                v___x_5877_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_a_5874_, v_macroStack_5875_, v___y_5869_);
                v_a_5878_ = crate::leanh::lean_ctor_get(v___x_5877_, 0);
                v_isSharedCheck_5886_ = (!crate::leanh::lean_is_exclusive(v___x_5877_)) as u8;
                if v_isSharedCheck_5886_ == 0 {
                    v___x_5880_ = v___x_5877_;
                    v_isShared_5881_ = v_isSharedCheck_5886_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5878_);
                    crate::leanh::lean_dec(v___x_5877_);
                    v___x_5880_ = crate::leanh::lean_box(0);
                    v_isShared_5881_ = v_isSharedCheck_5886_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5882_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5882_, 0, v___x_5876_);
                crate::leanh::lean_ctor_set(v___x_5882_, 1, v_a_5878_);
                if v_isShared_5881_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5880_, 1);
                    crate::leanh::lean_ctor_set(v___x_5880_, 0, v___x_5882_);
                    v___x_5884_ = v___x_5880_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5885_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5885_, 0, v___x_5882_);
                    v___x_5884_ = v_reuseFailAlloc_5885_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg___boxed(
    mut v_msg_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
    mut v___y_5889_: *mut crate::leanh::LeanObject,
    mut v___y_5890_: *mut crate::leanh::LeanObject,
    mut v___y_5891_: *mut crate::leanh::LeanObject,
    mut v___y_5892_: *mut crate::leanh::LeanObject,
    mut v___y_5893_: *mut crate::leanh::LeanObject,
    mut v___y_5894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5895_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_);
    crate::leanh::lean_dec(v___y_5893_);
    crate::leanh::lean_dec_ref(v___y_5892_);
    crate::leanh::lean_dec(v___y_5891_);
    crate::leanh::lean_dec_ref(v___y_5890_);
    crate::leanh::lean_dec(v___y_5889_);
    crate::leanh::lean_dec_ref(v___y_5888_);
    return v_res_5895_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(
    mut v_ref_5896_: *mut crate::leanh::LeanObject,
    mut v_msg_5897_: *mut crate::leanh::LeanObject,
    mut v___y_5898_: *mut crate::leanh::LeanObject,
    mut v___y_5899_: *mut crate::leanh::LeanObject,
    mut v___y_5900_: *mut crate::leanh::LeanObject,
    mut v___y_5901_: *mut crate::leanh::LeanObject,
    mut v___y_5902_: *mut crate::leanh::LeanObject,
    mut v___y_5903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5917_: u8 = 0;
    let mut v_cancelTk_x3f_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5919_: u8 = 0;
    let mut v_inheritedTraceOptions_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5905_ = crate::leanh::lean_ctor_get(v___y_5902_, 0);
    v_fileMap_5906_ = crate::leanh::lean_ctor_get(v___y_5902_, 1);
    v_options_5907_ = crate::leanh::lean_ctor_get(v___y_5902_, 2);
    v_currRecDepth_5908_ = crate::leanh::lean_ctor_get(v___y_5902_, 3);
    v_maxRecDepth_5909_ = crate::leanh::lean_ctor_get(v___y_5902_, 4);
    v_ref_5910_ = crate::leanh::lean_ctor_get(v___y_5902_, 5);
    v_currNamespace_5911_ = crate::leanh::lean_ctor_get(v___y_5902_, 6);
    v_openDecls_5912_ = crate::leanh::lean_ctor_get(v___y_5902_, 7);
    v_initHeartbeats_5913_ = crate::leanh::lean_ctor_get(v___y_5902_, 8);
    v_maxHeartbeats_5914_ = crate::leanh::lean_ctor_get(v___y_5902_, 9);
    v_quotContext_5915_ = crate::leanh::lean_ctor_get(v___y_5902_, 10);
    v_currMacroScope_5916_ = crate::leanh::lean_ctor_get(v___y_5902_, 11);
    v_diag_5917_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5902_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5918_ = crate::leanh::lean_ctor_get(v___y_5902_, 12);
    v_suppressElabErrors_5919_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5902_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5920_ = crate::leanh::lean_ctor_get(v___y_5902_, 13);
    v_ref_5921_ = l_Lean_replaceRef(v_ref_5896_, v_ref_5910_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5920_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5918_);
    crate::leanh::lean_inc(v_currMacroScope_5916_);
    crate::leanh::lean_inc(v_quotContext_5915_);
    crate::leanh::lean_inc(v_maxHeartbeats_5914_);
    crate::leanh::lean_inc(v_initHeartbeats_5913_);
    crate::leanh::lean_inc(v_openDecls_5912_);
    crate::leanh::lean_inc(v_currNamespace_5911_);
    crate::leanh::lean_inc(v_maxRecDepth_5909_);
    crate::leanh::lean_inc(v_currRecDepth_5908_);
    crate::leanh::lean_inc_ref(v_options_5907_);
    crate::leanh::lean_inc_ref(v_fileMap_5906_);
    crate::leanh::lean_inc_ref(v_fileName_5905_);
    v___x_5922_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5922_, 0, v_fileName_5905_);
    crate::leanh::lean_ctor_set(v___x_5922_, 1, v_fileMap_5906_);
    crate::leanh::lean_ctor_set(v___x_5922_, 2, v_options_5907_);
    crate::leanh::lean_ctor_set(v___x_5922_, 3, v_currRecDepth_5908_);
    crate::leanh::lean_ctor_set(v___x_5922_, 4, v_maxRecDepth_5909_);
    crate::leanh::lean_ctor_set(v___x_5922_, 5, v_ref_5921_);
    crate::leanh::lean_ctor_set(v___x_5922_, 6, v_currNamespace_5911_);
    crate::leanh::lean_ctor_set(v___x_5922_, 7, v_openDecls_5912_);
    crate::leanh::lean_ctor_set(v___x_5922_, 8, v_initHeartbeats_5913_);
    crate::leanh::lean_ctor_set(v___x_5922_, 9, v_maxHeartbeats_5914_);
    crate::leanh::lean_ctor_set(v___x_5922_, 10, v_quotContext_5915_);
    crate::leanh::lean_ctor_set(v___x_5922_, 11, v_currMacroScope_5916_);
    crate::leanh::lean_ctor_set(v___x_5922_, 12, v_cancelTk_x3f_5918_);
    crate::leanh::lean_ctor_set(v___x_5922_, 13, v_inheritedTraceOptions_5920_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5922_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5917_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5922_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5919_,
    );
    v___x_5923_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_5897_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_, v___x_5922_, v___y_5903_);
    crate::leanh::lean_dec_ref_known(v___x_5922_, 14);
    return v___x_5923_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg___boxed(
    mut v_ref_5924_: *mut crate::leanh::LeanObject,
    mut v_msg_5925_: *mut crate::leanh::LeanObject,
    mut v___y_5926_: *mut crate::leanh::LeanObject,
    mut v___y_5927_: *mut crate::leanh::LeanObject,
    mut v___y_5928_: *mut crate::leanh::LeanObject,
    mut v___y_5929_: *mut crate::leanh::LeanObject,
    mut v___y_5930_: *mut crate::leanh::LeanObject,
    mut v___y_5931_: *mut crate::leanh::LeanObject,
    mut v___y_5932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5933_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_5924_, v_msg_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_);
    crate::leanh::lean_dec(v___y_5931_);
    crate::leanh::lean_dec_ref(v___y_5930_);
    crate::leanh::lean_dec(v___y_5929_);
    crate::leanh::lean_dec_ref(v___y_5928_);
    crate::leanh::lean_dec(v___y_5927_);
    crate::leanh::lean_dec_ref(v___y_5926_);
    crate::leanh::lean_dec(v_ref_5924_);
    return v_res_5933_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: f64 = 0.0;
    v___x_5934_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5935_ = lean_float_of_nat(v___x_5934_);
    return v___x_5935_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(
    mut v_cls_5938_: *mut crate::leanh::LeanObject,
    mut v_msg_5939_: *mut crate::leanh::LeanObject,
    mut v___y_5940_: *mut crate::leanh::LeanObject,
    mut v___y_5941_: *mut crate::leanh::LeanObject,
    mut v___y_5942_: *mut crate::leanh::LeanObject,
    mut v___y_5943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5950_: u8 = 0;
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5963_: u8 = 0;
    let mut v_tid_5964_: u64 = 0;
    let mut v_traces_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5968_: u8 = 0;
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: f64 = 0.0;
    let mut v___x_5971_: u8 = 0;
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5989_: u8 = 0;
    let mut v_isSharedCheck_5990_: u8 = 0;
    let mut v_isSharedCheck_5991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5945_ = crate::leanh::lean_ctor_get(v___y_5942_, 5);
                v___x_5946_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_5939_, v___y_5940_, v___y_5941_, v___y_5942_, v___y_5943_);
                v_a_5947_ = crate::leanh::lean_ctor_get(v___x_5946_, 0);
                v_isSharedCheck_5991_ = (!crate::leanh::lean_is_exclusive(v___x_5946_)) as u8;
                if v_isSharedCheck_5991_ == 0 {
                    v___x_5949_ = v___x_5946_;
                    v_isShared_5950_ = v_isSharedCheck_5991_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5947_);
                    crate::leanh::lean_dec(v___x_5946_);
                    v___x_5949_ = crate::leanh::lean_box(0);
                    v_isShared_5950_ = v_isSharedCheck_5991_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5951_ = lean_st_ref_take(v___y_5943_);
                v_traceState_5952_ = crate::leanh::lean_ctor_get(v___x_5951_, 4);
                v_env_5953_ = crate::leanh::lean_ctor_get(v___x_5951_, 0);
                v_nextMacroScope_5954_ = crate::leanh::lean_ctor_get(v___x_5951_, 1);
                v_ngen_5955_ = crate::leanh::lean_ctor_get(v___x_5951_, 2);
                v_auxDeclNGen_5956_ = crate::leanh::lean_ctor_get(v___x_5951_, 3);
                v_cache_5957_ = crate::leanh::lean_ctor_get(v___x_5951_, 5);
                v_messages_5958_ = crate::leanh::lean_ctor_get(v___x_5951_, 6);
                v_infoState_5959_ = crate::leanh::lean_ctor_get(v___x_5951_, 7);
                v_snapshotTasks_5960_ = crate::leanh::lean_ctor_get(v___x_5951_, 8);
                v_isSharedCheck_5990_ = (!crate::leanh::lean_is_exclusive(v___x_5951_)) as u8;
                if v_isSharedCheck_5990_ == 0 {
                    v___x_5962_ = v___x_5951_;
                    v_isShared_5963_ = v_isSharedCheck_5990_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5960_);
                    crate::leanh::lean_inc(v_infoState_5959_);
                    crate::leanh::lean_inc(v_messages_5958_);
                    crate::leanh::lean_inc(v_cache_5957_);
                    crate::leanh::lean_inc(v_traceState_5952_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5956_);
                    crate::leanh::lean_inc(v_ngen_5955_);
                    crate::leanh::lean_inc(v_nextMacroScope_5954_);
                    crate::leanh::lean_inc(v_env_5953_);
                    crate::leanh::lean_dec(v___x_5951_);
                    v___x_5962_ = crate::leanh::lean_box(0);
                    v_isShared_5963_ = v_isSharedCheck_5990_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5964_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_5952_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5965_ = crate::leanh::lean_ctor_get(v_traceState_5952_, 0);
                v_isSharedCheck_5989_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_5952_)) as u8;
                if v_isSharedCheck_5989_ == 0 {
                    v___x_5967_ = v_traceState_5952_;
                    v_isShared_5968_ = v_isSharedCheck_5989_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_5965_);
                    crate::leanh::lean_dec(v_traceState_5952_);
                    v___x_5967_ = crate::leanh::lean_box(0);
                    v_isShared_5968_ = v_isSharedCheck_5989_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5969_ = crate::leanh::lean_box(0);
                v___x_5970_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0);
                v___x_5971_ = 0;
                v___x_5972_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0;
                v___x_5973_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_5973_, 0, v_cls_5938_);
                crate::leanh::lean_ctor_set(v___x_5973_, 1, v___x_5969_);
                crate::leanh::lean_ctor_set(v___x_5973_, 2, v___x_5972_);
                crate::leanh::lean_ctor_set_float(
                    v___x_5973_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5970_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_5973_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5970_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5973_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_5971_,
                );
                v___x_5974_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1;
                v___x_5975_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5975_, 0, v___x_5973_);
                crate::leanh::lean_ctor_set(v___x_5975_, 1, v_a_5947_);
                crate::leanh::lean_ctor_set(v___x_5975_, 2, v___x_5974_);
                crate::leanh::lean_inc(v_ref_5945_);
                v___x_5976_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5976_, 0, v_ref_5945_);
                crate::leanh::lean_ctor_set(v___x_5976_, 1, v___x_5975_);
                v___x_5977_ = l_Lean_PersistentArray_push___redArg(v_traces_5965_, v___x_5976_);
                if v_isShared_5968_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5967_, 0, v___x_5977_);
                    v___x_5979_ = v___x_5967_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5988_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5988_, 0, v___x_5977_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5988_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_5964_,
                    );
                    v___x_5979_ = v_reuseFailAlloc_5988_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5962_, 4, v___x_5979_);
                    v___x_5981_ = v___x_5962_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5987_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 0, v_env_5953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 1, v_nextMacroScope_5954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 2, v_ngen_5955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 3, v_auxDeclNGen_5956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 4, v___x_5979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 5, v_cache_5957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 6, v_messages_5958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 7, v_infoState_5959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 8, v_snapshotTasks_5960_);
                    v___x_5981_ = v_reuseFailAlloc_5987_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5982_ = lean_st_ref_set(v___y_5943_, v___x_5981_);
                v___x_5983_ = crate::leanh::lean_box(0);
                if v_isShared_5950_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5949_, 0, v___x_5983_);
                    v___x_5985_ = v___x_5949_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5986_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5986_, 0, v___x_5983_);
                    v___x_5985_ = v_reuseFailAlloc_5986_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___boxed(
    mut v_cls_5992_: *mut crate::leanh::LeanObject,
    mut v_msg_5993_: *mut crate::leanh::LeanObject,
    mut v___y_5994_: *mut crate::leanh::LeanObject,
    mut v___y_5995_: *mut crate::leanh::LeanObject,
    mut v___y_5996_: *mut crate::leanh::LeanObject,
    mut v___y_5997_: *mut crate::leanh::LeanObject,
    mut v___y_5998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5999_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_5992_, v_msg_5993_, v___y_5994_, v___y_5995_, v___y_5996_, v___y_5997_);
    crate::leanh::lean_dec(v___y_5997_);
    crate::leanh::lean_dec_ref(v___y_5996_);
    crate::leanh::lean_dec(v___y_5995_);
    crate::leanh::lean_dec_ref(v___y_5994_);
    return v_res_5999_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(
    mut v_as_6003_: *mut crate::leanh::LeanObject,
    mut v___y_6004_: *mut crate::leanh::LeanObject,
    mut v___y_6005_: *mut crate::leanh::LeanObject,
    mut v___y_6006_: *mut crate::leanh::LeanObject,
    mut v___y_6007_: *mut crate::leanh::LeanObject,
    mut v___y_6008_: *mut crate::leanh::LeanObject,
    mut v___y_6009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6014_: u8 = 0;
    let mut v_tail_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: u8 = 0;
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_6003_) == 0 {
                    v___x_6011_ = crate::leanh::lean_box(0);
                    v___x_6012_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6012_, 0, v___x_6011_);
                    return v___x_6012_;
                } else {
                    v_options_6013_ = crate::leanh::lean_ctor_get(v___y_6008_, 2);
                    v_hasTrace_6014_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_6013_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6014_ == 0 {
                        v_tail_6015_ = crate::leanh::lean_ctor_get(v_as_6003_, 1);
                        crate::leanh::lean_inc(v_tail_6015_);
                        crate::leanh::lean_dec_ref_known(v_as_6003_, 2);
                        v_as_6003_ = v_tail_6015_;
                        state = 0;
                        continue;
                    } else {
                        v_head_6017_ = crate::leanh::lean_ctor_get(v_as_6003_, 0);
                        crate::leanh::lean_inc(v_head_6017_);
                        v_tail_6018_ = crate::leanh::lean_ctor_get(v_as_6003_, 1);
                        crate::leanh::lean_inc(v_tail_6018_);
                        crate::leanh::lean_dec_ref_known(v_as_6003_, 2);
                        v_fst_6019_ = crate::leanh::lean_ctor_get(v_head_6017_, 0);
                        crate::leanh::lean_inc_n(v_fst_6019_, 2);
                        v_snd_6020_ = crate::leanh::lean_ctor_get(v_head_6017_, 1);
                        crate::leanh::lean_inc(v_snd_6020_);
                        crate::leanh::lean_dec(v_head_6017_);
                        v_inheritedTraceOptions_6021_ =
                            crate::leanh::lean_ctor_get(v___y_6008_, 13);
                        v___x_6022_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1;
                        v___x_6023_ = l_Lean_Name_append(v___x_6022_, v_fst_6019_);
                        v___x_6024_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_6021_,
                            v_options_6013_,
                            v___x_6023_,
                        );
                        crate::leanh::lean_dec(v___x_6023_);
                        if v___x_6024_ == 0 {
                            crate::leanh::lean_dec(v_snd_6020_);
                            crate::leanh::lean_dec(v_fst_6019_);
                            v_as_6003_ = v_tail_6018_;
                            state = 0;
                            continue;
                        } else {
                            v___x_6026_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6026_, 0, v_snd_6020_);
                            v___x_6027_ = l_Lean_MessageData_ofFormat(v___x_6026_);
                            v___x_6028_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_fst_6019_, v___x_6027_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_);
                            if crate::leanh::lean_obj_tag(v___x_6028_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6028_, 1);
                                v_as_6003_ = v_tail_6018_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_tail_6018_);
                                return v___x_6028_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___boxed(
    mut v_as_6030_: *mut crate::leanh::LeanObject,
    mut v___y_6031_: *mut crate::leanh::LeanObject,
    mut v___y_6032_: *mut crate::leanh::LeanObject,
    mut v___y_6033_: *mut crate::leanh::LeanObject,
    mut v___y_6034_: *mut crate::leanh::LeanObject,
    mut v___y_6035_: *mut crate::leanh::LeanObject,
    mut v___y_6036_: *mut crate::leanh::LeanObject,
    mut v___y_6037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6038_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v_as_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_);
    crate::leanh::lean_dec(v___y_6036_);
    crate::leanh::lean_dec_ref(v___y_6035_);
    crate::leanh::lean_dec(v___y_6034_);
    crate::leanh::lean_dec_ref(v___y_6033_);
    crate::leanh::lean_dec(v___y_6032_);
    crate::leanh::lean_dec_ref(v___y_6031_);
    return v_res_6038_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(
    mut v_keys_6039_: *mut crate::leanh::LeanObject,
    mut v_i_6040_: *mut crate::leanh::LeanObject,
    mut v_k_6041_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: u8 = 0;
    let mut v_k_x27_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: u8 = 0;
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6042_ = lean_array_get_size(v_keys_6039_);
                v___x_6043_ = lean_nat_dec_lt(v_i_6040_, v___x_6042_);
                if v___x_6043_ == 0 {
                    crate::leanh::lean_dec(v_i_6040_);
                    return v___x_6043_;
                } else {
                    v_k_x27_6044_ = lean_array_fget_borrowed(v_keys_6039_, v_i_6040_);
                    v___x_6045_ = l_Lean_instBEqExtraModUse_beq(v_k_6041_, v_k_x27_6044_);
                    if v___x_6045_ == 0 {
                        v___x_6046_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6047_ = lean_nat_add(v_i_6040_, v___x_6046_);
                        crate::leanh::lean_dec(v_i_6040_);
                        v_i_6040_ = v___x_6047_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_6040_);
                        return v___x_6045_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg___boxed(
    mut v_keys_6049_: *mut crate::leanh::LeanObject,
    mut v_i_6050_: *mut crate::leanh::LeanObject,
    mut v_k_6051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6052_: u8 = 0;
    let mut v_r_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6052_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_6049_, v_i_6050_, v_k_6051_);
    crate::leanh::lean_dec_ref(v_k_6051_);
    crate::leanh::lean_dec_ref(v_keys_6049_);
    v_r_6053_ = crate::leanh::lean_box((v_res_6052_) as usize);
    return v_r_6053_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___closed__0()
-> usize {
    let mut v___x_6054_: usize = 0;
    let mut v___x_6055_: usize = 0;
    let mut v___x_6056_: usize = 0;
    v___x_6054_ = 5usize;
    v___x_6055_ = 1usize;
    v___x_6056_ = lean_usize_shift_left(v___x_6055_, v___x_6054_);
    return v___x_6056_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___closed__1()
-> usize {
    let mut v___x_6057_: usize = 0;
    let mut v___x_6058_: usize = 0;
    let mut v___x_6059_: usize = 0;
    v___x_6057_ = 1usize;
    v___x_6058_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___closed__0);
    v___x_6059_ = lean_usize_sub(v___x_6058_, v___x_6057_);
    return v___x_6059_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(
    mut v_x_6060_: *mut crate::leanh::LeanObject,
    mut v_x_6061_: usize,
    mut v_x_6062_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: usize = 0;
    let mut v___x_6066_: usize = 0;
    let mut v___x_6067_: usize = 0;
    let mut v_j_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: u8 = 0;
    let mut v_node_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: usize = 0;
    let mut v___x_6075_: u8 = 0;
    let mut v_ks_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6060_) == 0 {
                    v_es_6063_ = crate::leanh::lean_ctor_get(v_x_6060_, 0);
                    v___x_6064_ = crate::leanh::lean_box(2);
                    v___x_6065_ = 5usize;
                    v___x_6066_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___closed__1);
                    v___x_6067_ = lean_usize_land(v_x_6061_, v___x_6066_);
                    v_j_6068_ = lean_usize_to_nat(v___x_6067_);
                    v___x_6069_ = lean_array_get_borrowed(v___x_6064_, v_es_6063_, v_j_6068_);
                    crate::leanh::lean_dec(v_j_6068_);
                    match crate::leanh::lean_obj_tag(v___x_6069_) {
                        0 => {
                            v_key_6070_ = crate::leanh::lean_ctor_get(v___x_6069_, 0);
                            v___x_6071_ = l_Lean_instBEqExtraModUse_beq(v_x_6062_, v_key_6070_);
                            return v___x_6071_;
                        }
                        1 => {
                            v_node_6072_ = crate::leanh::lean_ctor_get(v___x_6069_, 0);
                            v___x_6073_ = lean_usize_shift_right(v_x_6061_, v___x_6065_);
                            v_x_6060_ = v_node_6072_;
                            v_x_6061_ = v___x_6073_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_6075_ = 0;
                            return v___x_6075_;
                        }
                    }
                } else {
                    v_ks_6076_ = crate::leanh::lean_ctor_get(v_x_6060_, 0);
                    v___x_6077_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6078_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_ks_6076_, v___x_6077_, v_x_6062_);
                    return v___x_6078_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___boxed(
    mut v_x_6079_: *mut crate::leanh::LeanObject,
    mut v_x_6080_: *mut crate::leanh::LeanObject,
    mut v_x_6081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_14859__boxed_6082_: usize = 0;
    let mut v_res_6083_: u8 = 0;
    let mut v_r_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_14859__boxed_6082_ = crate::leanh::lean_unbox_usize(v_x_6080_);
    crate::leanh::lean_dec(v_x_6080_);
    v_res_6083_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_6079_, v_x_14859__boxed_6082_, v_x_6081_);
    crate::leanh::lean_dec_ref(v_x_6081_);
    crate::leanh::lean_dec_ref(v_x_6079_);
    v_r_6084_ = crate::leanh::lean_box((v_res_6083_) as usize);
    return v_r_6084_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(
    mut v_x_6085_: *mut crate::leanh::LeanObject,
    mut v_x_6086_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6087_: u64 = 0;
    let mut v___x_6088_: usize = 0;
    let mut v___x_6089_: u8 = 0;
    v___x_6087_ = l_Lean_instHashableExtraModUse_hash(v_x_6086_);
    v___x_6088_ = lean_uint64_to_usize(v___x_6087_);
    v___x_6089_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_6085_, v___x_6088_, v_x_6086_);
    return v___x_6089_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg___boxed(
    mut v_x_6090_: *mut crate::leanh::LeanObject,
    mut v_x_6091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6092_: u8 = 0;
    let mut v_r_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6092_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_6090_, v_x_6091_);
    crate::leanh::lean_dec_ref(v_x_6091_);
    crate::leanh::lean_dec_ref(v_x_6090_);
    v_r_6093_ = crate::leanh::lean_box((v_res_6092_) as usize);
    return v_r_6093_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6096_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1;
    v___x_6097_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0;
    v___x_6098_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6097_,
        v___x_6096_,
    );
    return v___x_6098_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6099_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6099_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6100_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3);
    v___x_6101_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6101_, 0, v___x_6100_);
    return v___x_6101_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6102_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4);
    v___x_6103_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6103_, 0, v___x_6102_);
    crate::leanh::lean_ctor_set(v___x_6103_, 1, v___x_6102_);
    return v___x_6103_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6104_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4);
    v___x_6105_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6105_, 0, v___x_6104_);
    crate::leanh::lean_ctor_set(v___x_6105_, 1, v___x_6104_);
    crate::leanh::lean_ctor_set(v___x_6105_, 2, v___x_6104_);
    crate::leanh::lean_ctor_set(v___x_6105_, 3, v___x_6104_);
    crate::leanh::lean_ctor_set(v___x_6105_, 4, v___x_6104_);
    crate::leanh::lean_ctor_set(v___x_6105_, 5, v___x_6104_);
    return v___x_6105_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6110_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9;
    v___x_6111_ = l_Lean_stringToMessageData(v___x_6110_);
    return v___x_6111_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6113_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11;
    v___x_6114_ = l_Lean_stringToMessageData(v___x_6113_);
    return v___x_6114_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6115_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0;
    v___x_6116_ = l_Lean_stringToMessageData(v___x_6115_);
    return v___x_6116_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_6117_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8;
    v___x_6118_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1;
    v___x_6119_ = l_Lean_Name_append(v___x_6118_, v_cls_6117_);
    return v___x_6119_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6121_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15;
    v___x_6122_ = l_Lean_stringToMessageData(v___x_6121_);
    return v___x_6122_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6124_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17;
    v___x_6125_ = l_Lean_stringToMessageData(v___x_6124_);
    return v___x_6125_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(
    mut v_mod_6130_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6131_: u8,
    mut v_hint_6132_: *mut crate::leanh::LeanObject,
    mut v___y_6133_: *mut crate::leanh::LeanObject,
    mut v___y_6134_: *mut crate::leanh::LeanObject,
    mut v___y_6135_: *mut crate::leanh::LeanObject,
    mut v___y_6136_: *mut crate::leanh::LeanObject,
    mut v___y_6137_: *mut crate::leanh::LeanObject,
    mut v___y_6138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_6142_: u8 = 0;
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6165_: u8 = 0;
    let mut v_asyncMode_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6179_: u8 = 0;
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6187_: u8 = 0;
    let mut v_unused_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6190_: u8 = 0;
    let mut v_unused_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: u8 = 0;
    let mut v_options_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6195_: u8 = 0;
    let mut v_inheritedTraceOptions_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: u8 = 0;
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: u8 = 0;
    let mut v___x_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6140_ = lean_st_ref_get(v___y_6138_);
                v_env_6141_ = crate::leanh::lean_ctor_get(v___x_6140_, 0);
                crate::leanh::lean_inc_ref(v_env_6141_);
                crate::leanh::lean_dec(v___x_6140_);
                v_isExporting_6142_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_6141_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_6141_);
                v___x_6143_ = lean_st_ref_get(v___y_6138_);
                v_env_6144_ = crate::leanh::lean_ctor_get(v___x_6143_, 0);
                crate::leanh::lean_inc_ref(v_env_6144_);
                crate::leanh::lean_dec(v___x_6143_);
                v___x_6145_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2);
                crate::leanh::lean_inc(v_mod_6130_);
                v_entry_6146_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_6146_, 0, v_mod_6130_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_6146_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_6142_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_6146_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_6131_,
                );
                v___x_6147_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_6148_ = crate::leanh::lean_box(1);
                v___x_6149_ = crate::leanh::lean_box(0);
                v___x_6192_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_6145_,
                    v___x_6147_,
                    v_env_6144_,
                    v___x_6148_,
                    v___x_6149_,
                );
                v___x_6193_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v___x_6192_, v_entry_6146_);
                crate::leanh::lean_dec(v___x_6192_);
                if v___x_6193_ == 0 {
                    v_options_6194_ = crate::leanh::lean_ctor_get(v___y_6137_, 2);
                    v_hasTrace_6195_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_6194_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6195_ == 0 {
                        crate::leanh::lean_dec(v_hint_6132_);
                        crate::leanh::lean_dec(v_mod_6130_);
                        v___y_6151_ = v___y_6136_;
                        v___y_6152_ = v___y_6138_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_6196_ =
                            crate::leanh::lean_ctor_get(v___y_6137_, 13);
                        v_cls_6197_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8;
                        v___x_6217_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14);
                        v___x_6218_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_6196_,
                            v_options_6194_,
                            v___x_6217_,
                        );
                        if v___x_6218_ == 0 {
                            crate::leanh::lean_dec(v_hint_6132_);
                            crate::leanh::lean_dec(v_mod_6130_);
                            v___y_6151_ = v___y_6136_;
                            v___y_6152_ = v___y_6138_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6219_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16);
                            if v_isExporting_6142_ == 0 {
                                v___x_6228_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__21;
                                v___y_6221_ = v___x_6228_;
                                state = 8;
                                continue;
                            } else {
                                v___x_6229_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__22;
                                v___y_6221_ = v___x_6229_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_6146_, 1);
                    crate::leanh::lean_dec(v_hint_6132_);
                    crate::leanh::lean_dec(v_mod_6130_);
                    v___x_6230_ = crate::leanh::lean_box(0);
                    v___x_6231_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6231_, 0, v___x_6230_);
                    return v___x_6231_;
                }
            }
            1 => {
                v___x_6153_ = lean_st_ref_take(v___y_6152_);
                v_toEnvExtension_6154_ = crate::leanh::lean_ctor_get(v___x_6147_, 0);
                v_env_6155_ = crate::leanh::lean_ctor_get(v___x_6153_, 0);
                v_nextMacroScope_6156_ = crate::leanh::lean_ctor_get(v___x_6153_, 1);
                v_ngen_6157_ = crate::leanh::lean_ctor_get(v___x_6153_, 2);
                v_auxDeclNGen_6158_ = crate::leanh::lean_ctor_get(v___x_6153_, 3);
                v_traceState_6159_ = crate::leanh::lean_ctor_get(v___x_6153_, 4);
                v_messages_6160_ = crate::leanh::lean_ctor_get(v___x_6153_, 6);
                v_infoState_6161_ = crate::leanh::lean_ctor_get(v___x_6153_, 7);
                v_snapshotTasks_6162_ = crate::leanh::lean_ctor_get(v___x_6153_, 8);
                v_isSharedCheck_6190_ = (!crate::leanh::lean_is_exclusive(v___x_6153_)) as u8;
                if v_isSharedCheck_6190_ == 0 {
                    v_unused_6191_ = crate::leanh::lean_ctor_get(v___x_6153_, 5);
                    crate::leanh::lean_dec(v_unused_6191_);
                    v___x_6164_ = v___x_6153_;
                    v_isShared_6165_ = v_isSharedCheck_6190_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6162_);
                    crate::leanh::lean_inc(v_infoState_6161_);
                    crate::leanh::lean_inc(v_messages_6160_);
                    crate::leanh::lean_inc(v_traceState_6159_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6158_);
                    crate::leanh::lean_inc(v_ngen_6157_);
                    crate::leanh::lean_inc(v_nextMacroScope_6156_);
                    crate::leanh::lean_inc(v_env_6155_);
                    crate::leanh::lean_dec(v___x_6153_);
                    v___x_6164_ = crate::leanh::lean_box(0);
                    v_isShared_6165_ = v_isSharedCheck_6190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_6166_ = crate::leanh::lean_ctor_get(v_toEnvExtension_6154_, 2);
                v___x_6167_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_6147_,
                    v_env_6155_,
                    v_entry_6146_,
                    v_asyncMode_6166_,
                    v___x_6149_,
                );
                v___x_6168_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5);
                if v_isShared_6165_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6164_, 5, v___x_6168_);
                    crate::leanh::lean_ctor_set(v___x_6164_, 0, v___x_6167_);
                    v___x_6170_ = v___x_6164_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6189_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 0, v___x_6167_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 1, v_nextMacroScope_6156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 2, v_ngen_6157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 3, v_auxDeclNGen_6158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 4, v_traceState_6159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 5, v___x_6168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 6, v_messages_6160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 7, v_infoState_6161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 8, v_snapshotTasks_6162_);
                    v___x_6170_ = v_reuseFailAlloc_6189_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6171_ = lean_st_ref_set(v___y_6152_, v___x_6170_);
                v___x_6172_ = lean_st_ref_take(v___y_6151_);
                v_mctx_6173_ = crate::leanh::lean_ctor_get(v___x_6172_, 0);
                v_zetaDeltaFVarIds_6174_ = crate::leanh::lean_ctor_get(v___x_6172_, 2);
                v_postponed_6175_ = crate::leanh::lean_ctor_get(v___x_6172_, 3);
                v_diag_6176_ = crate::leanh::lean_ctor_get(v___x_6172_, 4);
                v_isSharedCheck_6187_ = (!crate::leanh::lean_is_exclusive(v___x_6172_)) as u8;
                if v_isSharedCheck_6187_ == 0 {
                    v_unused_6188_ = crate::leanh::lean_ctor_get(v___x_6172_, 1);
                    crate::leanh::lean_dec(v_unused_6188_);
                    v___x_6178_ = v___x_6172_;
                    v_isShared_6179_ = v_isSharedCheck_6187_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_6176_);
                    crate::leanh::lean_inc(v_postponed_6175_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_6174_);
                    crate::leanh::lean_inc(v_mctx_6173_);
                    crate::leanh::lean_dec(v___x_6172_);
                    v___x_6178_ = crate::leanh::lean_box(0);
                    v_isShared_6179_ = v_isSharedCheck_6187_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6180_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6);
                if v_isShared_6179_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6178_, 1, v___x_6180_);
                    v___x_6182_ = v___x_6178_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6186_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6186_, 0, v_mctx_6173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6186_, 1, v___x_6180_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6186_,
                        2,
                        v_zetaDeltaFVarIds_6174_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6186_, 3, v_postponed_6175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6186_, 4, v_diag_6176_);
                    v___x_6182_ = v_reuseFailAlloc_6186_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6183_ = lean_st_ref_set(v___y_6151_, v___x_6182_);
                v___x_6184_ = crate::leanh::lean_box(0);
                v___x_6185_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6185_, 0, v___x_6184_);
                return v___x_6185_;
            }
            6 => {
                v___x_6201_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6201_, 0, v___y_6199_);
                crate::leanh::lean_ctor_set(v___x_6201_, 1, v___y_6200_);
                v___x_6202_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_6197_, v___x_6201_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_);
                if crate::leanh::lean_obj_tag(v___x_6202_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6202_, 1);
                    v___y_6151_ = v___y_6136_;
                    v___y_6152_ = v___y_6138_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_6146_, 1);
                    return v___x_6202_;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref(v___y_6205_);
                v___x_6206_ = l_Lean_stringToMessageData(v___y_6205_);
                v___x_6207_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6207_, 0, v___y_6204_);
                crate::leanh::lean_ctor_set(v___x_6207_, 1, v___x_6206_);
                v___x_6208_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10);
                v___x_6209_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6209_, 0, v___x_6207_);
                crate::leanh::lean_ctor_set(v___x_6209_, 1, v___x_6208_);
                v___x_6210_ = l_Lean_MessageData_ofName(v_mod_6130_);
                v___x_6211_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6211_, 0, v___x_6209_);
                crate::leanh::lean_ctor_set(v___x_6211_, 1, v___x_6210_);
                v___x_6212_ = l_Lean_Name_isAnonymous(v_hint_6132_);
                if v___x_6212_ == 0 {
                    v___x_6213_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12);
                    v___x_6214_ = l_Lean_MessageData_ofName(v_hint_6132_);
                    v___x_6215_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6215_, 0, v___x_6213_);
                    crate::leanh::lean_ctor_set(v___x_6215_, 1, v___x_6214_);
                    v___y_6199_ = v___x_6211_;
                    v___y_6200_ = v___x_6215_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_6132_);
                    v___x_6216_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13);
                    v___y_6199_ = v___x_6211_;
                    v___y_6200_ = v___x_6216_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc_ref(v___y_6221_);
                v___x_6222_ = l_Lean_stringToMessageData(v___y_6221_);
                v___x_6223_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6223_, 0, v___x_6219_);
                crate::leanh::lean_ctor_set(v___x_6223_, 1, v___x_6222_);
                v___x_6224_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18);
                v___x_6225_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6225_, 0, v___x_6223_);
                crate::leanh::lean_ctor_set(v___x_6225_, 1, v___x_6224_);
                if v_isMeta_6131_ == 0 {
                    v___x_6226_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19;
                    v___y_6204_ = v___x_6225_;
                    v___y_6205_ = v___x_6226_;
                    state = 7;
                    continue;
                } else {
                    v___x_6227_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__20;
                    v___y_6204_ = v___x_6225_;
                    v___y_6205_ = v___x_6227_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___boxed(
    mut v_mod_6232_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6233_: *mut crate::leanh::LeanObject,
    mut v_hint_6234_: *mut crate::leanh::LeanObject,
    mut v___y_6235_: *mut crate::leanh::LeanObject,
    mut v___y_6236_: *mut crate::leanh::LeanObject,
    mut v___y_6237_: *mut crate::leanh::LeanObject,
    mut v___y_6238_: *mut crate::leanh::LeanObject,
    mut v___y_6239_: *mut crate::leanh::LeanObject,
    mut v___y_6240_: *mut crate::leanh::LeanObject,
    mut v___y_6241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_6242_: u8 = 0;
    let mut v_res_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_6242_ = (crate::leanh::lean_unbox(v_isMeta_6233_) as u8);
    v_res_6243_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_mod_6232_, v_isMeta_boxed_6242_, v_hint_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_);
    crate::leanh::lean_dec(v___y_6240_);
    crate::leanh::lean_dec_ref(v___y_6239_);
    crate::leanh::lean_dec(v___y_6238_);
    crate::leanh::lean_dec_ref(v___y_6237_);
    crate::leanh::lean_dec(v___y_6236_);
    crate::leanh::lean_dec_ref(v___y_6235_);
    return v_res_6243_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(
    mut v___x_6244_: *mut crate::leanh::LeanObject,
    mut v_declName_6245_: *mut crate::leanh::LeanObject,
    mut v_as_6246_: *mut crate::leanh::LeanObject,
    mut v_sz_6247_: usize,
    mut v_i_6248_: usize,
    mut v_b_6249_: *mut crate::leanh::LeanObject,
    mut v___y_6250_: *mut crate::leanh::LeanObject,
    mut v___y_6251_: *mut crate::leanh::LeanObject,
    mut v___y_6252_: *mut crate::leanh::LeanObject,
    mut v___y_6253_: *mut crate::leanh::LeanObject,
    mut v___y_6254_: *mut crate::leanh::LeanObject,
    mut v___y_6255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6257_: u8 = 0;
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: u8 = 0;
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: usize = 0;
    let mut v___x_6270_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6257_ = lean_usize_dec_lt(v_i_6248_, v_sz_6247_);
                if v___x_6257_ == 0 {
                    crate::leanh::lean_dec(v_declName_6245_);
                    v___x_6258_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6258_, 0, v_b_6249_);
                    return v___x_6258_;
                } else {
                    v___x_6259_ = l_Lean_Environment_header(v___x_6244_);
                    v_modules_6260_ = crate::leanh::lean_ctor_get(v___x_6259_, 3);
                    crate::leanh::lean_inc_ref(v_modules_6260_);
                    crate::leanh::lean_dec_ref(v___x_6259_);
                    v___x_6261_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_6262_ = lean_array_uget_borrowed(v_as_6246_, v_i_6248_);
                    v___x_6263_ = lean_array_get(v___x_6261_, v_modules_6260_, v_a_6262_);
                    crate::leanh::lean_dec_ref(v_modules_6260_);
                    v_toImport_6264_ = crate::leanh::lean_ctor_get(v___x_6263_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_6264_);
                    crate::leanh::lean_dec(v___x_6263_);
                    v_module_6265_ = crate::leanh::lean_ctor_get(v_toImport_6264_, 0);
                    crate::leanh::lean_inc(v_module_6265_);
                    crate::leanh::lean_dec_ref(v_toImport_6264_);
                    v___x_6266_ = 0;
                    crate::leanh::lean_inc(v_declName_6245_);
                    v___x_6267_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_6265_, v___x_6266_, v_declName_6245_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_);
                    if crate::leanh::lean_obj_tag(v___x_6267_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6267_, 1);
                        v___x_6268_ = crate::leanh::lean_box(0);
                        v___x_6269_ = 1usize;
                        v___x_6270_ = lean_usize_add(v_i_6248_, v___x_6269_);
                        v_i_6248_ = v___x_6270_;
                        v_b_6249_ = v___x_6268_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_6245_);
                        return v___x_6267_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5___boxed(
    mut v___x_6272_: *mut crate::leanh::LeanObject,
    mut v_declName_6273_: *mut crate::leanh::LeanObject,
    mut v_as_6274_: *mut crate::leanh::LeanObject,
    mut v_sz_6275_: *mut crate::leanh::LeanObject,
    mut v_i_6276_: *mut crate::leanh::LeanObject,
    mut v_b_6277_: *mut crate::leanh::LeanObject,
    mut v___y_6278_: *mut crate::leanh::LeanObject,
    mut v___y_6279_: *mut crate::leanh::LeanObject,
    mut v___y_6280_: *mut crate::leanh::LeanObject,
    mut v___y_6281_: *mut crate::leanh::LeanObject,
    mut v___y_6282_: *mut crate::leanh::LeanObject,
    mut v___y_6283_: *mut crate::leanh::LeanObject,
    mut v___y_6284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6285_: usize = 0;
    let mut v_i_boxed_6286_: usize = 0;
    let mut v_res_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6285_ = crate::leanh::lean_unbox_usize(v_sz_6275_);
    crate::leanh::lean_dec(v_sz_6275_);
    v_i_boxed_6286_ = crate::leanh::lean_unbox_usize(v_i_6276_);
    crate::leanh::lean_dec(v_i_6276_);
    v_res_6287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v___x_6272_, v_declName_6273_, v_as_6274_, v_sz_boxed_6285_, v_i_boxed_6286_, v_b_6277_, v___y_6278_, v___y_6279_, v___y_6280_, v___y_6281_, v___y_6282_, v___y_6283_);
    crate::leanh::lean_dec(v___y_6283_);
    crate::leanh::lean_dec_ref(v___y_6282_);
    crate::leanh::lean_dec(v___y_6281_);
    crate::leanh::lean_dec_ref(v___y_6280_);
    crate::leanh::lean_dec(v___y_6279_);
    crate::leanh::lean_dec_ref(v___y_6278_);
    crate::leanh::lean_dec_ref(v_as_6274_);
    crate::leanh::lean_dec_ref(v___x_6272_);
    return v_res_6287_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(
    mut v_a_6288_: *mut crate::leanh::LeanObject,
    mut v_x_6289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: u8 = 0;
    let mut v___x_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6289_) == 0 {
                    v___x_6290_ = crate::leanh::lean_box(0);
                    return v___x_6290_;
                } else {
                    v_key_6291_ = crate::leanh::lean_ctor_get(v_x_6289_, 0);
                    v_value_6292_ = crate::leanh::lean_ctor_get(v_x_6289_, 1);
                    v_tail_6293_ = crate::leanh::lean_ctor_get(v_x_6289_, 2);
                    v___x_6294_ = lean_name_eq(v_key_6291_, v_a_6288_);
                    if v___x_6294_ == 0 {
                        v_x_6289_ = v_tail_6293_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_6292_);
                        v___x_6296_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6296_, 0, v_value_6292_);
                        return v___x_6296_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg___boxed(
    mut v_a_6297_: *mut crate::leanh::LeanObject,
    mut v_x_6298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6299_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_6297_, v_x_6298_);
    crate::leanh::lean_dec(v_x_6298_);
    crate::leanh::lean_dec(v_a_6297_);
    return v_res_6299_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___closed__0()
-> u64 {
    let mut v___x_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: u64 = 0;
    v___x_6300_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_6301_ = lean_uint64_of_nat(v___x_6300_);
    return v___x_6301_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(
    mut v_m_6302_: *mut crate::leanh::LeanObject,
    mut v_a_6303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6307_: u64 = 0;
    let mut v___x_6308_: u64 = 0;
    let mut v___x_6309_: u64 = 0;
    let mut v_fold_6310_: u64 = 0;
    let mut v___x_6311_: u64 = 0;
    let mut v___x_6312_: u64 = 0;
    let mut v___x_6313_: u64 = 0;
    let mut v___x_6314_: usize = 0;
    let mut v___x_6315_: usize = 0;
    let mut v___x_6316_: usize = 0;
    let mut v___x_6317_: usize = 0;
    let mut v___x_6318_: usize = 0;
    let mut v___x_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: u64 = 0;
    let mut v_hash_6322_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_6304_ = crate::leanh::lean_ctor_get(v_m_6302_, 1);
                v___x_6305_ = lean_array_get_size(v_buckets_6304_);
                if crate::leanh::lean_obj_tag(v_a_6303_) == 0 {
                    v___x_6321_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___closed__0);
                    v___y_6307_ = v___x_6321_;
                    state = 1;
                    continue;
                } else {
                    v_hash_6322_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_6303_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_6307_ = v_hash_6322_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6308_ = 32u64;
                v___x_6309_ = lean_uint64_shift_right(v___y_6307_, v___x_6308_);
                v_fold_6310_ = lean_uint64_xor(v___y_6307_, v___x_6309_);
                v___x_6311_ = 16u64;
                v___x_6312_ = lean_uint64_shift_right(v_fold_6310_, v___x_6311_);
                v___x_6313_ = lean_uint64_xor(v_fold_6310_, v___x_6312_);
                v___x_6314_ = lean_uint64_to_usize(v___x_6313_);
                v___x_6315_ = lean_usize_of_nat(v___x_6305_);
                v___x_6316_ = 1usize;
                v___x_6317_ = lean_usize_sub(v___x_6315_, v___x_6316_);
                v___x_6318_ = lean_usize_land(v___x_6314_, v___x_6317_);
                v___x_6319_ = lean_array_uget_borrowed(v_buckets_6304_, v___x_6318_);
                v___x_6320_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_6303_, v___x_6319_);
                return v___x_6320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___boxed(
    mut v_m_6323_: *mut crate::leanh::LeanObject,
    mut v_a_6324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6325_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_6323_, v_a_6324_);
    crate::leanh::lean_dec(v_a_6324_);
    crate::leanh::lean_dec_ref(v_m_6323_);
    return v_res_6325_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6328_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1;
    v___x_6329_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0;
    v___x_6330_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6329_,
        v___x_6328_,
    );
    return v___x_6330_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(
    mut v_declName_6333_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6334_: u8,
    mut v___y_6335_: *mut crate::leanh::LeanObject,
    mut v___y_6336_: *mut crate::leanh::LeanObject,
    mut v___y_6337_: *mut crate::leanh::LeanObject,
    mut v___y_6338_: *mut crate::leanh::LeanObject,
    mut v___y_6339_: *mut crate::leanh::LeanObject,
    mut v___y_6340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6350_: usize = 0;
    let mut v___x_6351_: usize = 0;
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6355_: u8 = 0;
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6359_: u8 = 0;
    let mut v_unused_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: u8 = 0;
    let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6372_: u8 = 0;
    let mut v_toImport_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: u8 = 0;
    let mut v___x_6384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6342_ = lean_st_ref_get(v___y_6340_);
                v_env_6346_ = crate::leanh::lean_ctor_get(v___x_6342_, 0);
                crate::leanh::lean_inc_ref(v_env_6346_);
                crate::leanh::lean_dec(v___x_6342_);
                v___x_6361_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6346_, v_declName_6333_);
                if crate::leanh::lean_obj_tag(v___x_6361_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_6346_);
                    crate::leanh::lean_dec(v_declName_6333_);
                    state = 1;
                    continue;
                } else {
                    v_val_6362_ = crate::leanh::lean_ctor_get(v___x_6361_, 0);
                    crate::leanh::lean_inc(v_val_6362_);
                    crate::leanh::lean_dec_ref_known(v___x_6361_, 1);
                    v___x_6363_ = l_Lean_Environment_header(v_env_6346_);
                    v_modules_6364_ = crate::leanh::lean_ctor_get(v___x_6363_, 3);
                    crate::leanh::lean_inc_ref(v_modules_6364_);
                    crate::leanh::lean_dec_ref(v___x_6363_);
                    v___x_6365_ = lean_array_get_size(v_modules_6364_);
                    v___x_6366_ = lean_nat_dec_lt(v_val_6362_, v___x_6365_);
                    if v___x_6366_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_6364_);
                        crate::leanh::lean_dec(v_val_6362_);
                        crate::leanh::lean_dec_ref(v_env_6346_);
                        crate::leanh::lean_dec(v_declName_6333_);
                        state = 1;
                        continue;
                    } else {
                        v___x_6367_ = lean_st_ref_get(v___y_6340_);
                        v_env_6368_ = crate::leanh::lean_ctor_get(v___x_6367_, 0);
                        crate::leanh::lean_inc_ref(v_env_6368_);
                        crate::leanh::lean_dec(v___x_6367_);
                        v___x_6369_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2);
                        v___x_6370_ = lean_array_fget(v_modules_6364_, v_val_6362_);
                        crate::leanh::lean_dec(v_val_6362_);
                        crate::leanh::lean_dec_ref(v_modules_6364_);
                        if v_isMeta_6334_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_6368_);
                            v___y_6372_ = v_isMeta_6334_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_6333_);
                            v___x_6383_ = l_Lean_isMarkedMeta(v_env_6368_, v_declName_6333_);
                            if v___x_6383_ == 0 {
                                v___y_6372_ = v_isMeta_6334_;
                                state = 5;
                                continue;
                            } else {
                                v___x_6384_ = 0;
                                v___y_6372_ = v___x_6384_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6344_ = crate::leanh::lean_box(0);
                v___x_6345_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6345_, 0, v___x_6344_);
                return v___x_6345_;
            }
            2 => {
                v___x_6349_ = crate::leanh::lean_box(0);
                v_sz_6350_ = lean_array_size(v___y_6348_);
                v___x_6351_ = 0usize;
                v___x_6352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v_env_6346_, v_declName_6333_, v___y_6348_, v_sz_6350_, v___x_6351_, v___x_6349_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_);
                crate::leanh::lean_dec_ref(v___y_6348_);
                crate::leanh::lean_dec_ref(v_env_6346_);
                if crate::leanh::lean_obj_tag(v___x_6352_) == 0 {
                    v_isSharedCheck_6359_ = (!crate::leanh::lean_is_exclusive(v___x_6352_)) as u8;
                    if v_isSharedCheck_6359_ == 0 {
                        v_unused_6360_ = crate::leanh::lean_ctor_get(v___x_6352_, 0);
                        crate::leanh::lean_dec(v_unused_6360_);
                        v___x_6354_ = v___x_6352_;
                        v_isShared_6355_ = v_isSharedCheck_6359_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6352_);
                        v___x_6354_ = crate::leanh::lean_box(0);
                        v_isShared_6355_ = v_isSharedCheck_6359_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_6352_;
                }
            }
            3 => {
                if v_isShared_6355_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6354_, 0, v___x_6349_);
                    v___x_6357_ = v___x_6354_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6358_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6358_, 0, v___x_6349_);
                    v___x_6357_ = v_reuseFailAlloc_6358_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6357_;
            }
            5 => {
                v_toImport_6373_ = crate::leanh::lean_ctor_get(v___x_6370_, 0);
                crate::leanh::lean_inc_ref(v_toImport_6373_);
                crate::leanh::lean_dec(v___x_6370_);
                v_module_6374_ = crate::leanh::lean_ctor_get(v_toImport_6373_, 0);
                crate::leanh::lean_inc(v_module_6374_);
                crate::leanh::lean_dec_ref(v_toImport_6373_);
                crate::leanh::lean_inc(v_declName_6333_);
                v___x_6375_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_6374_, v___y_6372_, v_declName_6333_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_);
                if crate::leanh::lean_obj_tag(v___x_6375_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6375_, 1);
                    v___x_6376_ = l_Lean_indirectModUseExt;
                    v___x_6377_ = crate::leanh::lean_box(1);
                    v___x_6378_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_6346_);
                    v___x_6379_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_6369_,
                        v___x_6376_,
                        v_env_6346_,
                        v___x_6377_,
                        v___x_6378_,
                    );
                    v___x_6380_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v___x_6379_, v_declName_6333_);
                    crate::leanh::lean_dec(v___x_6379_);
                    if crate::leanh::lean_obj_tag(v___x_6380_) == 0 {
                        v___x_6381_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__3;
                        v___y_6348_ = v___x_6381_;
                        state = 2;
                        continue;
                    } else {
                        v_val_6382_ = crate::leanh::lean_ctor_get(v___x_6380_, 0);
                        crate::leanh::lean_inc(v_val_6382_);
                        crate::leanh::lean_dec_ref_known(v___x_6380_, 1);
                        v___y_6348_ = v_val_6382_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_6346_);
                    crate::leanh::lean_dec(v_declName_6333_);
                    return v___x_6375_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___boxed(
    mut v_declName_6385_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6386_: *mut crate::leanh::LeanObject,
    mut v___y_6387_: *mut crate::leanh::LeanObject,
    mut v___y_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
    mut v___y_6390_: *mut crate::leanh::LeanObject,
    mut v___y_6391_: *mut crate::leanh::LeanObject,
    mut v___y_6392_: *mut crate::leanh::LeanObject,
    mut v___y_6393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_6394_: u8 = 0;
    let mut v_res_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_6394_ = (crate::leanh::lean_unbox(v_isMeta_6386_) as u8);
    v_res_6395_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_declName_6385_, v_isMeta_boxed_6394_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_, v___y_6391_, v___y_6392_);
    crate::leanh::lean_dec(v___y_6392_);
    crate::leanh::lean_dec_ref(v___y_6391_);
    crate::leanh::lean_dec(v___y_6390_);
    crate::leanh::lean_dec_ref(v___y_6389_);
    crate::leanh::lean_dec(v___y_6388_);
    crate::leanh::lean_dec_ref(v___y_6387_);
    return v_res_6395_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(
    mut v_as_x27_6396_: *mut crate::leanh::LeanObject,
    mut v_b_6397_: *mut crate::leanh::LeanObject,
    mut v___y_6398_: *mut crate::leanh::LeanObject,
    mut v___y_6399_: *mut crate::leanh::LeanObject,
    mut v___y_6400_: *mut crate::leanh::LeanObject,
    mut v___y_6401_: *mut crate::leanh::LeanObject,
    mut v___y_6402_: *mut crate::leanh::LeanObject,
    mut v___y_6403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: u8 = 0;
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_6396_) == 0 {
                    v___x_6405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6405_, 0, v_b_6397_);
                    return v___x_6405_;
                } else {
                    v_head_6406_ = crate::leanh::lean_ctor_get(v_as_x27_6396_, 0);
                    v_tail_6407_ = crate::leanh::lean_ctor_get(v_as_x27_6396_, 1);
                    v___x_6408_ = 1;
                    crate::leanh::lean_inc(v_head_6406_);
                    v___x_6409_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_head_6406_, v___x_6408_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_, v___y_6403_);
                    if crate::leanh::lean_obj_tag(v___x_6409_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6409_, 1);
                        v___x_6410_ = crate::leanh::lean_box(0);
                        v_as_x27_6396_ = v_tail_6407_;
                        v_b_6397_ = v___x_6410_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6409_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg___boxed(
    mut v_as_x27_6412_: *mut crate::leanh::LeanObject,
    mut v_b_6413_: *mut crate::leanh::LeanObject,
    mut v___y_6414_: *mut crate::leanh::LeanObject,
    mut v___y_6415_: *mut crate::leanh::LeanObject,
    mut v___y_6416_: *mut crate::leanh::LeanObject,
    mut v___y_6417_: *mut crate::leanh::LeanObject,
    mut v___y_6418_: *mut crate::leanh::LeanObject,
    mut v___y_6419_: *mut crate::leanh::LeanObject,
    mut v___y_6420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6421_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_6412_, v_b_6413_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_);
    crate::leanh::lean_dec(v___y_6419_);
    crate::leanh::lean_dec_ref(v___y_6418_);
    crate::leanh::lean_dec(v___y_6417_);
    crate::leanh::lean_dec_ref(v___y_6416_);
    crate::leanh::lean_dec(v___y_6415_);
    crate::leanh::lean_dec_ref(v___y_6414_);
    crate::leanh::lean_dec(v_as_x27_6412_);
    return v_res_6421_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(
    mut v_env_6422_: *mut crate::leanh::LeanObject,
    mut v_options_6423_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_6424_: *mut crate::leanh::LeanObject,
    mut v_openDecls_6425_: *mut crate::leanh::LeanObject,
    mut v_n_6426_: *mut crate::leanh::LeanObject,
    mut v___y_6427_: *mut crate::leanh::LeanObject,
    mut v___y_6428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6429_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_6422_,
        v_options_6423_,
        v_currNamespace_6424_,
        v_openDecls_6425_,
        v_n_6426_,
    );
    v___x_6430_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6430_, 0, v___x_6429_);
    crate::leanh::lean_ctor_set(v___x_6430_, 1, v___y_6428_);
    return v___x_6430_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed(
    mut v_env_6431_: *mut crate::leanh::LeanObject,
    mut v_options_6432_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_6433_: *mut crate::leanh::LeanObject,
    mut v_openDecls_6434_: *mut crate::leanh::LeanObject,
    mut v_n_6435_: *mut crate::leanh::LeanObject,
    mut v___y_6436_: *mut crate::leanh::LeanObject,
    mut v___y_6437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6438_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(v_env_6431_, v_options_6432_, v_currNamespace_6433_, v_openDecls_6434_, v_n_6435_, v___y_6436_, v___y_6437_);
    crate::leanh::lean_dec_ref(v___y_6436_);
    crate::leanh::lean_dec_ref(v_options_6432_);
    return v_res_6438_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(
    mut v_env_6439_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_6440_: *mut crate::leanh::LeanObject,
    mut v_openDecls_6441_: *mut crate::leanh::LeanObject,
    mut v_n_6442_: *mut crate::leanh::LeanObject,
    mut v___y_6443_: *mut crate::leanh::LeanObject,
    mut v___y_6444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6445_ = l_Lean_ResolveName_resolveNamespace(
        v_env_6439_,
        v_currNamespace_6440_,
        v_openDecls_6441_,
        v_n_6442_,
    );
    v___x_6446_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6446_, 0, v___x_6445_);
    crate::leanh::lean_ctor_set(v___x_6446_, 1, v___y_6444_);
    return v___x_6446_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed(
    mut v_env_6447_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_6448_: *mut crate::leanh::LeanObject,
    mut v_openDecls_6449_: *mut crate::leanh::LeanObject,
    mut v_n_6450_: *mut crate::leanh::LeanObject,
    mut v___y_6451_: *mut crate::leanh::LeanObject,
    mut v___y_6452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6453_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(v_env_6447_, v_currNamespace_6448_, v_openDecls_6449_, v_n_6450_, v___y_6451_, v___y_6452_);
    crate::leanh::lean_dec_ref(v___y_6451_);
    return v_res_6453_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6454_ = crate::leanh::lean_box(0);
    v___x_6455_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_6456_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6456_, 0, v___x_6455_);
    crate::leanh::lean_ctor_set(v___x_6456_, 1, v___x_6454_);
    return v___x_6456_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6458_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0);
    v___x_6459_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6459_, 0, v___x_6458_);
    return v___x_6459_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___boxed(
    mut v___y_6460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6461_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
    return v_res_6461_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6467_ = l_Lean_maxRecDepthErrorMessage;
    v___x_6468_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6468_, 0, v___x_6467_);
    return v___x_6468_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6469_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3);
    v___x_6470_ = l_Lean_MessageData_ofFormat(v___x_6469_);
    return v___x_6470_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6471_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4);
    v___x_6472_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2;
    v___x_6473_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6473_, 0, v___x_6472_);
    crate::leanh::lean_ctor_set(v___x_6473_, 1, v___x_6471_);
    return v___x_6473_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(
    mut v_ref_6474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6476_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5);
    v___x_6477_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6477_, 0, v_ref_6474_);
    crate::leanh::lean_ctor_set(v___x_6477_, 1, v___x_6476_);
    v___x_6478_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6478_, 0, v___x_6477_);
    return v___x_6478_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___boxed(
    mut v_ref_6479_: *mut crate::leanh::LeanObject,
    mut v___y_6480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6481_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_6479_);
    return v_res_6481_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(
    mut v_x_6483_: *mut crate::leanh::LeanObject,
    mut v___y_6484_: *mut crate::leanh::LeanObject,
    mut v___y_6485_: *mut crate::leanh::LeanObject,
    mut v___y_6486_: *mut crate::leanh::LeanObject,
    mut v___y_6487_: *mut crate::leanh::LeanObject,
    mut v___y_6488_: *mut crate::leanh::LeanObject,
    mut v___y_6489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6531_: u8 = 0;
    let mut v___x_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6539_: u8 = 0;
    let mut v___x_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6543_: u8 = 0;
    let mut v_unused_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6548_: u8 = 0;
    let mut v___x_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6552_: u8 = 0;
    let mut v_reuseFailAlloc_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6554_: u8 = 0;
    let mut v_unused_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6559_: u8 = 0;
    let mut v___x_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6563_: u8 = 0;
    let mut v_a_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: u8 = 0;
    let mut v___x_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6491_ = lean_st_ref_get(v___y_6489_);
                v_env_6492_ = crate::leanh::lean_ctor_get(v___x_6491_, 0);
                crate::leanh::lean_inc_ref_n(v_env_6492_, 4);
                crate::leanh::lean_dec(v___x_6491_);
                v_options_6493_ = crate::leanh::lean_ctor_get(v___y_6488_, 2);
                v_currRecDepth_6494_ = crate::leanh::lean_ctor_get(v___y_6488_, 3);
                v_maxRecDepth_6495_ = crate::leanh::lean_ctor_get(v___y_6488_, 4);
                v_ref_6496_ = crate::leanh::lean_ctor_get(v___y_6488_, 5);
                v_currNamespace_6497_ = crate::leanh::lean_ctor_get(v___y_6488_, 6);
                v_openDecls_6498_ = crate::leanh::lean_ctor_get(v___y_6488_, 7);
                v_quotContext_6499_ = crate::leanh::lean_ctor_get(v___y_6488_, 10);
                v_currMacroScope_6500_ = crate::leanh::lean_ctor_get(v___y_6488_, 11);
                v___x_6501_ = lean_st_ref_get(v___y_6489_);
                v_nextMacroScope_6502_ = crate::leanh::lean_ctor_get(v___x_6501_, 1);
                crate::leanh::lean_inc(v_nextMacroScope_6502_);
                crate::leanh::lean_dec(v___x_6501_);
                v___f_6503_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                crate::leanh::lean_closure_set(v___f_6503_, 0, v_env_6492_);
                v___f_6504_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                crate::leanh::lean_closure_set(v___f_6504_, 0, v_env_6492_);
                crate::leanh::lean_inc_n(v_openDecls_6498_, 2);
                crate::leanh::lean_inc_n(v_currNamespace_6497_, 3);
                v___f_6505_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 3);
                crate::leanh::lean_closure_set(v___f_6505_, 0, v_env_6492_);
                crate::leanh::lean_closure_set(v___f_6505_, 1, v_currNamespace_6497_);
                crate::leanh::lean_closure_set(v___f_6505_, 2, v_openDecls_6498_);
                v___f_6506_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 1);
                crate::leanh::lean_closure_set(v___f_6506_, 0, v_currNamespace_6497_);
                crate::leanh::lean_inc_ref(v_options_6493_);
                v___f_6507_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                crate::leanh::lean_closure_set(v___f_6507_, 0, v_env_6492_);
                crate::leanh::lean_closure_set(v___f_6507_, 1, v_options_6493_);
                crate::leanh::lean_closure_set(v___f_6507_, 2, v_currNamespace_6497_);
                crate::leanh::lean_closure_set(v___f_6507_, 3, v_openDecls_6498_);
                v_methods_6508_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v_methods_6508_, 0, v___f_6503_);
                crate::leanh::lean_ctor_set(v_methods_6508_, 1, v___f_6506_);
                crate::leanh::lean_ctor_set(v_methods_6508_, 2, v___f_6504_);
                crate::leanh::lean_ctor_set(v_methods_6508_, 3, v___f_6505_);
                crate::leanh::lean_ctor_set(v_methods_6508_, 4, v___f_6507_);
                crate::leanh::lean_inc(v_ref_6496_);
                crate::leanh::lean_inc(v_maxRecDepth_6495_);
                crate::leanh::lean_inc(v_currRecDepth_6494_);
                crate::leanh::lean_inc(v_currMacroScope_6500_);
                crate::leanh::lean_inc(v_quotContext_6499_);
                v___x_6509_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6509_, 0, v_methods_6508_);
                crate::leanh::lean_ctor_set(v___x_6509_, 1, v_quotContext_6499_);
                crate::leanh::lean_ctor_set(v___x_6509_, 2, v_currMacroScope_6500_);
                crate::leanh::lean_ctor_set(v___x_6509_, 3, v_currRecDepth_6494_);
                crate::leanh::lean_ctor_set(v___x_6509_, 4, v_maxRecDepth_6495_);
                crate::leanh::lean_ctor_set(v___x_6509_, 5, v_ref_6496_);
                v___x_6510_ = crate::leanh::lean_box(0);
                v___x_6511_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6511_, 0, v_nextMacroScope_6502_);
                crate::leanh::lean_ctor_set(v___x_6511_, 1, v___x_6510_);
                crate::leanh::lean_ctor_set(v___x_6511_, 2, v___x_6510_);
                v___x_6512_ = crate::leanh::lean_apply_2(v_x_6483_, v___x_6509_, v___x_6511_);
                if crate::leanh::lean_obj_tag(v___x_6512_) == 0 {
                    v_a_6513_ = crate::leanh::lean_ctor_get(v___x_6512_, 1);
                    crate::leanh::lean_inc(v_a_6513_);
                    v_a_6514_ = crate::leanh::lean_ctor_get(v___x_6512_, 0);
                    crate::leanh::lean_inc(v_a_6514_);
                    crate::leanh::lean_dec_ref_known(v___x_6512_, 2);
                    v_macroScope_6515_ = crate::leanh::lean_ctor_get(v_a_6513_, 0);
                    crate::leanh::lean_inc(v_macroScope_6515_);
                    v_traceMsgs_6516_ = crate::leanh::lean_ctor_get(v_a_6513_, 1);
                    crate::leanh::lean_inc(v_traceMsgs_6516_);
                    v_expandedMacroDecls_6517_ = crate::leanh::lean_ctor_get(v_a_6513_, 2);
                    crate::leanh::lean_inc(v_expandedMacroDecls_6517_);
                    crate::leanh::lean_dec(v_a_6513_);
                    v___x_6518_ = crate::leanh::lean_box(0);
                    v___x_6519_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_expandedMacroDecls_6517_, v___x_6518_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_);
                    crate::leanh::lean_dec(v_expandedMacroDecls_6517_);
                    if crate::leanh::lean_obj_tag(v___x_6519_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6519_, 1);
                        v___x_6520_ = lean_st_ref_take(v___y_6489_);
                        v_env_6521_ = crate::leanh::lean_ctor_get(v___x_6520_, 0);
                        v_ngen_6522_ = crate::leanh::lean_ctor_get(v___x_6520_, 2);
                        v_auxDeclNGen_6523_ = crate::leanh::lean_ctor_get(v___x_6520_, 3);
                        v_traceState_6524_ = crate::leanh::lean_ctor_get(v___x_6520_, 4);
                        v_cache_6525_ = crate::leanh::lean_ctor_get(v___x_6520_, 5);
                        v_messages_6526_ = crate::leanh::lean_ctor_get(v___x_6520_, 6);
                        v_infoState_6527_ = crate::leanh::lean_ctor_get(v___x_6520_, 7);
                        v_snapshotTasks_6528_ = crate::leanh::lean_ctor_get(v___x_6520_, 8);
                        v_isSharedCheck_6554_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6520_)) as u8;
                        if v_isSharedCheck_6554_ == 0 {
                            v_unused_6555_ = crate::leanh::lean_ctor_get(v___x_6520_, 1);
                            crate::leanh::lean_dec(v_unused_6555_);
                            v___x_6530_ = v___x_6520_;
                            v_isShared_6531_ = v_isSharedCheck_6554_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_6528_);
                            crate::leanh::lean_inc(v_infoState_6527_);
                            crate::leanh::lean_inc(v_messages_6526_);
                            crate::leanh::lean_inc(v_cache_6525_);
                            crate::leanh::lean_inc(v_traceState_6524_);
                            crate::leanh::lean_inc(v_auxDeclNGen_6523_);
                            crate::leanh::lean_inc(v_ngen_6522_);
                            crate::leanh::lean_inc(v_env_6521_);
                            crate::leanh::lean_dec(v___x_6520_);
                            v___x_6530_ = crate::leanh::lean_box(0);
                            v_isShared_6531_ = v_isSharedCheck_6554_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_traceMsgs_6516_);
                        crate::leanh::lean_dec(v_macroScope_6515_);
                        crate::leanh::lean_dec(v_a_6514_);
                        v_a_6556_ = crate::leanh::lean_ctor_get(v___x_6519_, 0);
                        v_isSharedCheck_6563_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6519_)) as u8;
                        if v_isSharedCheck_6563_ == 0 {
                            v___x_6558_ = v___x_6519_;
                            v_isShared_6559_ = v_isSharedCheck_6563_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6556_);
                            crate::leanh::lean_dec(v___x_6519_);
                            v___x_6558_ = crate::leanh::lean_box(0);
                            v_isShared_6559_ = v_isSharedCheck_6563_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_6564_ = crate::leanh::lean_ctor_get(v___x_6512_, 0);
                    crate::leanh::lean_inc(v_a_6564_);
                    crate::leanh::lean_dec_ref_known(v___x_6512_, 2);
                    if crate::leanh::lean_obj_tag(v_a_6564_) == 0 {
                        v_a_6565_ = crate::leanh::lean_ctor_get(v_a_6564_, 0);
                        crate::leanh::lean_inc(v_a_6565_);
                        v_a_6566_ = crate::leanh::lean_ctor_get(v_a_6564_, 1);
                        crate::leanh::lean_inc_ref(v_a_6566_);
                        crate::leanh::lean_dec_ref_known(v_a_6564_, 2);
                        v___x_6567_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0;
                        v___x_6568_ = lean_string_dec_eq(v_a_6566_, v___x_6567_);
                        if v___x_6568_ == 0 {
                            v___x_6569_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6569_, 0, v_a_6566_);
                            v___x_6570_ = l_Lean_MessageData_ofFormat(v___x_6569_);
                            v___x_6571_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_a_6565_, v___x_6570_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_);
                            crate::leanh::lean_dec(v_a_6565_);
                            return v___x_6571_;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_6566_);
                            v___x_6572_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_a_6565_);
                            return v___x_6572_;
                        }
                    } else {
                        v___x_6573_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
                        return v___x_6573_;
                    }
                }
            }
            1 => {
                if v_isShared_6531_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6530_, 1, v_macroScope_6515_);
                    v___x_6533_ = v___x_6530_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6553_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6553_, 0, v_env_6521_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6553_, 1, v_macroScope_6515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6553_, 2, v_ngen_6522_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6553_, 3, v_auxDeclNGen_6523_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6553_, 4, v_traceState_6524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6553_, 5, v_cache_6525_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6553_, 6, v_messages_6526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6553_, 7, v_infoState_6527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6553_, 8, v_snapshotTasks_6528_);
                    v___x_6533_ = v_reuseFailAlloc_6553_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6534_ = lean_st_ref_set(v___y_6489_, v___x_6533_);
                v___x_6535_ = l_List_reverse___redArg(v_traceMsgs_6516_);
                v___x_6536_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v___x_6535_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_);
                if crate::leanh::lean_obj_tag(v___x_6536_) == 0 {
                    v_isSharedCheck_6543_ = (!crate::leanh::lean_is_exclusive(v___x_6536_)) as u8;
                    if v_isSharedCheck_6543_ == 0 {
                        v_unused_6544_ = crate::leanh::lean_ctor_get(v___x_6536_, 0);
                        crate::leanh::lean_dec(v_unused_6544_);
                        v___x_6538_ = v___x_6536_;
                        v_isShared_6539_ = v_isSharedCheck_6543_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6536_);
                        v___x_6538_ = crate::leanh::lean_box(0);
                        v_isShared_6539_ = v_isSharedCheck_6543_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6514_);
                    v_a_6545_ = crate::leanh::lean_ctor_get(v___x_6536_, 0);
                    v_isSharedCheck_6552_ = (!crate::leanh::lean_is_exclusive(v___x_6536_)) as u8;
                    if v_isSharedCheck_6552_ == 0 {
                        v___x_6547_ = v___x_6536_;
                        v_isShared_6548_ = v_isSharedCheck_6552_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6545_);
                        crate::leanh::lean_dec(v___x_6536_);
                        v___x_6547_ = crate::leanh::lean_box(0);
                        v_isShared_6548_ = v_isSharedCheck_6552_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6539_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6538_, 0, v_a_6514_);
                    v___x_6541_ = v___x_6538_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6542_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6542_, 0, v_a_6514_);
                    v___x_6541_ = v_reuseFailAlloc_6542_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6541_;
            }
            5 => {
                if v_isShared_6548_ == 0 {
                    v___x_6550_ = v___x_6547_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6551_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6551_, 0, v_a_6545_);
                    v___x_6550_ = v_reuseFailAlloc_6551_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6550_;
            }
            7 => {
                if v_isShared_6559_ == 0 {
                    v___x_6561_ = v___x_6558_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6562_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6562_, 0, v_a_6556_);
                    v___x_6561_ = v_reuseFailAlloc_6562_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6561_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___boxed(
    mut v_x_6574_: *mut crate::leanh::LeanObject,
    mut v___y_6575_: *mut crate::leanh::LeanObject,
    mut v___y_6576_: *mut crate::leanh::LeanObject,
    mut v___y_6577_: *mut crate::leanh::LeanObject,
    mut v___y_6578_: *mut crate::leanh::LeanObject,
    mut v___y_6579_: *mut crate::leanh::LeanObject,
    mut v___y_6580_: *mut crate::leanh::LeanObject,
    mut v___y_6581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6582_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_6574_, v___y_6575_, v___y_6576_, v___y_6577_, v___y_6578_, v___y_6579_, v___y_6580_);
    crate::leanh::lean_dec(v___y_6580_);
    crate::leanh::lean_dec_ref(v___y_6579_);
    crate::leanh::lean_dec(v___y_6578_);
    crate::leanh::lean_dec_ref(v___y_6577_);
    crate::leanh::lean_dec(v___y_6576_);
    crate::leanh::lean_dec_ref(v___y_6575_);
    return v_res_6582_;
}
pub unsafe fn l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(
    mut v_pre_6583_: *mut crate::leanh::LeanObject,
    mut v_binders_6584_: *mut crate::leanh::LeanObject,
    mut v_type_6585_: *mut crate::leanh::LeanObject,
    mut v_a_6586_: *mut crate::leanh::LeanObject,
    mut v_a_6587_: *mut crate::leanh::LeanObject,
    mut v_a_6588_: *mut crate::leanh::LeanObject,
    mut v_a_6589_: *mut crate::leanh::LeanObject,
    mut v_a_6590_: *mut crate::leanh::LeanObject,
    mut v_a_6591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6603_: u8 = 0;
    let mut v___x_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: u8 = 0;
    let mut v___x_6608_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_pre_6583_);
                v___f_6598_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed
                        as *mut core::ffi::c_void,
                    10,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_6598_, 0, v_type_6585_);
                crate::leanh::lean_closure_set(v___f_6598_, 1, v_pre_6583_);
                v___x_6599_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_elabBinders___boxed as *mut core::ffi::c_void,
                    10,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_6599_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_6599_, 1, v_binders_6584_);
                crate::leanh::lean_closure_set(v___x_6599_, 2, v___f_6598_);
                v___x_6600_ = l_Lean_Elab_Term_withAutoBoundImplicit___redArg(
                    v___x_6599_,
                    v_a_6586_,
                    v_a_6587_,
                    v_a_6588_,
                    v_a_6589_,
                    v_a_6590_,
                    v_a_6591_,
                );
                if crate::leanh::lean_obj_tag(v___x_6600_) == 0 {
                    crate::leanh::lean_dec_ref(v_pre_6583_);
                    v___y_6594_ = v___x_6600_;
                    state = 1;
                    continue;
                } else {
                    v_a_6601_ = crate::leanh::lean_ctor_get(v___x_6600_, 0);
                    crate::leanh::lean_inc(v_a_6601_);
                    v___x_6607_ = l_Lean_Exception_isInterrupt(v_a_6601_);
                    if v___x_6607_ == 0 {
                        v___x_6608_ = l_Lean_Exception_isRuntime(v_a_6601_);
                        v___y_6603_ = v___x_6608_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_6601_);
                        v___y_6603_ = v___x_6607_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_6594_) == 0 {
                    v_a_6595_ = crate::leanh::lean_ctor_get(v___y_6594_, 0);
                    crate::leanh::lean_inc(v_a_6595_);
                    crate::leanh::lean_dec_ref_known(v___y_6594_, 1);
                    v___x_6596_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_mkUnusedBaseName___boxed as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_6596_, 0, v_a_6595_);
                    v___x_6597_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v___x_6596_, v_a_6586_, v_a_6587_, v_a_6588_, v_a_6589_, v_a_6590_, v_a_6591_);
                    return v___x_6597_;
                } else {
                    return v___y_6594_;
                }
            }
            2 => {
                if v___y_6603_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6600_, 1);
                    v___x_6604_ = crate::leanh::lean_box(0);
                    v___x_6605_ = l_Lean_Name_str___override(v___x_6604_, v_pre_6583_);
                    v___x_6606_ = l_Lean_Core_mkFreshUserName(v___x_6605_, v_a_6590_, v_a_6591_);
                    v___y_6594_ = v___x_6606_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_pre_6583_);
                    v___y_6594_ = v___x_6600_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___boxed(
    mut v_pre_6609_: *mut crate::leanh::LeanObject,
    mut v_binders_6610_: *mut crate::leanh::LeanObject,
    mut v_type_6611_: *mut crate::leanh::LeanObject,
    mut v_a_6612_: *mut crate::leanh::LeanObject,
    mut v_a_6613_: *mut crate::leanh::LeanObject,
    mut v_a_6614_: *mut crate::leanh::LeanObject,
    mut v_a_6615_: *mut crate::leanh::LeanObject,
    mut v_a_6616_: *mut crate::leanh::LeanObject,
    mut v_a_6617_: *mut crate::leanh::LeanObject,
    mut v_a_6618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6619_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(
        v_pre_6609_,
        v_binders_6610_,
        v_type_6611_,
        v_a_6612_,
        v_a_6613_,
        v_a_6614_,
        v_a_6615_,
        v_a_6616_,
        v_a_6617_,
    );
    crate::leanh::lean_dec(v_a_6617_);
    crate::leanh::lean_dec_ref(v_a_6616_);
    crate::leanh::lean_dec(v_a_6615_);
    crate::leanh::lean_dec_ref(v_a_6614_);
    crate::leanh::lean_dec(v_a_6613_);
    crate::leanh::lean_dec_ref(v_a_6612_);
    return v_res_6619_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(
    mut v_00_u03b1_6620_: *mut crate::leanh::LeanObject,
    mut v_x_6621_: *mut crate::leanh::LeanObject,
    mut v___y_6622_: *mut crate::leanh::LeanObject,
    mut v___y_6623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6624_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_6621_, v___y_6623_);
    return v___x_6624_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___boxed(
    mut v_00_u03b1_6625_: *mut crate::leanh::LeanObject,
    mut v_x_6626_: *mut crate::leanh::LeanObject,
    mut v___y_6627_: *mut crate::leanh::LeanObject,
    mut v___y_6628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6629_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(v_00_u03b1_6625_, v_x_6626_, v___y_6627_, v___y_6628_);
    crate::leanh::lean_dec_ref(v___y_6627_);
    crate::leanh::lean_dec_ref(v_x_6626_);
    return v_res_6629_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(
    mut v_00_u03b1_6630_: *mut crate::leanh::LeanObject,
    mut v_ref_6631_: *mut crate::leanh::LeanObject,
    mut v___y_6632_: *mut crate::leanh::LeanObject,
    mut v___y_6633_: *mut crate::leanh::LeanObject,
    mut v___y_6634_: *mut crate::leanh::LeanObject,
    mut v___y_6635_: *mut crate::leanh::LeanObject,
    mut v___y_6636_: *mut crate::leanh::LeanObject,
    mut v___y_6637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6639_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_6631_);
    return v___x_6639_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___boxed(
    mut v_00_u03b1_6640_: *mut crate::leanh::LeanObject,
    mut v_ref_6641_: *mut crate::leanh::LeanObject,
    mut v___y_6642_: *mut crate::leanh::LeanObject,
    mut v___y_6643_: *mut crate::leanh::LeanObject,
    mut v___y_6644_: *mut crate::leanh::LeanObject,
    mut v___y_6645_: *mut crate::leanh::LeanObject,
    mut v___y_6646_: *mut crate::leanh::LeanObject,
    mut v___y_6647_: *mut crate::leanh::LeanObject,
    mut v___y_6648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6649_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(v_00_u03b1_6640_, v_ref_6641_, v___y_6642_, v___y_6643_, v___y_6644_, v___y_6645_, v___y_6646_, v___y_6647_);
    crate::leanh::lean_dec(v___y_6647_);
    crate::leanh::lean_dec_ref(v___y_6646_);
    crate::leanh::lean_dec(v___y_6645_);
    crate::leanh::lean_dec_ref(v___y_6644_);
    crate::leanh::lean_dec(v___y_6643_);
    crate::leanh::lean_dec_ref(v___y_6642_);
    return v_res_6649_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(
    mut v_00_u03b1_6650_: *mut crate::leanh::LeanObject,
    mut v___y_6651_: *mut crate::leanh::LeanObject,
    mut v___y_6652_: *mut crate::leanh::LeanObject,
    mut v___y_6653_: *mut crate::leanh::LeanObject,
    mut v___y_6654_: *mut crate::leanh::LeanObject,
    mut v___y_6655_: *mut crate::leanh::LeanObject,
    mut v___y_6656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6658_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
    return v___x_6658_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___boxed(
    mut v_00_u03b1_6659_: *mut crate::leanh::LeanObject,
    mut v___y_6660_: *mut crate::leanh::LeanObject,
    mut v___y_6661_: *mut crate::leanh::LeanObject,
    mut v___y_6662_: *mut crate::leanh::LeanObject,
    mut v___y_6663_: *mut crate::leanh::LeanObject,
    mut v___y_6664_: *mut crate::leanh::LeanObject,
    mut v___y_6665_: *mut crate::leanh::LeanObject,
    mut v___y_6666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6667_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(v_00_u03b1_6659_, v___y_6660_, v___y_6661_, v___y_6662_, v___y_6663_, v___y_6664_, v___y_6665_);
    crate::leanh::lean_dec(v___y_6665_);
    crate::leanh::lean_dec_ref(v___y_6664_);
    crate::leanh::lean_dec(v___y_6663_);
    crate::leanh::lean_dec_ref(v___y_6662_);
    crate::leanh::lean_dec(v___y_6661_);
    crate::leanh::lean_dec_ref(v___y_6660_);
    return v_res_6667_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(
    mut v_00_u03b1_6668_: *mut crate::leanh::LeanObject,
    mut v_x_6669_: *mut crate::leanh::LeanObject,
    mut v___y_6670_: *mut crate::leanh::LeanObject,
    mut v___y_6671_: *mut crate::leanh::LeanObject,
    mut v___y_6672_: *mut crate::leanh::LeanObject,
    mut v___y_6673_: *mut crate::leanh::LeanObject,
    mut v___y_6674_: *mut crate::leanh::LeanObject,
    mut v___y_6675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6677_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_6669_, v___y_6670_, v___y_6671_, v___y_6672_, v___y_6673_, v___y_6674_, v___y_6675_);
    return v___x_6677_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___boxed(
    mut v_00_u03b1_6678_: *mut crate::leanh::LeanObject,
    mut v_x_6679_: *mut crate::leanh::LeanObject,
    mut v___y_6680_: *mut crate::leanh::LeanObject,
    mut v___y_6681_: *mut crate::leanh::LeanObject,
    mut v___y_6682_: *mut crate::leanh::LeanObject,
    mut v___y_6683_: *mut crate::leanh::LeanObject,
    mut v___y_6684_: *mut crate::leanh::LeanObject,
    mut v___y_6685_: *mut crate::leanh::LeanObject,
    mut v___y_6686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6687_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(
            v_00_u03b1_6678_,
            v_x_6679_,
            v___y_6680_,
            v___y_6681_,
            v___y_6682_,
            v___y_6683_,
            v___y_6684_,
            v___y_6685_,
        );
    crate::leanh::lean_dec(v___y_6685_);
    crate::leanh::lean_dec_ref(v___y_6684_);
    crate::leanh::lean_dec(v___y_6683_);
    crate::leanh::lean_dec_ref(v___y_6682_);
    crate::leanh::lean_dec(v___y_6681_);
    crate::leanh::lean_dec_ref(v___y_6680_);
    return v_res_6687_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(
    mut v_cls_6688_: *mut crate::leanh::LeanObject,
    mut v_msg_6689_: *mut crate::leanh::LeanObject,
    mut v___y_6690_: *mut crate::leanh::LeanObject,
    mut v___y_6691_: *mut crate::leanh::LeanObject,
    mut v___y_6692_: *mut crate::leanh::LeanObject,
    mut v___y_6693_: *mut crate::leanh::LeanObject,
    mut v___y_6694_: *mut crate::leanh::LeanObject,
    mut v___y_6695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6697_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_6688_, v_msg_6689_, v___y_6692_, v___y_6693_, v___y_6694_, v___y_6695_);
    return v___x_6697_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___boxed(
    mut v_cls_6698_: *mut crate::leanh::LeanObject,
    mut v_msg_6699_: *mut crate::leanh::LeanObject,
    mut v___y_6700_: *mut crate::leanh::LeanObject,
    mut v___y_6701_: *mut crate::leanh::LeanObject,
    mut v___y_6702_: *mut crate::leanh::LeanObject,
    mut v___y_6703_: *mut crate::leanh::LeanObject,
    mut v___y_6704_: *mut crate::leanh::LeanObject,
    mut v___y_6705_: *mut crate::leanh::LeanObject,
    mut v___y_6706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6707_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(v_cls_6698_, v_msg_6699_, v___y_6700_, v___y_6701_, v___y_6702_, v___y_6703_, v___y_6704_, v___y_6705_);
    crate::leanh::lean_dec(v___y_6705_);
    crate::leanh::lean_dec_ref(v___y_6704_);
    crate::leanh::lean_dec(v___y_6703_);
    crate::leanh::lean_dec_ref(v___y_6702_);
    crate::leanh::lean_dec(v___y_6701_);
    crate::leanh::lean_dec_ref(v___y_6700_);
    return v_res_6707_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(
    mut v_as_6708_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6709_: *mut crate::leanh::LeanObject,
    mut v_b_6710_: *mut crate::leanh::LeanObject,
    mut v_a_6711_: *mut crate::leanh::LeanObject,
    mut v___y_6712_: *mut crate::leanh::LeanObject,
    mut v___y_6713_: *mut crate::leanh::LeanObject,
    mut v___y_6714_: *mut crate::leanh::LeanObject,
    mut v___y_6715_: *mut crate::leanh::LeanObject,
    mut v___y_6716_: *mut crate::leanh::LeanObject,
    mut v___y_6717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6719_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_6709_, v_b_6710_, v___y_6712_, v___y_6713_, v___y_6714_, v___y_6715_, v___y_6716_, v___y_6717_);
    return v___x_6719_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___boxed(
    mut v_as_6720_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6721_: *mut crate::leanh::LeanObject,
    mut v_b_6722_: *mut crate::leanh::LeanObject,
    mut v_a_6723_: *mut crate::leanh::LeanObject,
    mut v___y_6724_: *mut crate::leanh::LeanObject,
    mut v___y_6725_: *mut crate::leanh::LeanObject,
    mut v___y_6726_: *mut crate::leanh::LeanObject,
    mut v___y_6727_: *mut crate::leanh::LeanObject,
    mut v___y_6728_: *mut crate::leanh::LeanObject,
    mut v___y_6729_: *mut crate::leanh::LeanObject,
    mut v___y_6730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6731_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(v_as_6720_, v_as_x27_6721_, v_b_6722_, v_a_6723_, v___y_6724_, v___y_6725_, v___y_6726_, v___y_6727_, v___y_6728_, v___y_6729_);
    crate::leanh::lean_dec(v___y_6729_);
    crate::leanh::lean_dec_ref(v___y_6728_);
    crate::leanh::lean_dec(v___y_6727_);
    crate::leanh::lean_dec_ref(v___y_6726_);
    crate::leanh::lean_dec(v___y_6725_);
    crate::leanh::lean_dec_ref(v___y_6724_);
    crate::leanh::lean_dec(v_as_x27_6721_);
    crate::leanh::lean_dec(v_as_6720_);
    return v_res_6731_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(
    mut v_00_u03b1_6732_: *mut crate::leanh::LeanObject,
    mut v_ref_6733_: *mut crate::leanh::LeanObject,
    mut v_msg_6734_: *mut crate::leanh::LeanObject,
    mut v___y_6735_: *mut crate::leanh::LeanObject,
    mut v___y_6736_: *mut crate::leanh::LeanObject,
    mut v___y_6737_: *mut crate::leanh::LeanObject,
    mut v___y_6738_: *mut crate::leanh::LeanObject,
    mut v___y_6739_: *mut crate::leanh::LeanObject,
    mut v___y_6740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6742_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_6733_, v_msg_6734_, v___y_6735_, v___y_6736_, v___y_6737_, v___y_6738_, v___y_6739_, v___y_6740_);
    return v___x_6742_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___boxed(
    mut v_00_u03b1_6743_: *mut crate::leanh::LeanObject,
    mut v_ref_6744_: *mut crate::leanh::LeanObject,
    mut v_msg_6745_: *mut crate::leanh::LeanObject,
    mut v___y_6746_: *mut crate::leanh::LeanObject,
    mut v___y_6747_: *mut crate::leanh::LeanObject,
    mut v___y_6748_: *mut crate::leanh::LeanObject,
    mut v___y_6749_: *mut crate::leanh::LeanObject,
    mut v___y_6750_: *mut crate::leanh::LeanObject,
    mut v___y_6751_: *mut crate::leanh::LeanObject,
    mut v___y_6752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6753_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(v_00_u03b1_6743_, v_ref_6744_, v_msg_6745_, v___y_6746_, v___y_6747_, v___y_6748_, v___y_6749_, v___y_6750_, v___y_6751_);
    crate::leanh::lean_dec(v___y_6751_);
    crate::leanh::lean_dec_ref(v___y_6750_);
    crate::leanh::lean_dec(v___y_6749_);
    crate::leanh::lean_dec_ref(v___y_6748_);
    crate::leanh::lean_dec(v___y_6747_);
    crate::leanh::lean_dec_ref(v___y_6746_);
    crate::leanh::lean_dec(v_ref_6744_);
    return v_res_6753_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(
    mut v_00_u03b2_6754_: *mut crate::leanh::LeanObject,
    mut v_m_6755_: *mut crate::leanh::LeanObject,
    mut v_a_6756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6757_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_6755_, v_a_6756_);
    return v___x_6757_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b2_6758_: *mut crate::leanh::LeanObject,
    mut v_m_6759_: *mut crate::leanh::LeanObject,
    mut v_a_6760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6761_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(v_00_u03b2_6758_, v_m_6759_, v_a_6760_);
    crate::leanh::lean_dec(v_a_6760_);
    crate::leanh::lean_dec_ref(v_m_6759_);
    return v_res_6761_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(
    mut v_00_u03b1_6762_: *mut crate::leanh::LeanObject,
    mut v_msg_6763_: *mut crate::leanh::LeanObject,
    mut v___y_6764_: *mut crate::leanh::LeanObject,
    mut v___y_6765_: *mut crate::leanh::LeanObject,
    mut v___y_6766_: *mut crate::leanh::LeanObject,
    mut v___y_6767_: *mut crate::leanh::LeanObject,
    mut v___y_6768_: *mut crate::leanh::LeanObject,
    mut v___y_6769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6771_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_6763_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_, v___y_6769_);
    return v___x_6771_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___boxed(
    mut v_00_u03b1_6772_: *mut crate::leanh::LeanObject,
    mut v_msg_6773_: *mut crate::leanh::LeanObject,
    mut v___y_6774_: *mut crate::leanh::LeanObject,
    mut v___y_6775_: *mut crate::leanh::LeanObject,
    mut v___y_6776_: *mut crate::leanh::LeanObject,
    mut v___y_6777_: *mut crate::leanh::LeanObject,
    mut v___y_6778_: *mut crate::leanh::LeanObject,
    mut v___y_6779_: *mut crate::leanh::LeanObject,
    mut v___y_6780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6781_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(v_00_u03b1_6772_, v_msg_6773_, v___y_6774_, v___y_6775_, v___y_6776_, v___y_6777_, v___y_6778_, v___y_6779_);
    crate::leanh::lean_dec(v___y_6779_);
    crate::leanh::lean_dec_ref(v___y_6778_);
    crate::leanh::lean_dec(v___y_6777_);
    crate::leanh::lean_dec_ref(v___y_6776_);
    crate::leanh::lean_dec(v___y_6775_);
    crate::leanh::lean_dec_ref(v___y_6774_);
    return v_res_6781_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(
    mut v_00_u03b2_6782_: *mut crate::leanh::LeanObject,
    mut v_x_6783_: *mut crate::leanh::LeanObject,
    mut v_x_6784_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6785_: u8 = 0;
    v___x_6785_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_6783_, v_x_6784_);
    return v___x_6785_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___boxed(
    mut v_00_u03b2_6786_: *mut crate::leanh::LeanObject,
    mut v_x_6787_: *mut crate::leanh::LeanObject,
    mut v_x_6788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6789_: u8 = 0;
    let mut v_r_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6789_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(v_00_u03b2_6786_, v_x_6787_, v_x_6788_);
    crate::leanh::lean_dec_ref(v_x_6788_);
    crate::leanh::lean_dec_ref(v_x_6787_);
    v_r_6790_ = crate::leanh::lean_box((v_res_6789_) as usize);
    return v_r_6790_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(
    mut v_00_u03b2_6791_: *mut crate::leanh::LeanObject,
    mut v_a_6792_: *mut crate::leanh::LeanObject,
    mut v_x_6793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6794_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_6792_, v_x_6793_);
    return v___x_6794_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___boxed(
    mut v_00_u03b2_6795_: *mut crate::leanh::LeanObject,
    mut v_a_6796_: *mut crate::leanh::LeanObject,
    mut v_x_6797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6798_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_6795_, v_a_6796_, v_x_6797_);
    crate::leanh::lean_dec(v_x_6797_);
    crate::leanh::lean_dec(v_a_6796_);
    return v_res_6798_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(
    mut v_msgData_6799_: *mut crate::leanh::LeanObject,
    mut v_macroStack_6800_: *mut crate::leanh::LeanObject,
    mut v___y_6801_: *mut crate::leanh::LeanObject,
    mut v___y_6802_: *mut crate::leanh::LeanObject,
    mut v___y_6803_: *mut crate::leanh::LeanObject,
    mut v___y_6804_: *mut crate::leanh::LeanObject,
    mut v___y_6805_: *mut crate::leanh::LeanObject,
    mut v___y_6806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6808_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_6799_, v_macroStack_6800_, v___y_6805_);
    return v___x_6808_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___boxed(
    mut v_msgData_6809_: *mut crate::leanh::LeanObject,
    mut v_macroStack_6810_: *mut crate::leanh::LeanObject,
    mut v___y_6811_: *mut crate::leanh::LeanObject,
    mut v___y_6812_: *mut crate::leanh::LeanObject,
    mut v___y_6813_: *mut crate::leanh::LeanObject,
    mut v___y_6814_: *mut crate::leanh::LeanObject,
    mut v___y_6815_: *mut crate::leanh::LeanObject,
    mut v___y_6816_: *mut crate::leanh::LeanObject,
    mut v___y_6817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6818_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(v_msgData_6809_, v_macroStack_6810_, v___y_6811_, v___y_6812_, v___y_6813_, v___y_6814_, v___y_6815_, v___y_6816_);
    crate::leanh::lean_dec(v___y_6816_);
    crate::leanh::lean_dec_ref(v___y_6815_);
    crate::leanh::lean_dec(v___y_6814_);
    crate::leanh::lean_dec_ref(v___y_6813_);
    crate::leanh::lean_dec(v___y_6812_);
    crate::leanh::lean_dec_ref(v___y_6811_);
    return v_res_6818_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(
    mut v_00_u03b2_6819_: *mut crate::leanh::LeanObject,
    mut v_x_6820_: *mut crate::leanh::LeanObject,
    mut v_x_6821_: usize,
    mut v_x_6822_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6823_: u8 = 0;
    v___x_6823_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_6820_, v_x_6821_, v_x_6822_);
    return v___x_6823_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___boxed(
    mut v_00_u03b2_6824_: *mut crate::leanh::LeanObject,
    mut v_x_6825_: *mut crate::leanh::LeanObject,
    mut v_x_6826_: *mut crate::leanh::LeanObject,
    mut v_x_6827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_15949__boxed_6828_: usize = 0;
    let mut v_res_6829_: u8 = 0;
    let mut v_r_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_15949__boxed_6828_ = crate::leanh::lean_unbox_usize(v_x_6826_);
    crate::leanh::lean_dec(v_x_6826_);
    v_res_6829_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_6824_, v_x_6825_, v_x_15949__boxed_6828_, v_x_6827_);
    crate::leanh::lean_dec_ref(v_x_6827_);
    crate::leanh::lean_dec_ref(v_x_6825_);
    v_r_6830_ = crate::leanh::lean_box((v_res_6829_) as usize);
    return v_r_6830_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(
    mut v_00_u03b2_6831_: *mut crate::leanh::LeanObject,
    mut v_keys_6832_: *mut crate::leanh::LeanObject,
    mut v_vals_6833_: *mut crate::leanh::LeanObject,
    mut v_heq_6834_: *mut crate::leanh::LeanObject,
    mut v_i_6835_: *mut crate::leanh::LeanObject,
    mut v_k_6836_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6837_: u8 = 0;
    v___x_6837_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_6832_, v_i_6835_, v_k_6836_);
    return v___x_6837_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___boxed(
    mut v_00_u03b2_6838_: *mut crate::leanh::LeanObject,
    mut v_keys_6839_: *mut crate::leanh::LeanObject,
    mut v_vals_6840_: *mut crate::leanh::LeanObject,
    mut v_heq_6841_: *mut crate::leanh::LeanObject,
    mut v_i_6842_: *mut crate::leanh::LeanObject,
    mut v_k_6843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6844_: u8 = 0;
    let mut v_r_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6844_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(v_00_u03b2_6838_, v_keys_6839_, v_vals_6840_, v_heq_6841_, v_i_6842_, v_k_6843_);
    crate::leanh::lean_dec_ref(v_k_6843_);
    crate::leanh::lean_dec_ref(v_vals_6840_);
    crate::leanh::lean_dec_ref(v_keys_6839_);
    v_r_6845_ = crate::leanh::lean_box((v_res_6844_) as usize);
    return v_r_6845_;
}
pub unsafe fn l_Lean_Elab_Command_mkInstanceName___lam__0(
    mut v_binders_6847_: *mut crate::leanh::LeanObject,
    mut v_type_6848_: *mut crate::leanh::LeanObject,
    mut v_x_6849_: *mut crate::leanh::LeanObject,
    mut v___y_6850_: *mut crate::leanh::LeanObject,
    mut v___y_6851_: *mut crate::leanh::LeanObject,
    mut v___y_6852_: *mut crate::leanh::LeanObject,
    mut v___y_6853_: *mut crate::leanh::LeanObject,
    mut v___y_6854_: *mut crate::leanh::LeanObject,
    mut v___y_6855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6857_ = l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0;
    v___x_6858_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(
        v___x_6857_,
        v_binders_6847_,
        v_type_6848_,
        v___y_6850_,
        v___y_6851_,
        v___y_6852_,
        v___y_6853_,
        v___y_6854_,
        v___y_6855_,
    );
    return v___x_6858_;
}
pub unsafe fn l_Lean_Elab_Command_mkInstanceName___lam__0___boxed(
    mut v_binders_6859_: *mut crate::leanh::LeanObject,
    mut v_type_6860_: *mut crate::leanh::LeanObject,
    mut v_x_6861_: *mut crate::leanh::LeanObject,
    mut v___y_6862_: *mut crate::leanh::LeanObject,
    mut v___y_6863_: *mut crate::leanh::LeanObject,
    mut v___y_6864_: *mut crate::leanh::LeanObject,
    mut v___y_6865_: *mut crate::leanh::LeanObject,
    mut v___y_6866_: *mut crate::leanh::LeanObject,
    mut v___y_6867_: *mut crate::leanh::LeanObject,
    mut v___y_6868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6869_ = l_Lean_Elab_Command_mkInstanceName___lam__0(
        v_binders_6859_,
        v_type_6860_,
        v_x_6861_,
        v___y_6862_,
        v___y_6863_,
        v___y_6864_,
        v___y_6865_,
        v___y_6866_,
        v___y_6867_,
    );
    crate::leanh::lean_dec(v___y_6867_);
    crate::leanh::lean_dec_ref(v___y_6866_);
    crate::leanh::lean_dec(v___y_6865_);
    crate::leanh::lean_dec_ref(v___y_6864_);
    crate::leanh::lean_dec(v___y_6863_);
    crate::leanh::lean_dec_ref(v___y_6862_);
    crate::leanh::lean_dec_ref(v_x_6861_);
    return v_res_6869_;
}
pub unsafe fn l_Lean_Elab_Command_mkInstanceName___lam__1(
    mut v_a_6870_: *mut crate::leanh::LeanObject,
    mut v_val_6871_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_6872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6874_ = lean_st_ref_set(v_a_6870_, v_val_6871_);
    v___x_6875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6875_, 0, v___x_6874_);
    return v___x_6875_;
}
pub unsafe fn l_Lean_Elab_Command_mkInstanceName___lam__1___boxed(
    mut v_a_6876_: *mut crate::leanh::LeanObject,
    mut v_val_6877_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_6878_: *mut crate::leanh::LeanObject,
    mut v___y_6879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6880_ =
        l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_6876_, v_val_6877_, v_a_x3f_6878_);
    crate::leanh::lean_dec(v_a_x3f_6878_);
    crate::leanh::lean_dec(v_a_6876_);
    return v_res_6880_;
}
pub unsafe fn l_Lean_Elab_Command_mkInstanceName(
    mut v_binders_6881_: *mut crate::leanh::LeanObject,
    mut v_type_6882_: *mut crate::leanh::LeanObject,
    mut v_a_6883_: *mut crate::leanh::LeanObject,
    mut v_a_6884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6892_: u8 = 0;
    let mut v___x_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6898_: u8 = 0;
    let mut v___x_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6902_: u8 = 0;
    let mut v_unused_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6905_: u8 = 0;
    let mut v_a_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6911_: u8 = 0;
    let mut v___x_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6915_: u8 = 0;
    let mut v_unused_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6886_ = lean_st_ref_get(v_a_6884_);
                v___f_6887_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Command_mkInstanceName___lam__0___boxed as *mut core::ffi::c_void,
                    10,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_6887_, 0, v_binders_6881_);
                crate::leanh::lean_closure_set(v___f_6887_, 1, v_type_6882_);
                v_r_6888_ =
                    l_Lean_Elab_Command_runTermElabM___redArg(v___f_6887_, v_a_6883_, v_a_6884_);
                if crate::leanh::lean_obj_tag(v_r_6888_) == 0 {
                    v_a_6889_ = crate::leanh::lean_ctor_get(v_r_6888_, 0);
                    v_isSharedCheck_6905_ = (!crate::leanh::lean_is_exclusive(v_r_6888_)) as u8;
                    if v_isSharedCheck_6905_ == 0 {
                        v___x_6891_ = v_r_6888_;
                        v_isShared_6892_ = v_isSharedCheck_6905_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6889_);
                        crate::leanh::lean_dec(v_r_6888_);
                        v___x_6891_ = crate::leanh::lean_box(0);
                        v_isShared_6892_ = v_isSharedCheck_6905_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6906_ = crate::leanh::lean_ctor_get(v_r_6888_, 0);
                    crate::leanh::lean_inc(v_a_6906_);
                    crate::leanh::lean_dec_ref_known(v_r_6888_, 1);
                    v___x_6907_ = crate::leanh::lean_box(0);
                    v___x_6908_ = l_Lean_Elab_Command_mkInstanceName___lam__1(
                        v_a_6884_,
                        v___x_6886_,
                        v___x_6907_,
                    );
                    v_isSharedCheck_6915_ = (!crate::leanh::lean_is_exclusive(v___x_6908_)) as u8;
                    if v_isSharedCheck_6915_ == 0 {
                        v_unused_6916_ = crate::leanh::lean_ctor_get(v___x_6908_, 0);
                        crate::leanh::lean_dec(v_unused_6916_);
                        v___x_6910_ = v___x_6908_;
                        v_isShared_6911_ = v_isSharedCheck_6915_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6908_);
                        v___x_6910_ = crate::leanh::lean_box(0);
                        v_isShared_6911_ = v_isSharedCheck_6915_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_6889_);
                if v_isShared_6892_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6891_, 1);
                    v___x_6894_ = v___x_6891_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6904_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6904_, 0, v_a_6889_);
                    v___x_6894_ = v_reuseFailAlloc_6904_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6895_ = l_Lean_Elab_Command_mkInstanceName___lam__1(
                    v_a_6884_,
                    v___x_6886_,
                    v___x_6894_,
                );
                crate::leanh::lean_dec_ref(v___x_6894_);
                v_isSharedCheck_6902_ = (!crate::leanh::lean_is_exclusive(v___x_6895_)) as u8;
                if v_isSharedCheck_6902_ == 0 {
                    v_unused_6903_ = crate::leanh::lean_ctor_get(v___x_6895_, 0);
                    crate::leanh::lean_dec(v_unused_6903_);
                    v___x_6897_ = v___x_6895_;
                    v_isShared_6898_ = v_isSharedCheck_6902_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_6895_);
                    v___x_6897_ = crate::leanh::lean_box(0);
                    v_isShared_6898_ = v_isSharedCheck_6902_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6897_, 0, v_a_6889_);
                    v___x_6900_ = v___x_6897_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6901_, 0, v_a_6889_);
                    v___x_6900_ = v_reuseFailAlloc_6901_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6900_;
            }
            5 => {
                if v_isShared_6911_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6910_, 1);
                    crate::leanh::lean_ctor_set(v___x_6910_, 0, v_a_6906_);
                    v___x_6913_ = v___x_6910_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6914_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6914_, 0, v_a_6906_);
                    v___x_6913_ = v_reuseFailAlloc_6914_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6913_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_mkInstanceName___boxed(
    mut v_binders_6917_: *mut crate::leanh::LeanObject,
    mut v_type_6918_: *mut crate::leanh::LeanObject,
    mut v_a_6919_: *mut crate::leanh::LeanObject,
    mut v_a_6920_: *mut crate::leanh::LeanObject,
    mut v_a_6921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6922_ =
        l_Lean_Elab_Command_mkInstanceName(v_binders_6917_, v_type_6918_, v_a_6919_, v_a_6920_);
    crate::leanh::lean_dec(v_a_6920_);
    crate::leanh::lean_dec_ref(v_a_6919_);
    return v_res_6922_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DeclNameGen(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DeclNameGen(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_DeclNameGen(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclNameGen(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DeclNameGen(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_DeclNameGen(builtin);
}
