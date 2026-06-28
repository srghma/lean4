// Lean compiler output
// Module: Lean.Elab.ConfigEval.DeriveEvalExpr
// Imports: Lean.Elab.ConfigEval.Basic Lean.Elab.ConfigEval.Util Lean.Elab.Command Lean.Elab.DeclNameGen Lean.Elab.ErrorUtils Lean.Meta.Eval
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_append___redArg, l_Array_range, l_Array_zip___redArg,
};
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkCApp,
    l_Lean_Syntax_mkNameLit, l_Lean_Syntax_mkNumLit, l_Lean_mkCIdent, l_Lean_mkCIdentFrom,
    l_Lean_mkIdentFrom, l_Lean_quoteNameMk, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_append, l_Lean_Name_beq___boxed,
    l_Lean_Name_hasMacroScopes, l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
    l_Lean_Syntax_node6, l_Lean_Syntax_node7, l_Lean_addMacroScope, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_mkFreshUserName, l_Lean_Core_withFreshMacroScope___redArg,
    l_Lean_Exception_isRuntime,
};
use crate::r#gen::Lean::Data::Name::{
    l_Lean_Name_getPrefix, l_Lean_Name_isAnonymous, l_Lean_Name_isStr,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_InductiveVal_isNested;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_elabCommand,
    l_Lean_Elab_Command_liftTermElabM___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::ConfigEval::Basic::{
    initialize_Lean_Elab_ConfigEval_Basic, l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg,
    runtime_initialize_Lean_Elab_ConfigEval_Basic,
};
use crate::r#gen::Lean::Elab::ConfigEval::Types::l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
use crate::r#gen::Lean::Elab::ConfigEval::Util::{
    initialize_Lean_Elab_ConfigEval_Util, l_Lean_Elab_ConfigEval_makeStringMatcher,
    l_Lean_Elab_ConfigEval_withClassInstDeps, runtime_initialize_Lean_Elab_ConfigEval_Util,
};
use crate::r#gen::Lean::Elab::DeclNameGen::{
    initialize_Lean_Elab_DeclNameGen, l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27,
    runtime_initialize_Lean_Elab_DeclNameGen,
};
use crate::r#gen::Lean::Elab::ErrorUtils::{
    initialize_Lean_Elab_ErrorUtils, runtime_initialize_Lean_Elab_ErrorUtils,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_instInhabitedTermElabM;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_Environment_unlockAsync,
    l_Lean_EnvironmentHeader_moduleNames, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData,
    l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_BinderInfo_isExplicit,
    l_Lean_Expr_constName_x3f, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasMVar, l_Lean_Expr_sort___override, l_Lean_mkConst,
};
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_inlineExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_forallMetaTelescopeReducing, l_Lean_Meta_isExprDefEqGuarded, l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg;
use crate::r#gen::Lean::Meta::Eval::{
    initialize_Lean_Meta_Eval, l_Lean_Meta_evalExpr_x27___boxed, runtime_initialize_Lean_Meta_Eval,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_intercalate,
};
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
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_7, lean_apply_8, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___lam__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__0_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [10, 69, 120, 112, 101, 99, 116, 105, 110, 103, 32, 96, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__2_value:
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
    m_data: [96, 46, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__14_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__16_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 32, 104, 97, 115, 32, 117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__2_value: LeanStringObject<50> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [96, 32, 104, 97, 115, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 44, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 44, 32, 111, 114, 32, 105, 110, 100, 105, 99, 101, 115, 0]};
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__4_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__6_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 97, 110, 116, 0]};
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [70, 105, 101, 108, 100, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [96, 32, 111, 102, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__4_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [96, 32, 105, 115, 32, 100, 101, 112, 101, 110, 100, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__4_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [69, 118, 101, 114, 121, 32, 102, 105, 101, 108, 100, 32, 111, 102, 32, 96, 0]};
static mut l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__0_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__2_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 101, 120, 112, 108, 105, 99, 105, 116, 0]};
static mut l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__2_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps___closed__0_value) as *mut LeanObject;
static mut l_panic___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__5___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__5___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__1_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [69, 118, 97, 108, 69, 120, 112, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 118, 97, 108, 69, 120, 112, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__4_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 110, 102, 105, 103, 69, 118, 97, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__5_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 62, 62, 61, 95, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__5_value) as *mut LeanObject,18263539223383923855 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__7_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__8_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__8_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__9_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__9_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__7_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__8_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__9_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__10_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__11_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [69, 118, 97, 108, 69, 120, 112, 114, 46, 101, 118, 97, 108, 69, 120, 112, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__11_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__12: *mut LeanObject = core::ptr::null_mut();
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__1_value) as *mut LeanObject,9141577778669374595 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__2_value) as *mut LeanObject,10938206529616139051 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__13_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__3_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__14_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__4_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__14_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__14_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__1_value) as *mut LeanObject,9918834448007672269 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__14_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__2_value) as *mut LeanObject,17737069931188427077 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__14_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__15_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__14_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__15_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__16_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__15_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__16_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__17_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__17_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__17_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__18_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__19_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 101, 114, 109, 95, 95, 91, 95, 93, 95, 33, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__19_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__19_value) as *mut LeanObject,941824322364543252 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__20_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__21_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 114, 103, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__21_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__22: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__21_value) as *mut LeanObject,15171651311844581305 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__23_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__24_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__24_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__25_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__24_value) as *mut LeanObject,2214559063752339918 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__25_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__27_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__27: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__27_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__28_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__28_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__29_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [33, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__29: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__29_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__30_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [62, 62, 61, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__30: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__30_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__31_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__31: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__31_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__32_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__32_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__7_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__32_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__32_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__8_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__32_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__31_value) as *mut LeanObject,7043493786777132025 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__32: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__32_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__33_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__33: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__33_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__34_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__34_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__34_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__7_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__34_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__34_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__8_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__34_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__34_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__33_value) as *mut LeanObject,16077784126176397009 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__34: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__34_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__35_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__35: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__35_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [118, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg___closed__0_value) as *mut LeanObject,5219232668914052262 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg___closed__1_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__3_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__4_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__1_value) as *mut LeanObject,9918834448007672269 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 117, 114, 101, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__1_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__1_value) as *mut LeanObject,18297062970124856758 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__3_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 117, 114, 101, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__4_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__4_value) as *mut LeanObject,6146206128508995449 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__1_value) as *mut LeanObject,76013442081319628 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__5_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__5_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__6_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__6_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__7_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__8_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__8_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__7_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__8_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__8_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__9_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__10_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__10_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__7_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__8_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__10_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__11_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__12_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__12_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__13_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__13_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__13_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__14_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__15_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__15: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__15_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__16: *mut LeanObject = core::ptr::null_mut();
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__3_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__4_value) as *mut LeanObject,11364794674035624021 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__17: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__17_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__18_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__17_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__18_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__19_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__0_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__19: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__19_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__20_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__20: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__20_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__21_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__21: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__21_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__22_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__22_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__20_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__22_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__21_value) as *mut LeanObject,13144668827652875511 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__22: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__22_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__23_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__22_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__23: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__23_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__24_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__3_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__24_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__21_value) as *mut LeanObject,16981400742628996529 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__24: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__24_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__25_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__24_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__25: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__25_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__3_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__26_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__8_value) as *mut LeanObject,7892421401833366012 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__26: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__26_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__27_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__26_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__27: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__27_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__28_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__28_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__20_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__28: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__28_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__29_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__28_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__29: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__29_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__30_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__29_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__30: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__30_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__31_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__27_value) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__30_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__31: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__31_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__32_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__25_value) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__31_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__32: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__32_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__33_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__23_value) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__32_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__33: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__33_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__34_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__19_value) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__33_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__34: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__34_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__35_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__18_value) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__34_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__35: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__35_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__36_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__36: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__36_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__37_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 42, 62, 95, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__37: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__37_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__38_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__37_value) as *mut LeanObject,9434413102969235905 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__38: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__38_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__39_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 117, 97, 114, 100, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__39: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__39_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__40_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__40: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__41_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__39_value) as *mut LeanObject,52503437768633523 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__41: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__41_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__42_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__41_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__42: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__42_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__43_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__42_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__43: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__43_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__44_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 61, 61, 95, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__44: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__44_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__45_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__44_value) as *mut LeanObject,1990087968466729753 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__45: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__45_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__46_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 114, 103, 115, 46, 115, 105, 122, 101, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__46: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__46_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__47_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__47: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__48_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 122, 101, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__48: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__48_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__49_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__21_value) as *mut LeanObject,15171651311844581305 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__49_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__49_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__48_value) as *mut LeanObject,17291410713092280100 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__49: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__49_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__50_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 61, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__50: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__50_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__51_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [42, 62, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__51: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__51_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__52_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 67, 111, 110, 102, 105, 103, 69, 118, 97, 108, 46, 68, 101, 114, 105, 118, 101, 69, 118, 97, 108, 69, 120, 112, 114, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__52: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__52_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__53_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 67, 111, 110, 102, 105, 103, 69, 118, 97, 108, 46, 101, 110, 115, 117, 114, 101, 69, 118, 97, 108, 69, 120, 112, 114, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__53: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__53_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__54_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__54: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__54_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__55_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__55: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__0_value: LeanStringObject<5> =
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
        m_data: [105, 110, 115, 116, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__1_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__2_value) as *mut LeanObject,13339369412082695315 as *mut LeanObject] };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__3_value: LeanStringObject<5> =
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
        m_data: [99, 116, 111, 114, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__3_value)
                as *mut LeanObject,
            2070854219589188243 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__6_value: LeanStringObject<21> =
    LeanStringObject {
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
            116, 104, 114, 111, 119, 85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 69, 120,
            112, 114, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__6_value)
                as *mut LeanObject,
            10685348141098492536 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__9_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__10_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__11_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__12_value: LeanStringObject<7> =
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
        m_data: [115, 117, 102, 102, 105, 120, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__13_value: LeanStringObject<9> =
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
        m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__14_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [100, 101, 99, 108, 83, 105, 103, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__15_value: LeanStringObject<16> =
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
            119, 104, 101, 114, 101, 83, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__16_value: LeanStringObject<6> =
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
        m_data: [119, 104, 101, 114, 101, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__17_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__18_value: LeanStringObject<16> =
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
            115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__19_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 76, 86, 97, 108, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__19_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__2_value) as *mut LeanObject,13339369412082695315 as *mut LeanObject] };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__22_value: LeanStringObject<19> =
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
            115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 68, 101, 102, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__23_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 84, 121, 112, 101, 63, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__23_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__25_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__23_value)
                as *mut LeanObject,
            15485966262270117935 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__25_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__26_value: LeanStringObject<5> =
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
        m_data: [115, 111, 109, 101, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__26_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__27: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__28_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__26_value)
                as *mut LeanObject,
            15308379890181982757 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__28_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__29_value: LeanStringObject<7> =
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
        m_data: [79, 112, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__29_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__30_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__29_value)
                as *mut LeanObject,
            18184376426117065311 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__30_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__30_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__26_value)
                as *mut LeanObject,
            4893146552088433753 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__30_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__31_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__30_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__31_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__32_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__31_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__32_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__33_value: LeanStringObject<11> =
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
        m_data: [69, 120, 112, 114, 46, 99, 111, 110, 115, 116, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__33_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__34_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__34: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__35_value: LeanStringObject<6> =
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
        m_data: [99, 111, 110, 115, 116, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__35_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__36_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [116, 101, 114, 109, 91, 95, 93, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__36_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__37_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__36_value)
                as *mut LeanObject,
            11666683425613976406 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__37_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__38_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [112, 97, 114, 116, 105, 97, 108, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__38_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__39_value: LeanStringObject<11> =
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
        m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__39_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__40_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [100, 101, 102, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__40_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__41_value: LeanStringObject<7> =
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
        m_data: [100, 101, 99, 108, 73, 100, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__41_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__42_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__18_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__1_value) as *mut LeanObject] };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__42_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__43_value: LeanStringObject<11> =
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
        m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__43_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__44_value: LeanStringObject<9> =
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
        m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__44_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__45_value: LeanStringObject<2> =
    LeanStringObject {
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
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__45_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__46_value: LeanStringObject<6> =
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
        m_data: [97, 114, 114, 111, 119, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__46_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__47_value: LeanStringObject<5> =
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
        m_data: [69, 120, 112, 114, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__47_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__48_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__48: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__49_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__47_value)
                as *mut LeanObject,
            5816915816860015341 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__49_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__50_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 134, 146, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__50_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__51_value: LeanStringObject<6> =
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
        m_data: [77, 101, 116, 97, 77, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__51_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__52_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__52: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__53_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__51_value)
                as *mut LeanObject,
            8001041254963390847 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__53_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__54_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__54_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__55_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [58, 61, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__55_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__56_value: LeanStringObject<19> =
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
            119, 105, 116, 104, 83, 105, 109, 112, 108, 101, 69, 118, 97, 108, 69, 120, 112, 114, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__56_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__57_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__57: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__58_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__56_value)
                as *mut LeanObject,
            5734604921149960318 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__58: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__58_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__59_value: LeanStringObject<11> =
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
        m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__59: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__59_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__60_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [46, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__60: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__60_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__61_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__61: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__61_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExpr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___closed__0_value) as *mut LeanObject;
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5___redArg___closed__0: u64 = 0;
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5___closed__1_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__3_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__3_value) as *mut LeanObject,7870113334857981723 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__5_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__10_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__10_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__13_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__13_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__15_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__15_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__17_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__18_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__19_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__20_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__20_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__1_value) as *mut LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            69, 114, 114, 111, 114, 32, 101, 118, 97, 108, 117, 97, 116, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__2_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [10, 10, 69, 120, 99, 101, 112, 116, 105, 111, 110, 58, 32, 0],
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__4_value: LeanStringObject<28> =
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
            84, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 46, 32, 79, 112, 116, 105,
            111, 110, 32, 118, 97, 108, 117, 101, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__6_value: LeanStringObject<43> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 43,
        m_capacity: 43,
        m_length: 42,
        m_data: [
            69, 114, 114, 111, 114, 32, 101, 118, 97, 108, 117, 97, 116, 105, 110, 103, 32, 99,
            111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 58, 32, 116, 104, 101, 32,
            116, 121, 112, 101, 32, 96, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__8_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 115, 99, 111, 112, 101, 32, 104,
            101, 114, 101, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__10_value: LeanStringObject<9> =
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
        m_data: [32, 40, 102, 114, 111, 109, 32, 96, 0],
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__12_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [96, 41, 0],
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0___closed__0_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        69, 120, 112, 101, 99, 116, 105, 110, 103, 32, 97, 32, 99, 111, 110, 115, 116, 97, 110,
        116, 32, 119, 105, 116, 104, 32, 110, 111, 32, 117, 110, 105, 118, 101, 114, 115, 101, 115,
        44, 32, 110, 111, 116, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 107, 67, 111, 110, 115, 116, 0],
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__0_value
        ) as *mut LeanObject,
        17968679829667083557 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__3_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__3_value
) as *mut LeanObject;
static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__29_value)
            as *mut LeanObject,
        18184376426117065311 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__3_value
        ) as *mut LeanObject,
        9480010471355609749 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__4_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__5:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__1_value) as *mut LeanObject,9141577778669374595 as *mut LeanObject] };
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__7_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__8_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0],
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__8_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__9_value:
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
    m_data: [64, 0],
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__9_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__10_value:
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
    m_data: [117, 110, 115, 97, 102, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__10_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__11_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [101, 118, 97, 108, 77, 101, 116, 97, 69, 118, 97, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__11_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__12:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__13_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__11_value
        ) as *mut LeanObject,
        8405917387524130853 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__13_value
) as *mut LeanObject;
static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__7_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__14_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__21_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__14_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__14_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__9_value)
            as *mut LeanObject,
        8497769072906204829 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__14_value
) as *mut LeanObject;
static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__7_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__21_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__15_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__15_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__10_value)
            as *mut LeanObject,
        14557702332550915328 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__15_value
) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    v___x_3961_ = lean_box(0);
    v___x_3962_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
    v___x_3963_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3963_, 0, v___x_3962_);
    lean_ctor_set(v___x_3963_, 1, v___x_3961_);
    return v___x_3963_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    v___x_3965_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg___closed__0);
    v___x_3966_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3966_, 0, v___x_3965_);
    return v___x_3966_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg___boxed(
    mut v___y_3967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3968_: *mut LeanObject = core::ptr::null_mut();
    v_res_3968_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg();
    return v_res_3968_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0(
    mut v_00_u03b1_3969_: *mut LeanObject,
    mut v___y_3970_: *mut LeanObject,
    mut v___y_3971_: *mut LeanObject,
    mut v___y_3972_: *mut LeanObject,
    mut v___y_3973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    v___x_3975_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg();
    return v___x_3975_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___boxed(
    mut v_00_u03b1_3976_: *mut LeanObject,
    mut v___y_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
    mut v___y_3979_: *mut LeanObject,
    mut v___y_3980_: *mut LeanObject,
    mut v___y_3981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3982_: *mut LeanObject = core::ptr::null_mut();
    v_res_3982_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0(v_00_u03b1_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
    lean_dec(v___y_3980_);
    lean_dec_ref(v___y_3979_);
    lean_dec(v___y_3978_);
    lean_dec_ref(v___y_3977_);
    return v_res_3982_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_3984_: *mut LeanObject = core::ptr::null_mut();
    v___x_3983_ = lean_box(0);
    v_dummy_3984_ = l_Lean_Expr_sort___override(v___x_3983_);
    return v_dummy_3984_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___lam__0(
    mut v_evalExprImpl_3985_: *mut LeanObject,
    mut v_c_3986_: *mut LeanObject,
    mut v_e_3987_: *mut LeanObject,
    mut v___y_3988_: *mut LeanObject,
    mut v___y_3989_: *mut LeanObject,
    mut v___y_3990_: *mut LeanObject,
    mut v___y_3991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: u8 = 0;
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4015_: u8 = 0;
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3993_ = l_Lean_Expr_getAppFn(v_e_3987_);
                v___x_3994_ = l_Lean_Expr_constName_x3f(v___x_3993_);
                lean_dec_ref(v___x_3993_);
                if lean_obj_tag(v___x_3994_) == 1 {
                    v_val_3995_ = lean_ctor_get(v___x_3994_, 0);
                    lean_inc(v_val_3995_);
                    lean_dec_ref_known(v___x_3994_, 1);
                    if lean_obj_tag(v_val_3995_) == 1 {
                        v_pre_3996_ = lean_ctor_get(v_val_3995_, 0);
                        lean_inc(v_pre_3996_);
                        v_str_3997_ = lean_ctor_get(v_val_3995_, 1);
                        lean_inc_ref(v_str_3997_);
                        lean_dec_ref_known(v_val_3995_, 2);
                        v___x_4010_ = lean_name_eq(v_c_3986_, v_pre_3996_);
                        lean_dec(v_pre_3996_);
                        if v___x_4010_ == 0 {
                            lean_dec_ref(v_str_3997_);
                            lean_dec_ref(v_e_3987_);
                            lean_dec_ref(v_evalExprImpl_3985_);
                            v___x_4011_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg();
                            v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
                            v_isSharedCheck_4019_ = (!lean_is_exclusive(v___x_4011_)) as u8;
                            if v_isSharedCheck_4019_ == 0 {
                                v___x_4014_ = v___x_4011_;
                                v_isShared_4015_ = v_isSharedCheck_4019_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_4012_);
                                lean_dec(v___x_4011_);
                                v___x_4014_ = lean_box(0);
                                v_isShared_4015_ = v_isSharedCheck_4019_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___y_3999_ = v___y_3988_;
                            v___y_4000_ = v___y_3989_;
                            v___y_4001_ = v___y_3990_;
                            v___y_4002_ = v___y_3991_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3995_);
                        lean_dec_ref(v_e_3987_);
                        lean_dec_ref(v_evalExprImpl_3985_);
                        v___x_4020_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg();
                        return v___x_4020_;
                    }
                } else {
                    lean_dec(v___x_3994_);
                    lean_dec_ref(v_e_3987_);
                    lean_dec_ref(v_evalExprImpl_3985_);
                    v___x_4021_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr_spec__0___redArg();
                    return v___x_4021_;
                }
            }
            1 => {
                v_dummy_4003_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___lam__0___closed__0_once), _init_l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___lam__0___closed__0);
                v_nargs_4004_ = l_Lean_Expr_getAppNumArgs(v_e_3987_);
                lean_inc(v_nargs_4004_);
                v___x_4005_ = lean_mk_array(v_nargs_4004_, v_dummy_4003_);
                v___x_4006_ = lean_unsigned_to_nat(1);
                v___x_4007_ = lean_nat_sub(v_nargs_4004_, v___x_4006_);
                lean_dec(v_nargs_4004_);
                v___x_4008_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_3987_,
                    v___x_4005_,
                    v___x_4007_,
                );
                lean_inc(v___y_4002_);
                lean_inc_ref(v___y_4001_);
                lean_inc(v___y_4000_);
                lean_inc_ref(v___y_3999_);
                v___x_4009_ = lean_apply_7(
                    v_evalExprImpl_3985_,
                    v_str_3997_,
                    v___x_4008_,
                    v___y_3999_,
                    v___y_4000_,
                    v___y_4001_,
                    v___y_4002_,
                    lean_box(0),
                );
                return v___x_4009_;
            }
            2 => {
                if v_isShared_4015_ == 0 {
                    v___x_4017_ = v___x_4014_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
                    v___x_4017_ = v_reuseFailAlloc_4018_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___lam__0___boxed(
    mut v_evalExprImpl_4022_: *mut LeanObject,
    mut v_c_4023_: *mut LeanObject,
    mut v_e_4024_: *mut LeanObject,
    mut v___y_4025_: *mut LeanObject,
    mut v___y_4026_: *mut LeanObject,
    mut v___y_4027_: *mut LeanObject,
    mut v___y_4028_: *mut LeanObject,
    mut v___y_4029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4030_: *mut LeanObject = core::ptr::null_mut();
    v_res_4030_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___lam__0(
        v_evalExprImpl_4022_,
        v_c_4023_,
        v_e_4024_,
        v___y_4025_,
        v___y_4026_,
        v___y_4027_,
        v___y_4028_,
    );
    lean_dec(v___y_4028_);
    lean_dec_ref(v___y_4027_);
    lean_dec(v___y_4026_);
    lean_dec_ref(v___y_4025_);
    lean_dec(v_c_4023_);
    return v_res_4030_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    v___x_4032_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__0;
    v___x_4033_ = l_Lean_stringToMessageData(v___x_4032_);
    return v___x_4033_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    v___x_4035_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__2;
    v___x_4036_ = l_Lean_stringToMessageData(v___x_4035_);
    return v___x_4036_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
    mut v_c_4037_: *mut LeanObject,
    mut v_evalExprImpl_4038_: *mut LeanObject,
    mut v_e_4039_: *mut LeanObject,
    mut v_a_4040_: *mut LeanObject,
    mut v_a_4041_: *mut LeanObject,
    mut v_a_4042_: *mut LeanObject,
    mut v_a_4043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: u8 = 0;
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_c_4037_);
    v___f_4045_ = lean_alloc_closure(
        l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___f_4045_, 0, v_evalExprImpl_4038_);
    lean_closure_set(v___f_4045_, 1, v_c_4037_);
    v___x_4046_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__1,
    );
    v___x_4047_ = 0;
    v___x_4048_ = l_Lean_MessageData_ofConstName(v_c_4037_, v___x_4047_);
    v___x_4049_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4049_, 0, v___x_4046_);
    lean_ctor_set(v___x_4049_, 1, v___x_4048_);
    v___x_4050_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__3_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__3,
    );
    v___x_4051_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4051_, 0, v___x_4049_);
    lean_ctor_set(v___x_4051_, 1, v___x_4050_);
    v___x_4052_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
        v___f_4045_,
        v_e_4039_,
        v___x_4051_,
        v_a_4040_,
        v_a_4041_,
        v_a_4042_,
        v_a_4043_,
    );
    return v___x_4052_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___boxed(
    mut v_c_4053_: *mut LeanObject,
    mut v_evalExprImpl_4054_: *mut LeanObject,
    mut v_e_4055_: *mut LeanObject,
    mut v_a_4056_: *mut LeanObject,
    mut v_a_4057_: *mut LeanObject,
    mut v_a_4058_: *mut LeanObject,
    mut v_a_4059_: *mut LeanObject,
    mut v_a_4060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4061_: *mut LeanObject = core::ptr::null_mut();
    v_res_4061_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
        v_c_4053_,
        v_evalExprImpl_4054_,
        v_e_4055_,
        v_a_4056_,
        v_a_4057_,
        v_a_4058_,
        v_a_4059_,
    );
    lean_dec(v_a_4059_);
    lean_dec_ref(v_a_4058_);
    lean_dec(v_a_4057_);
    lean_dec_ref(v_a_4056_);
    return v_res_4061_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr(
    mut v_00_u03b1_4062_: *mut LeanObject,
    mut v_c_4063_: *mut LeanObject,
    mut v_evalExprImpl_4064_: *mut LeanObject,
    mut v_e_4065_: *mut LeanObject,
    mut v_a_4066_: *mut LeanObject,
    mut v_a_4067_: *mut LeanObject,
    mut v_a_4068_: *mut LeanObject,
    mut v_a_4069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    v___x_4071_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
        v_c_4063_,
        v_evalExprImpl_4064_,
        v_e_4065_,
        v_a_4066_,
        v_a_4067_,
        v_a_4068_,
        v_a_4069_,
    );
    return v___x_4071_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___boxed(
    mut v_00_u03b1_4072_: *mut LeanObject,
    mut v_c_4073_: *mut LeanObject,
    mut v_evalExprImpl_4074_: *mut LeanObject,
    mut v_e_4075_: *mut LeanObject,
    mut v_a_4076_: *mut LeanObject,
    mut v_a_4077_: *mut LeanObject,
    mut v_a_4078_: *mut LeanObject,
    mut v_a_4079_: *mut LeanObject,
    mut v_a_4080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4081_: *mut LeanObject = core::ptr::null_mut();
    v_res_4081_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr(
        v_00_u03b1_4072_,
        v_c_4073_,
        v_evalExprImpl_4074_,
        v_e_4075_,
        v_a_4076_,
        v_a_4077_,
        v_a_4078_,
        v_a_4079_,
    );
    lean_dec(v_a_4079_);
    lean_dec_ref(v_a_4078_);
    lean_dec(v_a_4077_);
    lean_dec_ref(v_a_4076_);
    return v_res_4081_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__2(
    mut v_msgData_4082_: *mut LeanObject,
    mut v___y_4083_: *mut LeanObject,
    mut v___y_4084_: *mut LeanObject,
    mut v___y_4085_: *mut LeanObject,
    mut v___y_4086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    v___x_4088_ = lean_st_ref_get(v___y_4086_);
    v_env_4089_ = lean_ctor_get(v___x_4088_, 0);
    lean_inc_ref(v_env_4089_);
    lean_dec(v___x_4088_);
    v___x_4090_ = lean_st_ref_get(v___y_4084_);
    v_mctx_4091_ = lean_ctor_get(v___x_4090_, 0);
    lean_inc_ref(v_mctx_4091_);
    lean_dec(v___x_4090_);
    v_lctx_4092_ = lean_ctor_get(v___y_4083_, 2);
    v_options_4093_ = lean_ctor_get(v___y_4085_, 2);
    lean_inc_ref(v_options_4093_);
    lean_inc_ref(v_lctx_4092_);
    v___x_4094_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4094_, 0, v_env_4089_);
    lean_ctor_set(v___x_4094_, 1, v_mctx_4091_);
    lean_ctor_set(v___x_4094_, 2, v_lctx_4092_);
    lean_ctor_set(v___x_4094_, 3, v_options_4093_);
    v___x_4095_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4095_, 0, v___x_4094_);
    lean_ctor_set(v___x_4095_, 1, v_msgData_4082_);
    v___x_4096_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4096_, 0, v___x_4095_);
    return v___x_4096_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__2___boxed(
    mut v_msgData_4097_: *mut LeanObject,
    mut v___y_4098_: *mut LeanObject,
    mut v___y_4099_: *mut LeanObject,
    mut v___y_4100_: *mut LeanObject,
    mut v___y_4101_: *mut LeanObject,
    mut v___y_4102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4103_: *mut LeanObject = core::ptr::null_mut();
    v_res_4103_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__2(v_msgData_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
    lean_dec(v___y_4101_);
    lean_dec_ref(v___y_4100_);
    lean_dec(v___y_4099_);
    lean_dec_ref(v___y_4098_);
    return v_res_4103_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__5(
    mut v_opts_4104_: *mut LeanObject,
    mut v_opt_4105_: *mut LeanObject,
) -> u8 {
    let mut v_name_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    v_name_4106_ = lean_ctor_get(v_opt_4105_, 0);
    v_defValue_4107_ = lean_ctor_get(v_opt_4105_, 1);
    v_map_4108_ = lean_ctor_get(v_opts_4104_, 0);
    v___x_4109_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4108_,
            v_name_4106_,
        );
    if lean_obj_tag(v___x_4109_) == 0 {
        let mut v___x_4110_: u8 = 0;
        v___x_4110_ = (lean_unbox(v_defValue_4107_) as u8);
        return v___x_4110_;
    } else {
        let mut v_val_4111_: *mut LeanObject = core::ptr::null_mut();
        v_val_4111_ = lean_ctor_get(v___x_4109_, 0);
        lean_inc(v_val_4111_);
        lean_dec_ref_known(v___x_4109_, 1);
        if lean_obj_tag(v_val_4111_) == 1 {
            let mut v_v_4112_: u8 = 0;
            v_v_4112_ = lean_ctor_get_uint8(v_val_4111_, 0 as u32);
            lean_dec_ref_known(v_val_4111_, 0);
            return v_v_4112_;
        } else {
            let mut v___x_4113_: u8 = 0;
            lean_dec(v_val_4111_);
            v___x_4113_ = (lean_unbox(v_defValue_4107_) as u8);
            return v___x_4113_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__5___boxed(
    mut v_opts_4114_: *mut LeanObject,
    mut v_opt_4115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4116_: u8 = 0;
    let mut v_r_4117_: *mut LeanObject = core::ptr::null_mut();
    v_res_4116_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__5(v_opts_4114_, v_opt_4115_);
    lean_dec_ref(v_opt_4115_);
    lean_dec_ref(v_opts_4114_);
    v_r_4117_ = lean_box((v_res_4116_) as usize);
    return v_r_4117_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__0()
-> *mut LeanObject {
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    v___x_4118_ = lean_box(1);
    v___x_4119_ = l_Lean_MessageData_ofFormat(v___x_4118_);
    return v___x_4119_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__3()
-> *mut LeanObject {
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    v___x_4123_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__2;
    v___x_4124_ = l_Lean_MessageData_ofFormat(v___x_4123_);
    return v___x_4124_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6(
    mut v_x_4125_: *mut LeanObject,
    mut v_x_4126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4131_: u8 = 0;
    let mut v_before_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4135_: u8 = 0;
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_unused_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4126_) == 0 {
                    return v_x_4125_;
                } else {
                    v_head_4127_ = lean_ctor_get(v_x_4126_, 0);
                    v_tail_4128_ = lean_ctor_get(v_x_4126_, 1);
                    v_isSharedCheck_4150_ = (!lean_is_exclusive(v_x_4126_)) as u8;
                    if v_isSharedCheck_4150_ == 0 {
                        v___x_4130_ = v_x_4126_;
                        v_isShared_4131_ = v_isSharedCheck_4150_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4128_);
                        lean_inc(v_head_4127_);
                        lean_dec(v_x_4126_);
                        v___x_4130_ = lean_box(0);
                        v_isShared_4131_ = v_isSharedCheck_4150_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_4132_ = lean_ctor_get(v_head_4127_, 0);
                v_isSharedCheck_4148_ = (!lean_is_exclusive(v_head_4127_)) as u8;
                if v_isSharedCheck_4148_ == 0 {
                    v_unused_4149_ = lean_ctor_get(v_head_4127_, 1);
                    lean_dec(v_unused_4149_);
                    v___x_4134_ = v_head_4127_;
                    v_isShared_4135_ = v_isSharedCheck_4148_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_4132_);
                    lean_dec(v_head_4127_);
                    v___x_4134_ = lean_box(0);
                    v_isShared_4135_ = v_isSharedCheck_4148_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4136_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__0);
                if v_isShared_4135_ == 0 {
                    lean_ctor_set_tag(v___x_4134_, 7);
                    lean_ctor_set(v___x_4134_, 1, v___x_4136_);
                    lean_ctor_set(v___x_4134_, 0, v_x_4125_);
                    v___x_4138_ = v___x_4134_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4147_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_x_4125_);
                    lean_ctor_set(v_reuseFailAlloc_4147_, 1, v___x_4136_);
                    v___x_4138_ = v_reuseFailAlloc_4147_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4139_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__3);
                if v_isShared_4131_ == 0 {
                    lean_ctor_set_tag(v___x_4130_, 7);
                    lean_ctor_set(v___x_4130_, 1, v___x_4139_);
                    lean_ctor_set(v___x_4130_, 0, v___x_4138_);
                    v___x_4141_ = v___x_4130_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4138_);
                    lean_ctor_set(v_reuseFailAlloc_4146_, 1, v___x_4139_);
                    v___x_4141_ = v_reuseFailAlloc_4146_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4142_ = l_Lean_MessageData_ofSyntax(v_before_4132_);
                v___x_4143_ = l_Lean_indentD(v___x_4142_);
                v___x_4144_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4144_, 0, v___x_4141_);
                lean_ctor_set(v___x_4144_, 1, v___x_4143_);
                v_x_4125_ = v___x_4144_;
                v_x_4126_ = v_tail_4128_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    v___x_4154_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__1;
    v___x_4155_ = l_Lean_MessageData_ofFormat(v___x_4154_);
    return v___x_4155_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg(
    mut v_msgData_4156_: *mut LeanObject,
    mut v_macroStack_4157_: *mut LeanObject,
    mut v___y_4158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: u8 = 0;
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4169_: u8 = 0;
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4181_: u8 = 0;
    let mut v_unused_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4160_ = lean_ctor_get(v___y_4158_, 2);
                v___x_4161_ = l_Lean_Elab_pp_macroStack;
                v___x_4162_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__5(v_options_4160_, v___x_4161_);
                if v___x_4162_ == 0 {
                    lean_dec(v_macroStack_4157_);
                    v___x_4163_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4163_, 0, v_msgData_4156_);
                    return v___x_4163_;
                } else {
                    if lean_obj_tag(v_macroStack_4157_) == 0 {
                        v___x_4164_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4164_, 0, v_msgData_4156_);
                        return v___x_4164_;
                    } else {
                        v_head_4165_ = lean_ctor_get(v_macroStack_4157_, 0);
                        lean_inc(v_head_4165_);
                        v_after_4166_ = lean_ctor_get(v_head_4165_, 1);
                        v_isSharedCheck_4181_ = (!lean_is_exclusive(v_head_4165_)) as u8;
                        if v_isSharedCheck_4181_ == 0 {
                            v_unused_4182_ = lean_ctor_get(v_head_4165_, 0);
                            lean_dec(v_unused_4182_);
                            v___x_4168_ = v_head_4165_;
                            v_isShared_4169_ = v_isSharedCheck_4181_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_4166_);
                            lean_dec(v_head_4165_);
                            v___x_4168_ = lean_box(0);
                            v_isShared_4169_ = v_isSharedCheck_4181_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4170_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6___closed__0);
                if v_isShared_4169_ == 0 {
                    lean_ctor_set_tag(v___x_4168_, 7);
                    lean_ctor_set(v___x_4168_, 1, v___x_4170_);
                    lean_ctor_set(v___x_4168_, 0, v_msgData_4156_);
                    v___x_4172_ = v___x_4168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4180_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_msgData_4156_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 1, v___x_4170_);
                    v___x_4172_ = v_reuseFailAlloc_4180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4173_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___closed__2);
                v___x_4174_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4174_, 0, v___x_4172_);
                lean_ctor_set(v___x_4174_, 1, v___x_4173_);
                v___x_4175_ = l_Lean_MessageData_ofSyntax(v_after_4166_);
                v___x_4176_ = l_Lean_indentD(v___x_4175_);
                v_msgData_4177_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_4177_, 0, v___x_4174_);
                lean_ctor_set(v_msgData_4177_, 1, v___x_4176_);
                v___x_4178_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3_spec__6(v_msgData_4177_, v_macroStack_4157_);
                v___x_4179_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4179_, 0, v___x_4178_);
                return v___x_4179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg___boxed(
    mut v_msgData_4183_: *mut LeanObject,
    mut v_macroStack_4184_: *mut LeanObject,
    mut v___y_4185_: *mut LeanObject,
    mut v___y_4186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4187_: *mut LeanObject = core::ptr::null_mut();
    v_res_4187_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg(v_msgData_4183_, v_macroStack_4184_, v___y_4185_);
    lean_dec_ref(v___y_4185_);
    return v_res_4187_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___redArg(
    mut v_msg_4188_: *mut LeanObject,
    mut v___y_4189_: *mut LeanObject,
    mut v___y_4190_: *mut LeanObject,
    mut v___y_4191_: *mut LeanObject,
    mut v___y_4192_: *mut LeanObject,
    mut v___y_4193_: *mut LeanObject,
    mut v___y_4194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4205_: u8 = 0;
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4196_ = lean_ctor_get(v___y_4193_, 5);
                v___x_4197_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__2(v_msg_4188_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
                v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
                lean_inc(v_a_4198_);
                lean_dec_ref(v___x_4197_);
                v_macroStack_4199_ = lean_ctor_get(v___y_4189_, 1);
                v___x_4200_ = l_Lean_Elab_getBetterRef(v_ref_4196_, v_macroStack_4199_);
                lean_inc(v_macroStack_4199_);
                v___x_4201_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg(v_a_4198_, v_macroStack_4199_, v___y_4193_);
                v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
                v_isSharedCheck_4210_ = (!lean_is_exclusive(v___x_4201_)) as u8;
                if v_isSharedCheck_4210_ == 0 {
                    v___x_4204_ = v___x_4201_;
                    v_isShared_4205_ = v_isSharedCheck_4210_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4202_);
                    lean_dec(v___x_4201_);
                    v___x_4204_ = lean_box(0);
                    v_isShared_4205_ = v_isSharedCheck_4210_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4206_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4206_, 0, v___x_4200_);
                lean_ctor_set(v___x_4206_, 1, v_a_4202_);
                if v_isShared_4205_ == 0 {
                    lean_ctor_set_tag(v___x_4204_, 1);
                    lean_ctor_set(v___x_4204_, 0, v___x_4206_);
                    v___x_4208_ = v___x_4204_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
                    v___x_4208_ = v_reuseFailAlloc_4209_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___redArg___boxed(
    mut v_msg_4211_: *mut LeanObject,
    mut v___y_4212_: *mut LeanObject,
    mut v___y_4213_: *mut LeanObject,
    mut v___y_4214_: *mut LeanObject,
    mut v___y_4215_: *mut LeanObject,
    mut v___y_4216_: *mut LeanObject,
    mut v___y_4217_: *mut LeanObject,
    mut v___y_4218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4219_: *mut LeanObject = core::ptr::null_mut();
    v_res_4219_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___redArg(v_msg_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
    lean_dec(v___y_4217_);
    lean_dec_ref(v___y_4216_);
    lean_dec(v___y_4215_);
    lean_dec_ref(v___y_4214_);
    lean_dec(v___y_4213_);
    lean_dec_ref(v___y_4212_);
    return v_res_4219_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__8___redArg(
    mut v_ref_4220_: *mut LeanObject,
    mut v_msg_4221_: *mut LeanObject,
    mut v___y_4222_: *mut LeanObject,
    mut v___y_4223_: *mut LeanObject,
    mut v___y_4224_: *mut LeanObject,
    mut v___y_4225_: *mut LeanObject,
    mut v___y_4226_: *mut LeanObject,
    mut v___y_4227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4241_: u8 = 0;
    let mut v_cancelTk_x3f_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4243_: u8 = 0;
    let mut v_inheritedTraceOptions_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_4229_ = lean_ctor_get(v___y_4226_, 0);
    v_fileMap_4230_ = lean_ctor_get(v___y_4226_, 1);
    v_options_4231_ = lean_ctor_get(v___y_4226_, 2);
    v_currRecDepth_4232_ = lean_ctor_get(v___y_4226_, 3);
    v_maxRecDepth_4233_ = lean_ctor_get(v___y_4226_, 4);
    v_ref_4234_ = lean_ctor_get(v___y_4226_, 5);
    v_currNamespace_4235_ = lean_ctor_get(v___y_4226_, 6);
    v_openDecls_4236_ = lean_ctor_get(v___y_4226_, 7);
    v_initHeartbeats_4237_ = lean_ctor_get(v___y_4226_, 8);
    v_maxHeartbeats_4238_ = lean_ctor_get(v___y_4226_, 9);
    v_quotContext_4239_ = lean_ctor_get(v___y_4226_, 10);
    v_currMacroScope_4240_ = lean_ctor_get(v___y_4226_, 11);
    v_diag_4241_ = lean_ctor_get_uint8(
        v___y_4226_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4242_ = lean_ctor_get(v___y_4226_, 12);
    v_suppressElabErrors_4243_ = lean_ctor_get_uint8(
        v___y_4226_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4244_ = lean_ctor_get(v___y_4226_, 13);
    v_ref_4245_ = l_Lean_replaceRef(v_ref_4220_, v_ref_4234_);
    lean_inc_ref(v_inheritedTraceOptions_4244_);
    lean_inc(v_cancelTk_x3f_4242_);
    lean_inc(v_currMacroScope_4240_);
    lean_inc(v_quotContext_4239_);
    lean_inc(v_maxHeartbeats_4238_);
    lean_inc(v_initHeartbeats_4237_);
    lean_inc(v_openDecls_4236_);
    lean_inc(v_currNamespace_4235_);
    lean_inc(v_maxRecDepth_4233_);
    lean_inc(v_currRecDepth_4232_);
    lean_inc_ref(v_options_4231_);
    lean_inc_ref(v_fileMap_4230_);
    lean_inc_ref(v_fileName_4229_);
    v___x_4246_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_4246_, 0, v_fileName_4229_);
    lean_ctor_set(v___x_4246_, 1, v_fileMap_4230_);
    lean_ctor_set(v___x_4246_, 2, v_options_4231_);
    lean_ctor_set(v___x_4246_, 3, v_currRecDepth_4232_);
    lean_ctor_set(v___x_4246_, 4, v_maxRecDepth_4233_);
    lean_ctor_set(v___x_4246_, 5, v_ref_4245_);
    lean_ctor_set(v___x_4246_, 6, v_currNamespace_4235_);
    lean_ctor_set(v___x_4246_, 7, v_openDecls_4236_);
    lean_ctor_set(v___x_4246_, 8, v_initHeartbeats_4237_);
    lean_ctor_set(v___x_4246_, 9, v_maxHeartbeats_4238_);
    lean_ctor_set(v___x_4246_, 10, v_quotContext_4239_);
    lean_ctor_set(v___x_4246_, 11, v_currMacroScope_4240_);
    lean_ctor_set(v___x_4246_, 12, v_cancelTk_x3f_4242_);
    lean_ctor_set(v___x_4246_, 13, v_inheritedTraceOptions_4244_);
    lean_ctor_set_uint8(
        v___x_4246_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_4241_,
    );
    lean_ctor_set_uint8(
        v___x_4246_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4243_,
    );
    v___x_4247_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___redArg(v_msg_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___x_4246_, v___y_4227_);
    lean_dec_ref_known(v___x_4246_, 14);
    return v___x_4247_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__8___redArg___boxed(
    mut v_ref_4248_: *mut LeanObject,
    mut v_msg_4249_: *mut LeanObject,
    mut v___y_4250_: *mut LeanObject,
    mut v___y_4251_: *mut LeanObject,
    mut v___y_4252_: *mut LeanObject,
    mut v___y_4253_: *mut LeanObject,
    mut v___y_4254_: *mut LeanObject,
    mut v___y_4255_: *mut LeanObject,
    mut v___y_4256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4257_: *mut LeanObject = core::ptr::null_mut();
    v_res_4257_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__8___redArg(v_ref_4248_, v_msg_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
    lean_dec(v___y_4255_);
    lean_dec_ref(v___y_4254_);
    lean_dec(v___y_4253_);
    lean_dec_ref(v___y_4252_);
    lean_dec(v___y_4251_);
    lean_dec_ref(v___y_4250_);
    lean_dec(v_ref_4248_);
    return v_res_4257_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    v___x_4258_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4258_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    v___x_4259_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
    v___x_4260_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4260_, 0, v___x_4259_);
    return v___x_4260_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    v___x_4261_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__1);
    v___x_4262_ = lean_unsigned_to_nat(0);
    v___x_4263_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_4263_, 0, v___x_4262_);
    lean_ctor_set(v___x_4263_, 1, v___x_4262_);
    lean_ctor_set(v___x_4263_, 2, v___x_4262_);
    lean_ctor_set(v___x_4263_, 3, v___x_4262_);
    lean_ctor_set(v___x_4263_, 4, v___x_4261_);
    lean_ctor_set(v___x_4263_, 5, v___x_4261_);
    lean_ctor_set(v___x_4263_, 6, v___x_4261_);
    lean_ctor_set(v___x_4263_, 7, v___x_4261_);
    lean_ctor_set(v___x_4263_, 8, v___x_4261_);
    lean_ctor_set(v___x_4263_, 9, v___x_4261_);
    return v___x_4263_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    v___x_4264_ = lean_unsigned_to_nat(32);
    v___x_4265_ = lean_mk_empty_array_with_capacity(v___x_4264_);
    v___x_4266_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4266_, 0, v___x_4265_);
    return v___x_4266_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4267_: usize = 0;
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    v___x_4267_ = 5usize;
    v___x_4268_ = lean_unsigned_to_nat(0);
    v___x_4269_ = lean_unsigned_to_nat(32);
    v___x_4270_ = lean_mk_empty_array_with_capacity(v___x_4269_);
    v___x_4271_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__3);
    v___x_4272_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4272_, 0, v___x_4271_);
    lean_ctor_set(v___x_4272_, 1, v___x_4270_);
    lean_ctor_set(v___x_4272_, 2, v___x_4268_);
    lean_ctor_set(v___x_4272_, 3, v___x_4268_);
    lean_ctor_set_usize(v___x_4272_, 4, v___x_4267_);
    return v___x_4272_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    v___x_4273_ = lean_box(1);
    v___x_4274_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__4);
    v___x_4275_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__1);
    v___x_4276_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4276_, 0, v___x_4275_);
    lean_ctor_set(v___x_4276_, 1, v___x_4274_);
    lean_ctor_set(v___x_4276_, 2, v___x_4273_);
    return v___x_4276_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    v___x_4278_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__6;
    v___x_4279_ = l_Lean_stringToMessageData(v___x_4278_);
    return v___x_4279_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    v___x_4281_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__8;
    v___x_4282_ = l_Lean_stringToMessageData(v___x_4281_);
    return v___x_4282_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    v___x_4284_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__10;
    v___x_4285_ = l_Lean_stringToMessageData(v___x_4284_);
    return v___x_4285_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    v___x_4287_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__12;
    v___x_4288_ = l_Lean_stringToMessageData(v___x_4287_);
    return v___x_4288_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    v___x_4290_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__14;
    v___x_4291_ = l_Lean_stringToMessageData(v___x_4290_);
    return v___x_4291_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    v___x_4293_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__16;
    v___x_4294_ = l_Lean_stringToMessageData(v___x_4293_);
    return v___x_4294_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(
    mut v_msg_4295_: *mut LeanObject,
    mut v_declHint_4296_: *mut LeanObject,
    mut v___y_4297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: u8 = 0;
    let mut v_isExporting_4302_: u8 = 0;
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: u8 = 0;
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4324_: u8 = 0;
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4356_: u8 = 0;
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4299_ = lean_st_ref_get(v___y_4297_);
                v_env_4300_ = lean_ctor_get(v___x_4299_, 0);
                lean_inc_ref(v_env_4300_);
                lean_dec(v___x_4299_);
                v___x_4301_ = l_Lean_Name_isAnonymous(v_declHint_4296_);
                if v___x_4301_ == 0 {
                    v_isExporting_4302_ = lean_ctor_get_uint8(
                        v_env_4300_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4302_ == 0 {
                        lean_dec_ref(v_env_4300_);
                        lean_dec(v_declHint_4296_);
                        v___x_4303_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4303_, 0, v_msg_4295_);
                        return v___x_4303_;
                    } else {
                        lean_inc_ref(v_env_4300_);
                        v___x_4304_ = l_Lean_Environment_setExporting(v_env_4300_, v___x_4301_);
                        lean_inc(v_declHint_4296_);
                        lean_inc_ref(v___x_4304_);
                        v___x_4305_ = l_Lean_Environment_contains(
                            v___x_4304_,
                            v_declHint_4296_,
                            v_isExporting_4302_,
                        );
                        if v___x_4305_ == 0 {
                            lean_dec_ref(v___x_4304_);
                            lean_dec_ref(v_env_4300_);
                            lean_dec(v_declHint_4296_);
                            v___x_4306_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4306_, 0, v_msg_4295_);
                            return v___x_4306_;
                        } else {
                            v___x_4307_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__2);
                            v___x_4308_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__5);
                            v___x_4309_ = l_Lean_Options_empty;
                            v___x_4310_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_4310_, 0, v___x_4304_);
                            lean_ctor_set(v___x_4310_, 1, v___x_4307_);
                            lean_ctor_set(v___x_4310_, 2, v___x_4308_);
                            lean_ctor_set(v___x_4310_, 3, v___x_4309_);
                            lean_inc(v_declHint_4296_);
                            v___x_4311_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4296_, v___x_4301_);
                            v_c_4312_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_4312_, 0, v___x_4310_);
                            lean_ctor_set(v_c_4312_, 1, v___x_4311_);
                            v___x_4313_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4300_,
                                v_declHint_4296_,
                            );
                            if lean_obj_tag(v___x_4313_) == 0 {
                                lean_dec_ref(v_env_4300_);
                                lean_dec(v_declHint_4296_);
                                v___x_4314_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__7);
                                v___x_4315_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4315_, 0, v___x_4314_);
                                lean_ctor_set(v___x_4315_, 1, v_c_4312_);
                                v___x_4316_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__9);
                                v___x_4317_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4317_, 0, v___x_4315_);
                                lean_ctor_set(v___x_4317_, 1, v___x_4316_);
                                v___x_4318_ = l_Lean_MessageData_note(v___x_4317_);
                                v___x_4319_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4319_, 0, v_msg_4295_);
                                lean_ctor_set(v___x_4319_, 1, v___x_4318_);
                                v___x_4320_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_4320_, 0, v___x_4319_);
                                return v___x_4320_;
                            } else {
                                v_val_4321_ = lean_ctor_get(v___x_4313_, 0);
                                v_isSharedCheck_4356_ = (!lean_is_exclusive(v___x_4313_)) as u8;
                                if v_isSharedCheck_4356_ == 0 {
                                    v___x_4323_ = v___x_4313_;
                                    v_isShared_4324_ = v_isSharedCheck_4356_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_4321_);
                                    lean_dec(v___x_4313_);
                                    v___x_4323_ = lean_box(0);
                                    v_isShared_4324_ = v_isSharedCheck_4356_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_4300_);
                    lean_dec(v_declHint_4296_);
                    v___x_4357_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4357_, 0, v_msg_4295_);
                    return v___x_4357_;
                }
            }
            1 => {
                v___x_4325_ = lean_box(0);
                v___x_4326_ = l_Lean_Environment_header(v_env_4300_);
                lean_dec_ref(v_env_4300_);
                v___x_4327_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4326_);
                v_mod_4328_ = lean_array_get(v___x_4325_, v___x_4327_, v_val_4321_);
                lean_dec(v_val_4321_);
                lean_dec_ref(v___x_4327_);
                v___x_4329_ = l_Lean_isPrivateName(v_declHint_4296_);
                lean_dec(v_declHint_4296_);
                if v___x_4329_ == 0 {
                    v___x_4330_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__11);
                    v___x_4331_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4331_, 0, v___x_4330_);
                    lean_ctor_set(v___x_4331_, 1, v_c_4312_);
                    v___x_4332_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__13);
                    v___x_4333_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4333_, 0, v___x_4331_);
                    lean_ctor_set(v___x_4333_, 1, v___x_4332_);
                    v___x_4334_ = l_Lean_MessageData_ofName(v_mod_4328_);
                    v___x_4335_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4335_, 0, v___x_4333_);
                    lean_ctor_set(v___x_4335_, 1, v___x_4334_);
                    v___x_4336_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__3_once), _init_l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg___closed__3);
                    v___x_4337_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4337_, 0, v___x_4335_);
                    lean_ctor_set(v___x_4337_, 1, v___x_4336_);
                    v___x_4338_ = l_Lean_MessageData_note(v___x_4337_);
                    v___x_4339_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4339_, 0, v_msg_4295_);
                    lean_ctor_set(v___x_4339_, 1, v___x_4338_);
                    if v_isShared_4324_ == 0 {
                        lean_ctor_set_tag(v___x_4323_, 0);
                        lean_ctor_set(v___x_4323_, 0, v___x_4339_);
                        v___x_4341_ = v___x_4323_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4339_);
                        v___x_4341_ = v_reuseFailAlloc_4342_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4343_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__7);
                    v___x_4344_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4344_, 0, v___x_4343_);
                    lean_ctor_set(v___x_4344_, 1, v_c_4312_);
                    v___x_4345_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__15);
                    v___x_4346_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4346_, 0, v___x_4344_);
                    lean_ctor_set(v___x_4346_, 1, v___x_4345_);
                    v___x_4347_ = l_Lean_MessageData_ofName(v_mod_4328_);
                    v___x_4348_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4348_, 0, v___x_4346_);
                    lean_ctor_set(v___x_4348_, 1, v___x_4347_);
                    v___x_4349_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__17);
                    v___x_4350_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4350_, 0, v___x_4348_);
                    lean_ctor_set(v___x_4350_, 1, v___x_4349_);
                    v___x_4351_ = l_Lean_MessageData_note(v___x_4350_);
                    v___x_4352_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4352_, 0, v_msg_4295_);
                    lean_ctor_set(v___x_4352_, 1, v___x_4351_);
                    if v_isShared_4324_ == 0 {
                        lean_ctor_set_tag(v___x_4323_, 0);
                        lean_ctor_set(v___x_4323_, 0, v___x_4352_);
                        v___x_4354_ = v___x_4323_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4352_);
                        v___x_4354_ = v_reuseFailAlloc_4355_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4341_;
            }
            3 => {
                return v___x_4354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___boxed(
    mut v_msg_4358_: *mut LeanObject,
    mut v_declHint_4359_: *mut LeanObject,
    mut v___y_4360_: *mut LeanObject,
    mut v___y_4361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4362_: *mut LeanObject = core::ptr::null_mut();
    v_res_4362_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_msg_4358_, v_declHint_4359_, v___y_4360_);
    lean_dec(v___y_4360_);
    return v_res_4362_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7(
    mut v_msg_4363_: *mut LeanObject,
    mut v_declHint_4364_: *mut LeanObject,
    mut v___y_4365_: *mut LeanObject,
    mut v___y_4366_: *mut LeanObject,
    mut v___y_4367_: *mut LeanObject,
    mut v___y_4368_: *mut LeanObject,
    mut v___y_4369_: *mut LeanObject,
    mut v___y_4370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4376_: u8 = 0;
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_msg_4363_, v_declHint_4364_, v___y_4370_);
                v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
                v_isSharedCheck_4382_ = (!lean_is_exclusive(v___x_4372_)) as u8;
                if v_isSharedCheck_4382_ == 0 {
                    v___x_4375_ = v___x_4372_;
                    v_isShared_4376_ = v_isSharedCheck_4382_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4373_);
                    lean_dec(v___x_4372_);
                    v___x_4375_ = lean_box(0);
                    v_isShared_4376_ = v_isSharedCheck_4382_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4377_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4378_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_4378_, 0, v___x_4377_);
                lean_ctor_set(v___x_4378_, 1, v_a_4373_);
                if v_isShared_4376_ == 0 {
                    lean_ctor_set(v___x_4375_, 0, v___x_4378_);
                    v___x_4380_ = v___x_4375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4378_);
                    v___x_4380_ = v_reuseFailAlloc_4381_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(
    mut v_msg_4383_: *mut LeanObject,
    mut v_declHint_4384_: *mut LeanObject,
    mut v___y_4385_: *mut LeanObject,
    mut v___y_4386_: *mut LeanObject,
    mut v___y_4387_: *mut LeanObject,
    mut v___y_4388_: *mut LeanObject,
    mut v___y_4389_: *mut LeanObject,
    mut v___y_4390_: *mut LeanObject,
    mut v___y_4391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4392_: *mut LeanObject = core::ptr::null_mut();
    v_res_4392_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7(v_msg_4383_, v_declHint_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
    lean_dec(v___y_4390_);
    lean_dec_ref(v___y_4389_);
    lean_dec(v___y_4388_);
    lean_dec_ref(v___y_4387_);
    lean_dec(v___y_4386_);
    lean_dec_ref(v___y_4385_);
    return v_res_4392_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_4393_: *mut LeanObject,
    mut v_msg_4394_: *mut LeanObject,
    mut v_declHint_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
    mut v___y_4399_: *mut LeanObject,
    mut v___y_4400_: *mut LeanObject,
    mut v___y_4401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    v___x_4403_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7(v_msg_4394_, v_declHint_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
    v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
    lean_inc(v_a_4404_);
    lean_dec_ref(v___x_4403_);
    v___x_4405_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__8___redArg(v_ref_4393_, v_a_4404_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
    return v___x_4405_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_4406_: *mut LeanObject,
    mut v_msg_4407_: *mut LeanObject,
    mut v_declHint_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
    mut v___y_4411_: *mut LeanObject,
    mut v___y_4412_: *mut LeanObject,
    mut v___y_4413_: *mut LeanObject,
    mut v___y_4414_: *mut LeanObject,
    mut v___y_4415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4416_: *mut LeanObject = core::ptr::null_mut();
    v_res_4416_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_4406_, v_msg_4407_, v_declHint_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_);
    lean_dec(v___y_4414_);
    lean_dec_ref(v___y_4413_);
    lean_dec(v___y_4412_);
    lean_dec_ref(v___y_4411_);
    lean_dec(v___y_4410_);
    lean_dec_ref(v___y_4409_);
    lean_dec(v_ref_4406_);
    return v_res_4416_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    v___x_4418_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_4419_ = l_Lean_stringToMessageData(v___x_4418_);
    return v___x_4419_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    v___x_4421_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_4422_ = l_Lean_stringToMessageData(v___x_4421_);
    return v___x_4422_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg(
    mut v_ref_4423_: *mut LeanObject,
    mut v_constName_4424_: *mut LeanObject,
    mut v___y_4425_: *mut LeanObject,
    mut v___y_4426_: *mut LeanObject,
    mut v___y_4427_: *mut LeanObject,
    mut v___y_4428_: *mut LeanObject,
    mut v___y_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: u8 = 0;
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    v___x_4432_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_4433_ = 0;
    lean_inc(v_constName_4424_);
    v___x_4434_ = l_Lean_MessageData_ofConstName(v_constName_4424_, v___x_4433_);
    v___x_4435_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4435_, 0, v___x_4432_);
    lean_ctor_set(v___x_4435_, 1, v___x_4434_);
    v___x_4436_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_4437_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4437_, 0, v___x_4435_);
    lean_ctor_set(v___x_4437_, 1, v___x_4436_);
    v___x_4438_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_4423_, v___x_4437_, v_constName_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
    return v___x_4438_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_4439_: *mut LeanObject,
    mut v_constName_4440_: *mut LeanObject,
    mut v___y_4441_: *mut LeanObject,
    mut v___y_4442_: *mut LeanObject,
    mut v___y_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
    mut v___y_4445_: *mut LeanObject,
    mut v___y_4446_: *mut LeanObject,
    mut v___y_4447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4448_: *mut LeanObject = core::ptr::null_mut();
    v_res_4448_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg(v_ref_4439_, v_constName_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
    lean_dec(v___y_4446_);
    lean_dec_ref(v___y_4445_);
    lean_dec(v___y_4444_);
    lean_dec_ref(v___y_4443_);
    lean_dec(v___y_4442_);
    lean_dec_ref(v___y_4441_);
    lean_dec(v_ref_4439_);
    return v_res_4448_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0___redArg(
    mut v_constName_4449_: *mut LeanObject,
    mut v___y_4450_: *mut LeanObject,
    mut v___y_4451_: *mut LeanObject,
    mut v___y_4452_: *mut LeanObject,
    mut v___y_4453_: *mut LeanObject,
    mut v___y_4454_: *mut LeanObject,
    mut v___y_4455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    v_ref_4457_ = lean_ctor_get(v___y_4454_, 5);
    v___x_4458_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg(v_ref_4457_, v_constName_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
    return v___x_4458_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0___redArg___boxed(
    mut v_constName_4459_: *mut LeanObject,
    mut v___y_4460_: *mut LeanObject,
    mut v___y_4461_: *mut LeanObject,
    mut v___y_4462_: *mut LeanObject,
    mut v___y_4463_: *mut LeanObject,
    mut v___y_4464_: *mut LeanObject,
    mut v___y_4465_: *mut LeanObject,
    mut v___y_4466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4467_: *mut LeanObject = core::ptr::null_mut();
    v_res_4467_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0___redArg(v_constName_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
    lean_dec(v___y_4465_);
    lean_dec_ref(v___y_4464_);
    lean_dec(v___y_4463_);
    lean_dec_ref(v___y_4462_);
    lean_dec(v___y_4461_);
    lean_dec_ref(v___y_4460_);
    return v_res_4467_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0(
    mut v_constName_4468_: *mut LeanObject,
    mut v___y_4469_: *mut LeanObject,
    mut v___y_4470_: *mut LeanObject,
    mut v___y_4471_: *mut LeanObject,
    mut v___y_4472_: *mut LeanObject,
    mut v___y_4473_: *mut LeanObject,
    mut v___y_4474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: u8 = 0;
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4484_: u8 = 0;
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4476_ = lean_st_ref_get(v___y_4474_);
                v_env_4477_ = lean_ctor_get(v___x_4476_, 0);
                lean_inc_ref(v_env_4477_);
                lean_dec(v___x_4476_);
                v___x_4478_ = 0;
                lean_inc(v_constName_4468_);
                v___x_4479_ =
                    l_Lean_Environment_find_x3f(v_env_4477_, v_constName_4468_, v___x_4478_);
                if lean_obj_tag(v___x_4479_) == 0 {
                    v___x_4480_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0___redArg(v_constName_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_);
                    return v___x_4480_;
                } else {
                    lean_dec(v_constName_4468_);
                    v_val_4481_ = lean_ctor_get(v___x_4479_, 0);
                    v_isSharedCheck_4488_ = (!lean_is_exclusive(v___x_4479_)) as u8;
                    if v_isSharedCheck_4488_ == 0 {
                        v___x_4483_ = v___x_4479_;
                        v_isShared_4484_ = v_isSharedCheck_4488_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4481_);
                        lean_dec(v___x_4479_);
                        v___x_4483_ = lean_box(0);
                        v_isShared_4484_ = v_isSharedCheck_4488_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4484_ == 0 {
                    lean_ctor_set_tag(v___x_4483_, 0);
                    v___x_4486_ = v___x_4483_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_val_4481_);
                    v___x_4486_ = v_reuseFailAlloc_4487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0___boxed(
    mut v_constName_4489_: *mut LeanObject,
    mut v___y_4490_: *mut LeanObject,
    mut v___y_4491_: *mut LeanObject,
    mut v___y_4492_: *mut LeanObject,
    mut v___y_4493_: *mut LeanObject,
    mut v___y_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
    mut v___y_4496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4497_: *mut LeanObject = core::ptr::null_mut();
    v_res_4497_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0(v_constName_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
    lean_dec(v___y_4495_);
    lean_dec_ref(v___y_4494_);
    lean_dec(v___y_4493_);
    lean_dec_ref(v___y_4492_);
    lean_dec(v___y_4491_);
    lean_dec_ref(v___y_4490_);
    return v_res_4497_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__1()
-> *mut LeanObject {
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    v___x_4499_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__0;
    v___x_4500_ = l_Lean_stringToMessageData(v___x_4499_);
    return v___x_4500_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__3()
-> *mut LeanObject {
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    v___x_4502_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__2;
    v___x_4503_ = l_Lean_stringToMessageData(v___x_4502_);
    return v___x_4503_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__5()
-> *mut LeanObject {
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    v___x_4505_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__4;
    v___x_4506_ = l_Lean_stringToMessageData(v___x_4505_);
    return v___x_4506_;
}
pub unsafe fn _init_l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__7()
-> *mut LeanObject {
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    v___x_4508_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__6;
    v___x_4509_ = l_Lean_stringToMessageData(v___x_4508_);
    return v___x_4509_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType(
    mut v_typeRef_4510_: *mut LeanObject,
    mut v_type_4511_: *mut LeanObject,
    mut v_a_4512_: *mut LeanObject,
    mut v_a_4513_: *mut LeanObject,
    mut v_a_4514_: *mut LeanObject,
    mut v_a_4515_: *mut LeanObject,
    mut v_a_4516_: *mut LeanObject,
    mut v_a_4517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4531_: u8 = 0;
    let mut v_cancelTk_x3f_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4533_: u8 = 0;
    let mut v_inheritedTraceOptions_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4545_: u8 = 0;
    let mut v_val_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4554_: u8 = 0;
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: u8 = 0;
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4568_: u8 = 0;
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4572_: u8 = 0;
    let mut v_toConstantVal_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isReflexive_4576_: u8 = 0;
    let mut v___y_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: u8 = 0;
    let mut v___y_4586_: u8 = 0;
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4596_: u8 = 0;
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4600_: u8 = 0;
    let mut v___y_4602_: u8 = 0;
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: u8 = 0;
    let mut v_levelParams_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: u8 = 0;
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: u8 = 0;
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: u8 = 0;
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4616_: u8 = 0;
    let mut v_a_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4620_: u8 = 0;
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4624_: u8 = 0;
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4634_: u8 = 0;
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4519_ = lean_ctor_get(v_a_4516_, 0);
                v_fileMap_4520_ = lean_ctor_get(v_a_4516_, 1);
                v_options_4521_ = lean_ctor_get(v_a_4516_, 2);
                v_currRecDepth_4522_ = lean_ctor_get(v_a_4516_, 3);
                v_maxRecDepth_4523_ = lean_ctor_get(v_a_4516_, 4);
                v_ref_4524_ = lean_ctor_get(v_a_4516_, 5);
                v_currNamespace_4525_ = lean_ctor_get(v_a_4516_, 6);
                v_openDecls_4526_ = lean_ctor_get(v_a_4516_, 7);
                v_initHeartbeats_4527_ = lean_ctor_get(v_a_4516_, 8);
                v_maxHeartbeats_4528_ = lean_ctor_get(v_a_4516_, 9);
                v_quotContext_4529_ = lean_ctor_get(v_a_4516_, 10);
                v_currMacroScope_4530_ = lean_ctor_get(v_a_4516_, 11);
                v_diag_4531_ = lean_ctor_get_uint8(
                    v_a_4516_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4532_ = lean_ctor_get(v_a_4516_, 12);
                v_suppressElabErrors_4533_ = lean_ctor_get_uint8(
                    v_a_4516_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4534_ = lean_ctor_get(v_a_4516_, 13);
                v_ref_4535_ = l_Lean_replaceRef(v_typeRef_4510_, v_ref_4524_);
                lean_inc_ref(v_inheritedTraceOptions_4534_);
                lean_inc(v_cancelTk_x3f_4532_);
                lean_inc(v_currMacroScope_4530_);
                lean_inc(v_quotContext_4529_);
                lean_inc(v_maxHeartbeats_4528_);
                lean_inc(v_initHeartbeats_4527_);
                lean_inc(v_openDecls_4526_);
                lean_inc(v_currNamespace_4525_);
                lean_inc(v_maxRecDepth_4523_);
                lean_inc(v_currRecDepth_4522_);
                lean_inc_ref(v_options_4521_);
                lean_inc_ref(v_fileMap_4520_);
                lean_inc_ref(v_fileName_4519_);
                v___x_4536_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4536_, 0, v_fileName_4519_);
                lean_ctor_set(v___x_4536_, 1, v_fileMap_4520_);
                lean_ctor_set(v___x_4536_, 2, v_options_4521_);
                lean_ctor_set(v___x_4536_, 3, v_currRecDepth_4522_);
                lean_ctor_set(v___x_4536_, 4, v_maxRecDepth_4523_);
                lean_ctor_set(v___x_4536_, 5, v_ref_4535_);
                lean_ctor_set(v___x_4536_, 6, v_currNamespace_4525_);
                lean_ctor_set(v___x_4536_, 7, v_openDecls_4526_);
                lean_ctor_set(v___x_4536_, 8, v_initHeartbeats_4527_);
                lean_ctor_set(v___x_4536_, 9, v_maxHeartbeats_4528_);
                lean_ctor_set(v___x_4536_, 10, v_quotContext_4529_);
                lean_ctor_set(v___x_4536_, 11, v_currMacroScope_4530_);
                lean_ctor_set(v___x_4536_, 12, v_cancelTk_x3f_4532_);
                lean_ctor_set(v___x_4536_, 13, v_inheritedTraceOptions_4534_);
                lean_ctor_set_uint8(
                    v___x_4536_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_4531_,
                );
                lean_ctor_set_uint8(
                    v___x_4536_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4533_,
                );
                lean_inc_ref(v_type_4511_);
                v___x_4537_ =
                    l_Lean_Meta_whnfR(v_type_4511_, v_a_4514_, v_a_4515_, v___x_4536_, v_a_4517_);
                if lean_obj_tag(v___x_4537_) == 0 {
                    v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
                    lean_inc(v_a_4538_);
                    lean_dec_ref_known(v___x_4537_, 1);
                    v___x_4539_ = l_Lean_Expr_constName_x3f(v_a_4538_);
                    lean_dec(v_a_4538_);
                    if lean_obj_tag(v___x_4539_) == 1 {
                        lean_dec_ref(v_type_4511_);
                        v_val_4540_ = lean_ctor_get(v___x_4539_, 0);
                        lean_inc_n(v_val_4540_, 2);
                        lean_dec_ref_known(v___x_4539_, 1);
                        v___x_4541_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0(v_val_4540_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v___x_4536_, v_a_4517_);
                        if lean_obj_tag(v___x_4541_) == 0 {
                            v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
                            v_isSharedCheck_4616_ = (!lean_is_exclusive(v___x_4541_)) as u8;
                            if v_isSharedCheck_4616_ == 0 {
                                v___x_4544_ = v___x_4541_;
                                v_isShared_4545_ = v_isSharedCheck_4616_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_4542_);
                                lean_dec(v___x_4541_);
                                v___x_4544_ = lean_box(0);
                                v_isShared_4545_ = v_isSharedCheck_4616_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_4540_);
                            lean_dec_ref_known(v___x_4536_, 14);
                            v_a_4617_ = lean_ctor_get(v___x_4541_, 0);
                            v_isSharedCheck_4624_ = (!lean_is_exclusive(v___x_4541_)) as u8;
                            if v_isSharedCheck_4624_ == 0 {
                                v___x_4619_ = v___x_4541_;
                                v_isShared_4620_ = v_isSharedCheck_4624_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_4617_);
                                lean_dec(v___x_4541_);
                                v___x_4619_ = lean_box(0);
                                v_isShared_4620_ = v_isSharedCheck_4624_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_4539_);
                        v___x_4625_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3);
                        v___x_4626_ = l_Lean_MessageData_ofExpr(v_type_4511_);
                        v___x_4627_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4627_, 0, v___x_4625_);
                        lean_ctor_set(v___x_4627_, 1, v___x_4626_);
                        v___x_4628_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__7_once), _init_l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__7);
                        v___x_4629_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4629_, 0, v___x_4627_);
                        lean_ctor_set(v___x_4629_, 1, v___x_4628_);
                        v___x_4630_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___redArg(v___x_4629_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v___x_4536_, v_a_4517_);
                        lean_dec_ref_known(v___x_4536_, 14);
                        return v___x_4630_;
                    }
                } else {
                    lean_dec_ref_known(v___x_4536_, 14);
                    lean_dec_ref(v_type_4511_);
                    v_a_4631_ = lean_ctor_get(v___x_4537_, 0);
                    v_isSharedCheck_4638_ = (!lean_is_exclusive(v___x_4537_)) as u8;
                    if v_isSharedCheck_4638_ == 0 {
                        v___x_4633_ = v___x_4537_;
                        v_isShared_4634_ = v_isSharedCheck_4638_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_4631_);
                        lean_dec(v___x_4537_);
                        v___x_4633_ = lean_box(0);
                        v_isShared_4634_ = v_isSharedCheck_4638_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_4542_) == 5 {
                    v_val_4546_ = lean_ctor_get(v_a_4542_, 0);
                    lean_inc_ref(v_val_4546_);
                    lean_dec_ref_known(v_a_4542_, 1);
                    v_toConstantVal_4573_ = lean_ctor_get(v_val_4546_, 0);
                    v_numParams_4574_ = lean_ctor_get(v_val_4546_, 1);
                    v_numIndices_4575_ = lean_ctor_get(v_val_4546_, 2);
                    v_isReflexive_4576_ = lean_ctor_get_uint8(
                        v_val_4546_,
                        (core::mem::size_of::<*mut LeanObject>() * 6 + 2) as u32,
                    );
                    v_levelParams_4605_ = lean_ctor_get(v_toConstantVal_4573_, 1);
                    v___x_4606_ = l_List_isEmpty___redArg(v_levelParams_4605_);
                    if v___x_4606_ == 0 {
                        v___y_4602_ = v___x_4606_;
                        state = 10;
                        continue;
                    } else {
                        v___x_4607_ = lean_unsigned_to_nat(0);
                        v___x_4608_ = lean_nat_dec_eq(v_numParams_4574_, v___x_4607_);
                        v___y_4602_ = v___x_4608_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4544_);
                    lean_dec(v_a_4542_);
                    v___x_4609_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3);
                    v___x_4610_ = 0;
                    v___x_4611_ = l_Lean_MessageData_ofConstName(v_val_4540_, v___x_4610_);
                    v___x_4612_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4612_, 0, v___x_4609_);
                    lean_ctor_set(v___x_4612_, 1, v___x_4611_);
                    v___x_4613_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__5_once), _init_l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__5);
                    v___x_4614_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4614_, 0, v___x_4612_);
                    lean_ctor_set(v___x_4614_, 1, v___x_4613_);
                    v___x_4615_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___redArg(v___x_4614_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v___x_4536_, v_a_4517_);
                    lean_dec_ref_known(v___x_4536_, 14);
                    return v___x_4615_;
                }
            }
            2 => {
                if v___y_4554_ == 0 {
                    lean_dec_ref(v___y_4553_);
                    lean_dec(v_val_4540_);
                    if v_isShared_4545_ == 0 {
                        lean_ctor_set(v___x_4544_, 0, v_val_4546_);
                        v___x_4556_ = v___x_4544_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_val_4546_);
                        v___x_4556_ = v_reuseFailAlloc_4557_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_val_4546_);
                    lean_del_object(v___x_4544_);
                    v___x_4558_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3);
                    v___x_4559_ = 0;
                    v___x_4560_ = l_Lean_MessageData_ofConstName(v_val_4540_, v___x_4559_);
                    v___x_4561_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4561_, 0, v___x_4558_);
                    lean_ctor_set(v___x_4561_, 1, v___x_4560_);
                    v___x_4562_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__1_once), _init_l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__1);
                    v___x_4563_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4563_, 0, v___x_4561_);
                    lean_ctor_set(v___x_4563_, 1, v___x_4562_);
                    v___x_4564_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___redArg(v___x_4563_, v___y_4552_, v___y_4550_, v___y_4548_, v___y_4551_, v___y_4553_, v___y_4549_);
                    lean_dec_ref(v___y_4553_);
                    v_a_4565_ = lean_ctor_get(v___x_4564_, 0);
                    v_isSharedCheck_4572_ = (!lean_is_exclusive(v___x_4564_)) as u8;
                    if v_isSharedCheck_4572_ == 0 {
                        v___x_4567_ = v___x_4564_;
                        v_isShared_4568_ = v_isSharedCheck_4572_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4565_);
                        lean_dec(v___x_4564_);
                        v___x_4567_ = lean_box(0);
                        v_isShared_4568_ = v_isSharedCheck_4572_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4556_;
            }
            4 => {
                if v_isShared_4568_ == 0 {
                    v___x_4570_ = v___x_4567_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4565_);
                    v___x_4570_ = v_reuseFailAlloc_4571_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4570_;
            }
            6 => {
                v___x_4584_ = l_Lean_InductiveVal_isNested(v_val_4546_);
                if v___x_4584_ == 0 {
                    v___y_4548_ = v___y_4580_;
                    v___y_4549_ = v___y_4583_;
                    v___y_4550_ = v___y_4579_;
                    v___y_4551_ = v___y_4581_;
                    v___y_4552_ = v___y_4578_;
                    v___y_4553_ = v___y_4582_;
                    v___y_4554_ = v_isReflexive_4576_;
                    state = 2;
                    continue;
                } else {
                    v___y_4548_ = v___y_4580_;
                    v___y_4549_ = v___y_4583_;
                    v___y_4550_ = v___y_4579_;
                    v___y_4551_ = v___y_4581_;
                    v___y_4552_ = v___y_4578_;
                    v___y_4553_ = v___y_4582_;
                    v___y_4554_ = v___x_4584_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v___x_4587_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3);
                v___x_4588_ = l_Lean_MessageData_ofConstName(v_val_4540_, v___y_4586_);
                v___x_4589_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4589_, 0, v___x_4587_);
                lean_ctor_set(v___x_4589_, 1, v___x_4588_);
                v___x_4590_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__3_once), _init_l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___closed__3);
                v___x_4591_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4591_, 0, v___x_4589_);
                lean_ctor_set(v___x_4591_, 1, v___x_4590_);
                v___x_4592_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___redArg(v___x_4591_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v___x_4536_, v_a_4517_);
                lean_dec_ref_known(v___x_4536_, 14);
                v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
                v_isSharedCheck_4600_ = (!lean_is_exclusive(v___x_4592_)) as u8;
                if v_isSharedCheck_4600_ == 0 {
                    v___x_4595_ = v___x_4592_;
                    v_isShared_4596_ = v_isSharedCheck_4600_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_a_4593_);
                    lean_dec(v___x_4592_);
                    v___x_4595_ = lean_box(0);
                    v_isShared_4596_ = v_isSharedCheck_4600_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4596_ == 0 {
                    v___x_4598_ = v___x_4595_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
                    v___x_4598_ = v_reuseFailAlloc_4599_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4598_;
            }
            10 => {
                if v___y_4602_ == 0 {
                    lean_dec_ref(v_val_4546_);
                    lean_del_object(v___x_4544_);
                    v___y_4586_ = v___y_4602_;
                    state = 7;
                    continue;
                } else {
                    v___x_4603_ = lean_unsigned_to_nat(0);
                    v___x_4604_ = lean_nat_dec_eq(v_numIndices_4575_, v___x_4603_);
                    if v___x_4604_ == 0 {
                        lean_dec_ref(v_val_4546_);
                        lean_del_object(v___x_4544_);
                        v___y_4586_ = v___x_4604_;
                        state = 7;
                        continue;
                    } else {
                        v___y_4578_ = v_a_4512_;
                        v___y_4579_ = v_a_4513_;
                        v___y_4580_ = v_a_4514_;
                        v___y_4581_ = v_a_4515_;
                        v___y_4582_ = v___x_4536_;
                        v___y_4583_ = v_a_4517_;
                        state = 6;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_4620_ == 0 {
                    v___x_4622_ = v___x_4619_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
                    v___x_4622_ = v_reuseFailAlloc_4623_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4622_;
            }
            13 => {
                if v_isShared_4634_ == 0 {
                    v___x_4636_ = v___x_4633_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
                    v___x_4636_ = v_reuseFailAlloc_4637_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4636_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType___boxed(
    mut v_typeRef_4639_: *mut LeanObject,
    mut v_type_4640_: *mut LeanObject,
    mut v_a_4641_: *mut LeanObject,
    mut v_a_4642_: *mut LeanObject,
    mut v_a_4643_: *mut LeanObject,
    mut v_a_4644_: *mut LeanObject,
    mut v_a_4645_: *mut LeanObject,
    mut v_a_4646_: *mut LeanObject,
    mut v_a_4647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4648_: *mut LeanObject = core::ptr::null_mut();
    v_res_4648_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType(v_typeRef_4639_, v_type_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_);
    lean_dec(v_a_4646_);
    lean_dec_ref(v_a_4645_);
    lean_dec(v_a_4644_);
    lean_dec_ref(v_a_4643_);
    lean_dec(v_a_4642_);
    lean_dec_ref(v_a_4641_);
    lean_dec(v_typeRef_4639_);
    return v_res_4648_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1(
    mut v_00_u03b1_4649_: *mut LeanObject,
    mut v_msg_4650_: *mut LeanObject,
    mut v___y_4651_: *mut LeanObject,
    mut v___y_4652_: *mut LeanObject,
    mut v___y_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
    mut v___y_4655_: *mut LeanObject,
    mut v___y_4656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    v___x_4658_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___redArg(v_msg_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
    return v___x_4658_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___boxed(
    mut v_00_u03b1_4659_: *mut LeanObject,
    mut v_msg_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
    mut v___y_4662_: *mut LeanObject,
    mut v___y_4663_: *mut LeanObject,
    mut v___y_4664_: *mut LeanObject,
    mut v___y_4665_: *mut LeanObject,
    mut v___y_4666_: *mut LeanObject,
    mut v___y_4667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4668_: *mut LeanObject = core::ptr::null_mut();
    v_res_4668_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1(v_00_u03b1_4659_, v_msg_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
    lean_dec(v___y_4666_);
    lean_dec_ref(v___y_4665_);
    lean_dec(v___y_4664_);
    lean_dec_ref(v___y_4663_);
    lean_dec(v___y_4662_);
    lean_dec_ref(v___y_4661_);
    return v_res_4668_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0(
    mut v_00_u03b1_4669_: *mut LeanObject,
    mut v_constName_4670_: *mut LeanObject,
    mut v___y_4671_: *mut LeanObject,
    mut v___y_4672_: *mut LeanObject,
    mut v___y_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
    mut v___y_4676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    v___x_4678_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0___redArg(v_constName_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
    return v___x_4678_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0___boxed(
    mut v_00_u03b1_4679_: *mut LeanObject,
    mut v_constName_4680_: *mut LeanObject,
    mut v___y_4681_: *mut LeanObject,
    mut v___y_4682_: *mut LeanObject,
    mut v___y_4683_: *mut LeanObject,
    mut v___y_4684_: *mut LeanObject,
    mut v___y_4685_: *mut LeanObject,
    mut v___y_4686_: *mut LeanObject,
    mut v___y_4687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4688_: *mut LeanObject = core::ptr::null_mut();
    v_res_4688_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0(v_00_u03b1_4679_, v_constName_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_);
    lean_dec(v___y_4686_);
    lean_dec_ref(v___y_4685_);
    lean_dec(v___y_4684_);
    lean_dec_ref(v___y_4683_);
    lean_dec(v___y_4682_);
    lean_dec_ref(v___y_4681_);
    return v_res_4688_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3(
    mut v_msgData_4689_: *mut LeanObject,
    mut v_macroStack_4690_: *mut LeanObject,
    mut v___y_4691_: *mut LeanObject,
    mut v___y_4692_: *mut LeanObject,
    mut v___y_4693_: *mut LeanObject,
    mut v___y_4694_: *mut LeanObject,
    mut v___y_4695_: *mut LeanObject,
    mut v___y_4696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    v___x_4698_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___redArg(v_msgData_4689_, v_macroStack_4690_, v___y_4695_);
    return v___x_4698_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3___boxed(
    mut v_msgData_4699_: *mut LeanObject,
    mut v_macroStack_4700_: *mut LeanObject,
    mut v___y_4701_: *mut LeanObject,
    mut v___y_4702_: *mut LeanObject,
    mut v___y_4703_: *mut LeanObject,
    mut v___y_4704_: *mut LeanObject,
    mut v___y_4705_: *mut LeanObject,
    mut v___y_4706_: *mut LeanObject,
    mut v___y_4707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4708_: *mut LeanObject = core::ptr::null_mut();
    v_res_4708_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__3(v_msgData_4699_, v_macroStack_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
    lean_dec(v___y_4706_);
    lean_dec_ref(v___y_4705_);
    lean_dec(v___y_4704_);
    lean_dec_ref(v___y_4703_);
    lean_dec(v___y_4702_);
    lean_dec_ref(v___y_4701_);
    return v_res_4708_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4709_: *mut LeanObject,
    mut v_ref_4710_: *mut LeanObject,
    mut v_constName_4711_: *mut LeanObject,
    mut v___y_4712_: *mut LeanObject,
    mut v___y_4713_: *mut LeanObject,
    mut v___y_4714_: *mut LeanObject,
    mut v___y_4715_: *mut LeanObject,
    mut v___y_4716_: *mut LeanObject,
    mut v___y_4717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    v___x_4719_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg(v_ref_4710_, v_constName_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_);
    return v___x_4719_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4720_: *mut LeanObject,
    mut v_ref_4721_: *mut LeanObject,
    mut v_constName_4722_: *mut LeanObject,
    mut v___y_4723_: *mut LeanObject,
    mut v___y_4724_: *mut LeanObject,
    mut v___y_4725_: *mut LeanObject,
    mut v___y_4726_: *mut LeanObject,
    mut v___y_4727_: *mut LeanObject,
    mut v___y_4728_: *mut LeanObject,
    mut v___y_4729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4730_: *mut LeanObject = core::ptr::null_mut();
    v_res_4730_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1(v_00_u03b1_4720_, v_ref_4721_, v_constName_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
    lean_dec(v___y_4728_);
    lean_dec_ref(v___y_4727_);
    lean_dec(v___y_4726_);
    lean_dec_ref(v___y_4725_);
    lean_dec(v___y_4724_);
    lean_dec_ref(v___y_4723_);
    lean_dec(v_ref_4721_);
    return v_res_4730_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_4731_: *mut LeanObject,
    mut v_ref_4732_: *mut LeanObject,
    mut v_msg_4733_: *mut LeanObject,
    mut v_declHint_4734_: *mut LeanObject,
    mut v___y_4735_: *mut LeanObject,
    mut v___y_4736_: *mut LeanObject,
    mut v___y_4737_: *mut LeanObject,
    mut v___y_4738_: *mut LeanObject,
    mut v___y_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    v___x_4742_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_4732_, v_msg_4733_, v_declHint_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_);
    return v___x_4742_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_4743_: *mut LeanObject,
    mut v_ref_4744_: *mut LeanObject,
    mut v_msg_4745_: *mut LeanObject,
    mut v_declHint_4746_: *mut LeanObject,
    mut v___y_4747_: *mut LeanObject,
    mut v___y_4748_: *mut LeanObject,
    mut v___y_4749_: *mut LeanObject,
    mut v___y_4750_: *mut LeanObject,
    mut v___y_4751_: *mut LeanObject,
    mut v___y_4752_: *mut LeanObject,
    mut v___y_4753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4754_: *mut LeanObject = core::ptr::null_mut();
    v_res_4754_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4743_, v_ref_4744_, v_msg_4745_, v_declHint_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
    lean_dec(v___y_4752_);
    lean_dec_ref(v___y_4751_);
    lean_dec(v___y_4750_);
    lean_dec_ref(v___y_4749_);
    lean_dec(v___y_4748_);
    lean_dec_ref(v___y_4747_);
    lean_dec(v_ref_4744_);
    return v_res_4754_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9(
    mut v_msg_4755_: *mut LeanObject,
    mut v_declHint_4756_: *mut LeanObject,
    mut v___y_4757_: *mut LeanObject,
    mut v___y_4758_: *mut LeanObject,
    mut v___y_4759_: *mut LeanObject,
    mut v___y_4760_: *mut LeanObject,
    mut v___y_4761_: *mut LeanObject,
    mut v___y_4762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    v___x_4764_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_msg_4755_, v_declHint_4756_, v___y_4762_);
    return v___x_4764_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___boxed(
    mut v_msg_4765_: *mut LeanObject,
    mut v_declHint_4766_: *mut LeanObject,
    mut v___y_4767_: *mut LeanObject,
    mut v___y_4768_: *mut LeanObject,
    mut v___y_4769_: *mut LeanObject,
    mut v___y_4770_: *mut LeanObject,
    mut v___y_4771_: *mut LeanObject,
    mut v___y_4772_: *mut LeanObject,
    mut v___y_4773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4774_: *mut LeanObject = core::ptr::null_mut();
    v_res_4774_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9(v_msg_4765_, v_declHint_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_);
    lean_dec(v___y_4772_);
    lean_dec_ref(v___y_4771_);
    lean_dec(v___y_4770_);
    lean_dec_ref(v___y_4769_);
    lean_dec(v___y_4768_);
    lean_dec_ref(v___y_4767_);
    return v_res_4774_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__8(
    mut v_00_u03b1_4775_: *mut LeanObject,
    mut v_ref_4776_: *mut LeanObject,
    mut v_msg_4777_: *mut LeanObject,
    mut v___y_4778_: *mut LeanObject,
    mut v___y_4779_: *mut LeanObject,
    mut v___y_4780_: *mut LeanObject,
    mut v___y_4781_: *mut LeanObject,
    mut v___y_4782_: *mut LeanObject,
    mut v___y_4783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    v___x_4785_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__8___redArg(v_ref_4776_, v_msg_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
    return v___x_4785_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__8___boxed(
    mut v_00_u03b1_4786_: *mut LeanObject,
    mut v_ref_4787_: *mut LeanObject,
    mut v_msg_4788_: *mut LeanObject,
    mut v___y_4789_: *mut LeanObject,
    mut v___y_4790_: *mut LeanObject,
    mut v___y_4791_: *mut LeanObject,
    mut v___y_4792_: *mut LeanObject,
    mut v___y_4793_: *mut LeanObject,
    mut v___y_4794_: *mut LeanObject,
    mut v___y_4795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4796_: *mut LeanObject = core::ptr::null_mut();
    v_res_4796_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__8(v_00_u03b1_4786_, v_ref_4787_, v_msg_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_);
    lean_dec(v___y_4794_);
    lean_dec_ref(v___y_4793_);
    lean_dec(v___y_4792_);
    lean_dec_ref(v___y_4791_);
    lean_dec(v___y_4790_);
    lean_dec_ref(v___y_4789_);
    lean_dec(v_ref_4787_);
    return v_res_4796_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_useCtor(
    mut v_ival_4797_: *mut LeanObject,
    mut v_ctorName_4798_: *mut LeanObject,
) -> u8 {
    let mut v___y_4800_: u8 = 0;
    let mut v___x_4801_: u8 = 0;
    let mut v_toConstantVal_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: u8 = 0;
    let mut v___x_4806_: u8 = 0;
    let mut v___x_4807_: u8 = 0;
    let mut v___x_4808_: u8 = 0;
    let mut v___x_4809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4807_ = l_Lean_Name_isStr(v_ctorName_4798_);
                if v___x_4807_ == 0 {
                    v___y_4800_ = v___x_4807_;
                    state = 1;
                    continue;
                } else {
                    v___x_4808_ = l_Lean_Name_hasMacroScopes(v_ctorName_4798_);
                    if v___x_4808_ == 0 {
                        v___y_4800_ = v___x_4807_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4809_ = 0;
                        return v___x_4809_;
                    }
                }
            }
            1 => {
                if v___y_4800_ == 0 {
                    return v___y_4800_;
                } else {
                    v___x_4801_ = l_Lean_isPrivateName(v_ctorName_4798_);
                    if v___x_4801_ == 0 {
                        v_toConstantVal_4802_ = lean_ctor_get(v_ival_4797_, 0);
                        v_name_4803_ = lean_ctor_get(v_toConstantVal_4802_, 0);
                        v___x_4804_ = l_Lean_Name_getPrefix(v_ctorName_4798_);
                        v___x_4805_ = lean_name_eq(v___x_4804_, v_name_4803_);
                        lean_dec(v___x_4804_);
                        return v___x_4805_;
                    } else {
                        v___x_4806_ = 0;
                        return v___x_4806_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_useCtor___boxed(
    mut v_ival_4810_: *mut LeanObject,
    mut v_ctorName_4811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4812_: u8 = 0;
    let mut v_r_4813_: *mut LeanObject = core::ptr::null_mut();
    v_res_4812_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_useCtor(v_ival_4810_, v_ctorName_4811_);
    lean_dec(v_ctorName_4811_);
    lean_dec_ref(v_ival_4810_);
    v_r_4813_ = lean_box((v_res_4812_) as usize);
    return v_r_4813_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    v___x_4815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__0;
    v___x_4816_ = l_Lean_stringToMessageData(v___x_4815_);
    return v___x_4816_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    v___x_4818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__2;
    v___x_4819_ = l_Lean_stringToMessageData(v___x_4818_);
    return v___x_4819_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    v___x_4821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__4;
    v___x_4822_ = l_Lean_stringToMessageData(v___x_4821_);
    return v___x_4822_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0(
    mut v_type_4823_: *mut LeanObject,
    mut v_a_4824_: *mut LeanObject,
    mut v_as_4825_: *mut LeanObject,
    mut v_sz_4826_: usize,
    mut v_i_4827_: usize,
    mut v_b_4828_: *mut LeanObject,
    mut v___y_4829_: *mut LeanObject,
    mut v___y_4830_: *mut LeanObject,
    mut v___y_4831_: *mut LeanObject,
    mut v___y_4832_: *mut LeanObject,
    mut v___y_4833_: *mut LeanObject,
    mut v___y_4834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: usize = 0;
    let mut v___x_4839_: usize = 0;
    let mut v___x_4841_: u8 = 0;
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: u8 = 0;
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: u8 = 0;
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: u8 = 0;
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4864_: u8 = 0;
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4868_: u8 = 0;
    let mut v_a_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4872_: u8 = 0;
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4876_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4841_ = lean_usize_dec_lt(v_i_4827_, v_sz_4826_);
                if v___x_4841_ == 0 {
                    lean_dec(v_a_4824_);
                    v___x_4842_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4842_, 0, v_b_4828_);
                    return v___x_4842_;
                } else {
                    v_a_4843_ = lean_array_uget_borrowed(v_as_4825_, v_i_4827_);
                    lean_inc(v___y_4834_);
                    lean_inc_ref(v___y_4833_);
                    lean_inc(v___y_4832_);
                    lean_inc_ref(v___y_4831_);
                    lean_inc(v_a_4843_);
                    v___x_4844_ = lean_infer_type(
                        v_a_4843_,
                        v___y_4831_,
                        v___y_4832_,
                        v___y_4833_,
                        v___y_4834_,
                    );
                    if lean_obj_tag(v___x_4844_) == 0 {
                        v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
                        lean_inc(v_a_4845_);
                        lean_dec_ref_known(v___x_4844_, 1);
                        v___x_4849_ = l_Lean_Expr_hasMVar(v_a_4845_);
                        if v___x_4849_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___x_4850_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__1);
                            lean_inc(v_a_4843_);
                            v___x_4851_ = l_Lean_MessageData_ofExpr(v_a_4843_);
                            v___x_4852_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4852_, 0, v___x_4850_);
                            lean_ctor_set(v___x_4852_, 1, v___x_4851_);
                            v___x_4853_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__3);
                            v___x_4854_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4854_, 0, v___x_4852_);
                            lean_ctor_set(v___x_4854_, 1, v___x_4853_);
                            v___x_4855_ = 0;
                            lean_inc(v_a_4824_);
                            v___x_4856_ = l_Lean_MessageData_ofConstName(v_a_4824_, v___x_4855_);
                            v___x_4857_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4857_, 0, v___x_4854_);
                            lean_ctor_set(v___x_4857_, 1, v___x_4856_);
                            v___x_4858_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___closed__5);
                            v___x_4859_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4859_, 0, v___x_4857_);
                            lean_ctor_set(v___x_4859_, 1, v___x_4858_);
                            v___x_4860_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___redArg(v___x_4859_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
                            if lean_obj_tag(v___x_4860_) == 0 {
                                lean_dec_ref_known(v___x_4860_, 1);
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_4845_);
                                lean_dec_ref(v_b_4828_);
                                lean_dec(v_a_4824_);
                                v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
                                v_isSharedCheck_4868_ = (!lean_is_exclusive(v___x_4860_)) as u8;
                                if v_isSharedCheck_4868_ == 0 {
                                    v___x_4863_ = v___x_4860_;
                                    v_isShared_4864_ = v_isSharedCheck_4868_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_4861_);
                                    lean_dec(v___x_4860_);
                                    v___x_4863_ = lean_box(0);
                                    v_isShared_4864_ = v_isSharedCheck_4868_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_4828_);
                        lean_dec(v_a_4824_);
                        v_a_4869_ = lean_ctor_get(v___x_4844_, 0);
                        v_isSharedCheck_4876_ = (!lean_is_exclusive(v___x_4844_)) as u8;
                        if v_isSharedCheck_4876_ == 0 {
                            v___x_4871_ = v___x_4844_;
                            v_isShared_4872_ = v_isSharedCheck_4876_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4869_);
                            lean_dec(v___x_4844_);
                            v___x_4871_ = lean_box(0);
                            v_isShared_4872_ = v_isSharedCheck_4876_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4838_ = 1usize;
                v___x_4839_ = lean_usize_add(v_i_4827_, v___x_4838_);
                v_i_4827_ = v___x_4839_;
                v_b_4828_ = v_a_4837_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4847_ = lean_expr_eqv(v_a_4845_, v_type_4823_);
                if v___x_4847_ == 0 {
                    v___x_4848_ = lean_array_push(v_b_4828_, v_a_4845_);
                    v_a_4837_ = v___x_4848_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_a_4845_);
                    v_a_4837_ = v_b_4828_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_4864_ == 0 {
                    v___x_4866_ = v___x_4863_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
                    v___x_4866_ = v_reuseFailAlloc_4867_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4866_;
            }
            5 => {
                if v_isShared_4872_ == 0 {
                    v___x_4874_ = v___x_4871_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4869_);
                    v___x_4874_ = v_reuseFailAlloc_4875_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0___boxed(
    mut v_type_4877_: *mut LeanObject,
    mut v_a_4878_: *mut LeanObject,
    mut v_as_4879_: *mut LeanObject,
    mut v_sz_4880_: *mut LeanObject,
    mut v_i_4881_: *mut LeanObject,
    mut v_b_4882_: *mut LeanObject,
    mut v___y_4883_: *mut LeanObject,
    mut v___y_4884_: *mut LeanObject,
    mut v___y_4885_: *mut LeanObject,
    mut v___y_4886_: *mut LeanObject,
    mut v___y_4887_: *mut LeanObject,
    mut v___y_4888_: *mut LeanObject,
    mut v___y_4889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4890_: usize = 0;
    let mut v_i_boxed_4891_: usize = 0;
    let mut v_res_4892_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4890_ = lean_unbox_usize(v_sz_4880_);
    lean_dec(v_sz_4880_);
    v_i_boxed_4891_ = lean_unbox_usize(v_i_4881_);
    lean_dec(v_i_4881_);
    v_res_4892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0(v_type_4877_, v_a_4878_, v_as_4879_, v_sz_boxed_4890_, v_i_boxed_4891_, v_b_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
    lean_dec(v___y_4888_);
    lean_dec_ref(v___y_4887_);
    lean_dec(v___y_4886_);
    lean_dec_ref(v___y_4885_);
    lean_dec(v___y_4884_);
    lean_dec_ref(v___y_4883_);
    lean_dec_ref(v_as_4879_);
    lean_dec_ref(v_type_4877_);
    return v_res_4892_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__1(
    mut v___x_4893_: u8,
    mut v_as_4894_: *mut LeanObject,
    mut v_i_4895_: usize,
    mut v_stop_4896_: usize,
) -> u8 {
    let mut v___x_4897_: u8 = 0;
    let mut v___x_4898_: u8 = 0;
    let mut v___y_4900_: u8 = 0;
    let mut v___x_4901_: usize = 0;
    let mut v___x_4902_: usize = 0;
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: u8 = 0;
    let mut v___x_4906_: u8 = 0;
    let mut v___x_4907_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4897_ = lean_usize_dec_eq(v_i_4895_, v_stop_4896_);
                if v___x_4897_ == 0 {
                    v___x_4898_ = 1;
                    v___x_4904_ = lean_array_uget_borrowed(v_as_4894_, v_i_4895_);
                    v___x_4905_ = (lean_unbox(v___x_4904_) as u8);
                    v___x_4906_ = l_Lean_BinderInfo_isExplicit(v___x_4905_);
                    if v___x_4906_ == 0 {
                        v___y_4900_ = v___x_4893_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4900_ = v___x_4897_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4907_ = 0;
                    return v___x_4907_;
                }
            }
            1 => {
                if v___y_4900_ == 0 {
                    v___x_4901_ = 1usize;
                    v___x_4902_ = lean_usize_add(v_i_4895_, v___x_4901_);
                    v_i_4895_ = v___x_4902_;
                    state = 0;
                    continue;
                } else {
                    return v___x_4898_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__1___boxed(
    mut v___x_4908_: *mut LeanObject,
    mut v_as_4909_: *mut LeanObject,
    mut v_i_4910_: *mut LeanObject,
    mut v_stop_4911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7363__boxed_4912_: u8 = 0;
    let mut v_i_boxed_4913_: usize = 0;
    let mut v_stop_boxed_4914_: usize = 0;
    let mut v_res_4915_: u8 = 0;
    let mut v_r_4916_: *mut LeanObject = core::ptr::null_mut();
    v___x_7363__boxed_4912_ = (lean_unbox(v___x_4908_) as u8);
    v_i_boxed_4913_ = lean_unbox_usize(v_i_4910_);
    lean_dec(v_i_4910_);
    v_stop_boxed_4914_ = lean_unbox_usize(v_stop_4911_);
    lean_dec(v_stop_4911_);
    v_res_4915_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__1(v___x_7363__boxed_4912_, v_as_4909_, v_i_boxed_4913_, v_stop_boxed_4914_);
    lean_dec_ref(v_as_4909_);
    v_r_4916_ = lean_box((v_res_4915_) as usize);
    return v_r_4916_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    v___x_4918_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__0;
    v___x_4919_ = l_Lean_stringToMessageData(v___x_4918_);
    return v___x_4919_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    v___x_4921_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__2;
    v___x_4922_ = l_Lean_stringToMessageData(v___x_4921_);
    return v___x_4922_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg(
    mut v_a_4923_: *mut LeanObject,
    mut v_type_4924_: *mut LeanObject,
    mut v_as_x27_4925_: *mut LeanObject,
    mut v_b_4926_: *mut LeanObject,
    mut v___y_4927_: *mut LeanObject,
    mut v___y_4928_: *mut LeanObject,
    mut v___y_4929_: *mut LeanObject,
    mut v___y_4930_: *mut LeanObject,
    mut v___y_4931_: *mut LeanObject,
    mut v___y_4932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: u8 = 0;
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: u8 = 0;
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4951_: u8 = 0;
    let mut v___y_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4959_: usize = 0;
    let mut v___x_4960_: usize = 0;
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4965_: u8 = 0;
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4976_: u8 = 0;
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4980_: u8 = 0;
    let mut v_reuseFailAlloc_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4983_: u8 = 0;
    let mut v_fst_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: u8 = 0;
    let mut v___x_4988_: usize = 0;
    let mut v___x_4989_: usize = 0;
    let mut v___x_4990_: u8 = 0;
    let mut v___x_4991_: u8 = 0;
    let mut v_isSharedCheck_4992_: u8 = 0;
    let mut v_a_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4996_: u8 = 0;
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5000_: u8 = 0;
    let mut v_a_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5004_: u8 = 0;
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4925_) == 0 {
                    v___x_4934_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4934_, 0, v_b_4926_);
                    return v___x_4934_;
                } else {
                    v_head_4935_ = lean_ctor_get(v_as_x27_4925_, 0);
                    v_tail_4936_ = lean_ctor_get(v_as_x27_4925_, 1);
                    v___x_4937_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_useCtor(v_a_4923_, v_head_4935_);
                    if v___x_4937_ == 0 {
                        v_as_x27_4925_ = v_tail_4936_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4939_ = lean_box(0);
                        lean_inc(v_head_4935_);
                        v___x_4940_ = l_Lean_mkConst(v_head_4935_, v___x_4939_);
                        lean_inc(v___y_4932_);
                        lean_inc_ref(v___y_4931_);
                        lean_inc(v___y_4930_);
                        lean_inc_ref(v___y_4929_);
                        v___x_4941_ = lean_infer_type(
                            v___x_4940_,
                            v___y_4929_,
                            v___y_4930_,
                            v___y_4931_,
                            v___y_4932_,
                        );
                        if lean_obj_tag(v___x_4941_) == 0 {
                            v_a_4942_ = lean_ctor_get(v___x_4941_, 0);
                            lean_inc(v_a_4942_);
                            lean_dec_ref_known(v___x_4941_, 1);
                            v___x_4943_ = lean_box(0);
                            v___x_4944_ = 0;
                            v___x_4945_ = l_Lean_Meta_forallMetaTelescopeReducing(
                                v_a_4942_,
                                v___x_4943_,
                                v___x_4944_,
                                v___y_4929_,
                                v___y_4930_,
                                v___y_4931_,
                                v___y_4932_,
                            );
                            if lean_obj_tag(v___x_4945_) == 0 {
                                v_a_4946_ = lean_ctor_get(v___x_4945_, 0);
                                lean_inc(v_a_4946_);
                                lean_dec_ref_known(v___x_4945_, 1);
                                v_fst_4947_ = lean_ctor_get(v_a_4946_, 0);
                                v_snd_4948_ = lean_ctor_get(v_a_4946_, 1);
                                v_isSharedCheck_4992_ = (!lean_is_exclusive(v_a_4946_)) as u8;
                                if v_isSharedCheck_4992_ == 0 {
                                    v___x_4950_ = v_a_4946_;
                                    v_isShared_4951_ = v_isSharedCheck_4992_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_snd_4948_);
                                    lean_inc(v_fst_4947_);
                                    lean_dec(v_a_4946_);
                                    v___x_4950_ = lean_box(0);
                                    v_isShared_4951_ = v_isSharedCheck_4992_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_b_4926_);
                                v_a_4993_ = lean_ctor_get(v___x_4945_, 0);
                                v_isSharedCheck_5000_ = (!lean_is_exclusive(v___x_4945_)) as u8;
                                if v_isSharedCheck_5000_ == 0 {
                                    v___x_4995_ = v___x_4945_;
                                    v_isShared_4996_ = v_isSharedCheck_5000_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_4993_);
                                    lean_dec(v___x_4945_);
                                    v___x_4995_ = lean_box(0);
                                    v_isShared_4996_ = v_isSharedCheck_5000_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_b_4926_);
                            v_a_5001_ = lean_ctor_get(v___x_4941_, 0);
                            v_isSharedCheck_5008_ = (!lean_is_exclusive(v___x_4941_)) as u8;
                            if v_isSharedCheck_5008_ == 0 {
                                v___x_5003_ = v___x_4941_;
                                v_isShared_5004_ = v_isSharedCheck_5008_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_5001_);
                                lean_dec(v___x_4941_);
                                v___x_5003_ = lean_box(0);
                                v_isShared_5004_ = v_isSharedCheck_5008_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_fst_4984_ = lean_ctor_get(v_snd_4948_, 0);
                lean_inc(v_fst_4984_);
                lean_dec(v_snd_4948_);
                v___x_4985_ = lean_unsigned_to_nat(0);
                v___x_4986_ = lean_array_get_size(v_fst_4984_);
                v___x_4987_ = lean_nat_dec_lt(v___x_4985_, v___x_4986_);
                if v___x_4987_ == 0 {
                    lean_dec(v_fst_4984_);
                    v___y_4983_ = v___x_4937_;
                    state = 7;
                    continue;
                } else {
                    if v___x_4987_ == 0 {
                        lean_dec(v_fst_4984_);
                        v___y_4983_ = v___x_4937_;
                        state = 7;
                        continue;
                    } else {
                        v___x_4988_ = 0usize;
                        v___x_4989_ = lean_usize_of_nat(v___x_4986_);
                        v___x_4990_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__1(v___x_4937_, v_fst_4984_, v___x_4988_, v___x_4989_);
                        lean_dec(v_fst_4984_);
                        if v___x_4990_ == 0 {
                            v___y_4983_ = v___x_4937_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v_fst_4947_);
                            lean_dec_ref(v_b_4926_);
                            v___x_4991_ = 0;
                            v___y_4965_ = v___x_4991_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v_sz_4959_ = lean_array_size(v_fst_4947_);
                v___x_4960_ = 0usize;
                lean_inc(v_head_4935_);
                v___x_4961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0(v_type_4924_, v_head_4935_, v_fst_4947_, v_sz_4959_, v___x_4960_, v_b_4926_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
                lean_dec(v_fst_4947_);
                if lean_obj_tag(v___x_4961_) == 0 {
                    v_a_4962_ = lean_ctor_get(v___x_4961_, 0);
                    lean_inc(v_a_4962_);
                    lean_dec_ref_known(v___x_4961_, 1);
                    v_as_x27_4925_ = v_tail_4936_;
                    v_b_4926_ = v_a_4962_;
                    state = 0;
                    continue;
                } else {
                    return v___x_4961_;
                }
            }
            3 => {
                v___x_4966_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__1);
                lean_inc(v_head_4935_);
                v___x_4967_ = l_Lean_MessageData_ofConstName(v_head_4935_, v___y_4965_);
                if v_isShared_4951_ == 0 {
                    lean_ctor_set_tag(v___x_4950_, 7);
                    lean_ctor_set(v___x_4950_, 1, v___x_4967_);
                    lean_ctor_set(v___x_4950_, 0, v___x_4966_);
                    v___x_4969_ = v___x_4950_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4981_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4981_, 0, v___x_4966_);
                    lean_ctor_set(v_reuseFailAlloc_4981_, 1, v___x_4967_);
                    v___x_4969_ = v_reuseFailAlloc_4981_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4970_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__3_once), _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__3);
                v___x_4971_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4971_, 0, v___x_4969_);
                lean_ctor_set(v___x_4971_, 1, v___x_4970_);
                v___x_4972_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___redArg(v___x_4971_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_);
                v_a_4973_ = lean_ctor_get(v___x_4972_, 0);
                v_isSharedCheck_4980_ = (!lean_is_exclusive(v___x_4972_)) as u8;
                if v_isSharedCheck_4980_ == 0 {
                    v___x_4975_ = v___x_4972_;
                    v_isShared_4976_ = v_isSharedCheck_4980_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_4973_);
                    lean_dec(v___x_4972_);
                    v___x_4975_ = lean_box(0);
                    v_isShared_4976_ = v_isSharedCheck_4980_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4976_ == 0 {
                    v___x_4978_ = v___x_4975_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4973_);
                    v___x_4978_ = v_reuseFailAlloc_4979_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4978_;
            }
            7 => {
                if v___y_4983_ == 0 {
                    lean_dec(v_fst_4947_);
                    lean_dec_ref(v_b_4926_);
                    v___y_4965_ = v___y_4983_;
                    state = 3;
                    continue;
                } else {
                    lean_del_object(v___x_4950_);
                    v___y_4953_ = v___y_4927_;
                    v___y_4954_ = v___y_4928_;
                    v___y_4955_ = v___y_4929_;
                    v___y_4956_ = v___y_4930_;
                    v___y_4957_ = v___y_4931_;
                    v___y_4958_ = v___y_4932_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                if v_isShared_4996_ == 0 {
                    v___x_4998_ = v___x_4995_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
                    v___x_4998_ = v_reuseFailAlloc_4999_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4998_;
            }
            10 => {
                if v_isShared_5004_ == 0 {
                    v___x_5006_ = v___x_5003_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
                    v___x_5006_ = v_reuseFailAlloc_5007_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5006_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___boxed(
    mut v_a_5009_: *mut LeanObject,
    mut v_type_5010_: *mut LeanObject,
    mut v_as_x27_5011_: *mut LeanObject,
    mut v_b_5012_: *mut LeanObject,
    mut v___y_5013_: *mut LeanObject,
    mut v___y_5014_: *mut LeanObject,
    mut v___y_5015_: *mut LeanObject,
    mut v___y_5016_: *mut LeanObject,
    mut v___y_5017_: *mut LeanObject,
    mut v___y_5018_: *mut LeanObject,
    mut v___y_5019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5020_: *mut LeanObject = core::ptr::null_mut();
    v_res_5020_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg(v_a_5009_, v_type_5010_, v_as_x27_5011_, v_b_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
    lean_dec(v___y_5018_);
    lean_dec_ref(v___y_5017_);
    lean_dec(v___y_5016_);
    lean_dec_ref(v___y_5015_);
    lean_dec(v___y_5014_);
    lean_dec_ref(v___y_5013_);
    lean_dec(v_as_x27_5011_);
    lean_dec_ref(v_type_5010_);
    lean_dec_ref(v_a_5009_);
    return v_res_5020_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2___redArg(
    mut v_type_5021_: *mut LeanObject,
    mut v_a_5022_: *mut LeanObject,
    mut v_as_5023_: *mut LeanObject,
    mut v_as_x27_5024_: *mut LeanObject,
    mut v_b_5025_: *mut LeanObject,
    mut v___y_5026_: *mut LeanObject,
    mut v___y_5027_: *mut LeanObject,
    mut v___y_5028_: *mut LeanObject,
    mut v___y_5029_: *mut LeanObject,
    mut v___y_5030_: *mut LeanObject,
    mut v___y_5031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: u8 = 0;
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: u8 = 0;
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5050_: u8 = 0;
    let mut v___y_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5058_: usize = 0;
    let mut v___x_5059_: usize = 0;
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5064_: u8 = 0;
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5075_: u8 = 0;
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5079_: u8 = 0;
    let mut v_reuseFailAlloc_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5082_: u8 = 0;
    let mut v_fst_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: u8 = 0;
    let mut v___x_5087_: usize = 0;
    let mut v___x_5088_: usize = 0;
    let mut v___x_5089_: u8 = 0;
    let mut v___x_5090_: u8 = 0;
    let mut v_isSharedCheck_5091_: u8 = 0;
    let mut v_a_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5095_: u8 = 0;
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5099_: u8 = 0;
    let mut v_a_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5103_: u8 = 0;
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_5024_) == 0 {
                    v___x_5033_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5033_, 0, v_b_5025_);
                    return v___x_5033_;
                } else {
                    v_head_5034_ = lean_ctor_get(v_as_x27_5024_, 0);
                    v_tail_5035_ = lean_ctor_get(v_as_x27_5024_, 1);
                    v___x_5036_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_useCtor(v_a_5022_, v_head_5034_);
                    if v___x_5036_ == 0 {
                        v___x_5037_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg(v_a_5022_, v_type_5021_, v_tail_5035_, v_b_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_);
                        return v___x_5037_;
                    } else {
                        v___x_5038_ = lean_box(0);
                        lean_inc(v_head_5034_);
                        v___x_5039_ = l_Lean_mkConst(v_head_5034_, v___x_5038_);
                        lean_inc(v___y_5031_);
                        lean_inc_ref(v___y_5030_);
                        lean_inc(v___y_5029_);
                        lean_inc_ref(v___y_5028_);
                        v___x_5040_ = lean_infer_type(
                            v___x_5039_,
                            v___y_5028_,
                            v___y_5029_,
                            v___y_5030_,
                            v___y_5031_,
                        );
                        if lean_obj_tag(v___x_5040_) == 0 {
                            v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
                            lean_inc(v_a_5041_);
                            lean_dec_ref_known(v___x_5040_, 1);
                            v___x_5042_ = lean_box(0);
                            v___x_5043_ = 0;
                            v___x_5044_ = l_Lean_Meta_forallMetaTelescopeReducing(
                                v_a_5041_,
                                v___x_5042_,
                                v___x_5043_,
                                v___y_5028_,
                                v___y_5029_,
                                v___y_5030_,
                                v___y_5031_,
                            );
                            if lean_obj_tag(v___x_5044_) == 0 {
                                v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
                                lean_inc(v_a_5045_);
                                lean_dec_ref_known(v___x_5044_, 1);
                                v_fst_5046_ = lean_ctor_get(v_a_5045_, 0);
                                v_snd_5047_ = lean_ctor_get(v_a_5045_, 1);
                                v_isSharedCheck_5091_ = (!lean_is_exclusive(v_a_5045_)) as u8;
                                if v_isSharedCheck_5091_ == 0 {
                                    v___x_5049_ = v_a_5045_;
                                    v_isShared_5050_ = v_isSharedCheck_5091_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_snd_5047_);
                                    lean_inc(v_fst_5046_);
                                    lean_dec(v_a_5045_);
                                    v___x_5049_ = lean_box(0);
                                    v_isShared_5050_ = v_isSharedCheck_5091_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_b_5025_);
                                v_a_5092_ = lean_ctor_get(v___x_5044_, 0);
                                v_isSharedCheck_5099_ = (!lean_is_exclusive(v___x_5044_)) as u8;
                                if v_isSharedCheck_5099_ == 0 {
                                    v___x_5094_ = v___x_5044_;
                                    v_isShared_5095_ = v_isSharedCheck_5099_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_5092_);
                                    lean_dec(v___x_5044_);
                                    v___x_5094_ = lean_box(0);
                                    v_isShared_5095_ = v_isSharedCheck_5099_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_b_5025_);
                            v_a_5100_ = lean_ctor_get(v___x_5040_, 0);
                            v_isSharedCheck_5107_ = (!lean_is_exclusive(v___x_5040_)) as u8;
                            if v_isSharedCheck_5107_ == 0 {
                                v___x_5102_ = v___x_5040_;
                                v_isShared_5103_ = v_isSharedCheck_5107_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_5100_);
                                lean_dec(v___x_5040_);
                                v___x_5102_ = lean_box(0);
                                v_isShared_5103_ = v_isSharedCheck_5107_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_fst_5083_ = lean_ctor_get(v_snd_5047_, 0);
                lean_inc(v_fst_5083_);
                lean_dec(v_snd_5047_);
                v___x_5084_ = lean_unsigned_to_nat(0);
                v___x_5085_ = lean_array_get_size(v_fst_5083_);
                v___x_5086_ = lean_nat_dec_lt(v___x_5084_, v___x_5085_);
                if v___x_5086_ == 0 {
                    lean_dec(v_fst_5083_);
                    v___y_5082_ = v___x_5036_;
                    state = 7;
                    continue;
                } else {
                    if v___x_5086_ == 0 {
                        lean_dec(v_fst_5083_);
                        v___y_5082_ = v___x_5036_;
                        state = 7;
                        continue;
                    } else {
                        v___x_5087_ = 0usize;
                        v___x_5088_ = lean_usize_of_nat(v___x_5085_);
                        v___x_5089_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__1(v___x_5036_, v_fst_5083_, v___x_5087_, v___x_5088_);
                        lean_dec(v_fst_5083_);
                        if v___x_5089_ == 0 {
                            v___y_5082_ = v___x_5036_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v_fst_5046_);
                            lean_dec_ref(v_b_5025_);
                            v___x_5090_ = 0;
                            v___y_5064_ = v___x_5090_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v_sz_5058_ = lean_array_size(v_fst_5046_);
                v___x_5059_ = 0usize;
                lean_inc(v_head_5034_);
                v___x_5060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__0(v_type_5021_, v_head_5034_, v_fst_5046_, v_sz_5058_, v___x_5059_, v_b_5025_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_);
                lean_dec(v_fst_5046_);
                if lean_obj_tag(v___x_5060_) == 0 {
                    v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
                    lean_inc(v_a_5061_);
                    lean_dec_ref_known(v___x_5060_, 1);
                    v___x_5062_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg(v_a_5022_, v_type_5021_, v_tail_5035_, v_a_5061_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_);
                    return v___x_5062_;
                } else {
                    return v___x_5060_;
                }
            }
            3 => {
                v___x_5065_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__1);
                lean_inc(v_head_5034_);
                v___x_5066_ = l_Lean_MessageData_ofConstName(v_head_5034_, v___y_5064_);
                if v_isShared_5050_ == 0 {
                    lean_ctor_set_tag(v___x_5049_, 7);
                    lean_ctor_set(v___x_5049_, 1, v___x_5066_);
                    lean_ctor_set(v___x_5049_, 0, v___x_5065_);
                    v___x_5068_ = v___x_5049_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5080_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5080_, 0, v___x_5065_);
                    lean_ctor_set(v_reuseFailAlloc_5080_, 1, v___x_5066_);
                    v___x_5068_ = v_reuseFailAlloc_5080_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5069_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__3_once), _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg___closed__3);
                v___x_5070_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5070_, 0, v___x_5068_);
                lean_ctor_set(v___x_5070_, 1, v___x_5069_);
                v___x_5071_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1___redArg(v___x_5070_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_);
                v_a_5072_ = lean_ctor_get(v___x_5071_, 0);
                v_isSharedCheck_5079_ = (!lean_is_exclusive(v___x_5071_)) as u8;
                if v_isSharedCheck_5079_ == 0 {
                    v___x_5074_ = v___x_5071_;
                    v_isShared_5075_ = v_isSharedCheck_5079_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_5072_);
                    lean_dec(v___x_5071_);
                    v___x_5074_ = lean_box(0);
                    v_isShared_5075_ = v_isSharedCheck_5079_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5075_ == 0 {
                    v___x_5077_ = v___x_5074_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
                    v___x_5077_ = v_reuseFailAlloc_5078_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5077_;
            }
            7 => {
                if v___y_5082_ == 0 {
                    lean_dec(v_fst_5046_);
                    lean_dec_ref(v_b_5025_);
                    v___y_5064_ = v___y_5082_;
                    state = 3;
                    continue;
                } else {
                    lean_del_object(v___x_5049_);
                    v___y_5052_ = v___y_5026_;
                    v___y_5053_ = v___y_5027_;
                    v___y_5054_ = v___y_5028_;
                    v___y_5055_ = v___y_5029_;
                    v___y_5056_ = v___y_5030_;
                    v___y_5057_ = v___y_5031_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                if v_isShared_5095_ == 0 {
                    v___x_5097_ = v___x_5094_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5098_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_a_5092_);
                    v___x_5097_ = v_reuseFailAlloc_5098_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5097_;
            }
            10 => {
                if v_isShared_5103_ == 0 {
                    v___x_5105_ = v___x_5102_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
                    v___x_5105_ = v_reuseFailAlloc_5106_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2___redArg___boxed(
    mut v_type_5108_: *mut LeanObject,
    mut v_a_5109_: *mut LeanObject,
    mut v_as_5110_: *mut LeanObject,
    mut v_as_x27_5111_: *mut LeanObject,
    mut v_b_5112_: *mut LeanObject,
    mut v___y_5113_: *mut LeanObject,
    mut v___y_5114_: *mut LeanObject,
    mut v___y_5115_: *mut LeanObject,
    mut v___y_5116_: *mut LeanObject,
    mut v___y_5117_: *mut LeanObject,
    mut v___y_5118_: *mut LeanObject,
    mut v___y_5119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5120_: *mut LeanObject = core::ptr::null_mut();
    v_res_5120_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2___redArg(v_type_5108_, v_a_5109_, v_as_5110_, v_as_x27_5111_, v_b_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_);
    lean_dec(v___y_5118_);
    lean_dec_ref(v___y_5117_);
    lean_dec(v___y_5116_);
    lean_dec_ref(v___y_5115_);
    lean_dec(v___y_5114_);
    lean_dec_ref(v___y_5113_);
    lean_dec(v_as_x27_5111_);
    lean_dec(v_as_5110_);
    lean_dec_ref(v_a_5109_);
    lean_dec_ref(v_type_5108_);
    return v_res_5120_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps(
    mut v_typeRef_5123_: *mut LeanObject,
    mut v_type_5124_: *mut LeanObject,
    mut v_a_5125_: *mut LeanObject,
    mut v_a_5126_: *mut LeanObject,
    mut v_a_5127_: *mut LeanObject,
    mut v_a_5128_: *mut LeanObject,
    mut v_a_5129_: *mut LeanObject,
    mut v_a_5130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5144_: u8 = 0;
    let mut v_cancelTk_x3f_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5146_: u8 = 0;
    let mut v_inheritedTraceOptions_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5158_: u8 = 0;
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5132_ = lean_ctor_get(v_a_5129_, 0);
                v_fileMap_5133_ = lean_ctor_get(v_a_5129_, 1);
                v_options_5134_ = lean_ctor_get(v_a_5129_, 2);
                v_currRecDepth_5135_ = lean_ctor_get(v_a_5129_, 3);
                v_maxRecDepth_5136_ = lean_ctor_get(v_a_5129_, 4);
                v_ref_5137_ = lean_ctor_get(v_a_5129_, 5);
                v_currNamespace_5138_ = lean_ctor_get(v_a_5129_, 6);
                v_openDecls_5139_ = lean_ctor_get(v_a_5129_, 7);
                v_initHeartbeats_5140_ = lean_ctor_get(v_a_5129_, 8);
                v_maxHeartbeats_5141_ = lean_ctor_get(v_a_5129_, 9);
                v_quotContext_5142_ = lean_ctor_get(v_a_5129_, 10);
                v_currMacroScope_5143_ = lean_ctor_get(v_a_5129_, 11);
                v_diag_5144_ = lean_ctor_get_uint8(
                    v_a_5129_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5145_ = lean_ctor_get(v_a_5129_, 12);
                v_suppressElabErrors_5146_ = lean_ctor_get_uint8(
                    v_a_5129_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5147_ = lean_ctor_get(v_a_5129_, 13);
                v_ref_5148_ = l_Lean_replaceRef(v_typeRef_5123_, v_ref_5137_);
                lean_inc_ref(v_inheritedTraceOptions_5147_);
                lean_inc(v_cancelTk_x3f_5145_);
                lean_inc(v_currMacroScope_5143_);
                lean_inc(v_quotContext_5142_);
                lean_inc(v_maxHeartbeats_5141_);
                lean_inc(v_initHeartbeats_5140_);
                lean_inc(v_openDecls_5139_);
                lean_inc(v_currNamespace_5138_);
                lean_inc(v_maxRecDepth_5136_);
                lean_inc(v_currRecDepth_5135_);
                lean_inc_ref(v_options_5134_);
                lean_inc_ref(v_fileMap_5133_);
                lean_inc_ref(v_fileName_5132_);
                v___x_5149_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_5149_, 0, v_fileName_5132_);
                lean_ctor_set(v___x_5149_, 1, v_fileMap_5133_);
                lean_ctor_set(v___x_5149_, 2, v_options_5134_);
                lean_ctor_set(v___x_5149_, 3, v_currRecDepth_5135_);
                lean_ctor_set(v___x_5149_, 4, v_maxRecDepth_5136_);
                lean_ctor_set(v___x_5149_, 5, v_ref_5148_);
                lean_ctor_set(v___x_5149_, 6, v_currNamespace_5138_);
                lean_ctor_set(v___x_5149_, 7, v_openDecls_5139_);
                lean_ctor_set(v___x_5149_, 8, v_initHeartbeats_5140_);
                lean_ctor_set(v___x_5149_, 9, v_maxHeartbeats_5141_);
                lean_ctor_set(v___x_5149_, 10, v_quotContext_5142_);
                lean_ctor_set(v___x_5149_, 11, v_currMacroScope_5143_);
                lean_ctor_set(v___x_5149_, 12, v_cancelTk_x3f_5145_);
                lean_ctor_set(v___x_5149_, 13, v_inheritedTraceOptions_5147_);
                lean_ctor_set_uint8(
                    v___x_5149_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_5144_,
                );
                lean_ctor_set_uint8(
                    v___x_5149_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5146_,
                );
                lean_inc_ref(v_type_5124_);
                v___x_5150_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType(v_typeRef_5123_, v_type_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v___x_5149_, v_a_5130_);
                if lean_obj_tag(v___x_5150_) == 0 {
                    v_a_5151_ = lean_ctor_get(v___x_5150_, 0);
                    lean_inc(v_a_5151_);
                    lean_dec_ref_known(v___x_5150_, 1);
                    v_ctors_5152_ = lean_ctor_get(v_a_5151_, 4);
                    lean_inc(v_ctors_5152_);
                    v___x_5153_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps___closed__0;
                    v___x_5154_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2___redArg(v_type_5124_, v_a_5151_, v_ctors_5152_, v_ctors_5152_, v___x_5153_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v___x_5149_, v_a_5130_);
                    lean_dec_ref_known(v___x_5149_, 14);
                    lean_dec(v_ctors_5152_);
                    lean_dec(v_a_5151_);
                    lean_dec_ref(v_type_5124_);
                    return v___x_5154_;
                } else {
                    lean_dec_ref_known(v___x_5149_, 14);
                    lean_dec_ref(v_type_5124_);
                    v_a_5155_ = lean_ctor_get(v___x_5150_, 0);
                    v_isSharedCheck_5162_ = (!lean_is_exclusive(v___x_5150_)) as u8;
                    if v_isSharedCheck_5162_ == 0 {
                        v___x_5157_ = v___x_5150_;
                        v_isShared_5158_ = v_isSharedCheck_5162_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5155_);
                        lean_dec(v___x_5150_);
                        v___x_5157_ = lean_box(0);
                        v_isShared_5158_ = v_isSharedCheck_5162_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5158_ == 0 {
                    v___x_5160_ = v___x_5157_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5161_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_a_5155_);
                    v___x_5160_ = v_reuseFailAlloc_5161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps___boxed(
    mut v_typeRef_5163_: *mut LeanObject,
    mut v_type_5164_: *mut LeanObject,
    mut v_a_5165_: *mut LeanObject,
    mut v_a_5166_: *mut LeanObject,
    mut v_a_5167_: *mut LeanObject,
    mut v_a_5168_: *mut LeanObject,
    mut v_a_5169_: *mut LeanObject,
    mut v_a_5170_: *mut LeanObject,
    mut v_a_5171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5172_: *mut LeanObject = core::ptr::null_mut();
    v_res_5172_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps(v_typeRef_5163_, v_type_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_);
    lean_dec(v_a_5170_);
    lean_dec_ref(v_a_5169_);
    lean_dec(v_a_5168_);
    lean_dec_ref(v_a_5167_);
    lean_dec(v_a_5166_);
    lean_dec_ref(v_a_5165_);
    lean_dec(v_typeRef_5163_);
    return v_res_5172_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2(
    mut v_type_5173_: *mut LeanObject,
    mut v_a_5174_: *mut LeanObject,
    mut v_as_5175_: *mut LeanObject,
    mut v_as_x27_5176_: *mut LeanObject,
    mut v_b_5177_: *mut LeanObject,
    mut v_a_5178_: *mut LeanObject,
    mut v___y_5179_: *mut LeanObject,
    mut v___y_5180_: *mut LeanObject,
    mut v___y_5181_: *mut LeanObject,
    mut v___y_5182_: *mut LeanObject,
    mut v___y_5183_: *mut LeanObject,
    mut v___y_5184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    v___x_5186_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2___redArg(v_type_5173_, v_a_5174_, v_as_5175_, v_as_x27_5176_, v_b_5177_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
    return v___x_5186_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2___boxed(
    mut v_type_5187_: *mut LeanObject,
    mut v_a_5188_: *mut LeanObject,
    mut v_as_5189_: *mut LeanObject,
    mut v_as_x27_5190_: *mut LeanObject,
    mut v_b_5191_: *mut LeanObject,
    mut v_a_5192_: *mut LeanObject,
    mut v___y_5193_: *mut LeanObject,
    mut v___y_5194_: *mut LeanObject,
    mut v___y_5195_: *mut LeanObject,
    mut v___y_5196_: *mut LeanObject,
    mut v___y_5197_: *mut LeanObject,
    mut v___y_5198_: *mut LeanObject,
    mut v___y_5199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5200_: *mut LeanObject = core::ptr::null_mut();
    v_res_5200_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2(v_type_5187_, v_a_5188_, v_as_5189_, v_as_x27_5190_, v_b_5191_, v_a_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_);
    lean_dec(v___y_5198_);
    lean_dec_ref(v___y_5197_);
    lean_dec(v___y_5196_);
    lean_dec_ref(v___y_5195_);
    lean_dec(v___y_5194_);
    lean_dec_ref(v___y_5193_);
    lean_dec(v_as_x27_5190_);
    lean_dec(v_as_5189_);
    lean_dec_ref(v_a_5188_);
    lean_dec_ref(v_type_5187_);
    return v_res_5200_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2(
    mut v_a_5201_: *mut LeanObject,
    mut v_type_5202_: *mut LeanObject,
    mut v_as_5203_: *mut LeanObject,
    mut v_as_x27_5204_: *mut LeanObject,
    mut v_b_5205_: *mut LeanObject,
    mut v_a_5206_: *mut LeanObject,
    mut v___y_5207_: *mut LeanObject,
    mut v___y_5208_: *mut LeanObject,
    mut v___y_5209_: *mut LeanObject,
    mut v___y_5210_: *mut LeanObject,
    mut v___y_5211_: *mut LeanObject,
    mut v___y_5212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    v___x_5214_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___redArg(v_a_5201_, v_type_5202_, v_as_x27_5204_, v_b_5205_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_);
    return v___x_5214_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2___boxed(
    mut v_a_5215_: *mut LeanObject,
    mut v_type_5216_: *mut LeanObject,
    mut v_as_5217_: *mut LeanObject,
    mut v_as_x27_5218_: *mut LeanObject,
    mut v_b_5219_: *mut LeanObject,
    mut v_a_5220_: *mut LeanObject,
    mut v___y_5221_: *mut LeanObject,
    mut v___y_5222_: *mut LeanObject,
    mut v___y_5223_: *mut LeanObject,
    mut v___y_5224_: *mut LeanObject,
    mut v___y_5225_: *mut LeanObject,
    mut v___y_5226_: *mut LeanObject,
    mut v___y_5227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5228_: *mut LeanObject = core::ptr::null_mut();
    v_res_5228_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps_spec__2_spec__2(v_a_5215_, v_type_5216_, v_as_5217_, v_as_x27_5218_, v_b_5219_, v_a_5220_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_);
    lean_dec(v___y_5226_);
    lean_dec_ref(v___y_5225_);
    lean_dec(v___y_5224_);
    lean_dec_ref(v___y_5223_);
    lean_dec(v___y_5222_);
    lean_dec_ref(v___y_5221_);
    lean_dec(v_as_x27_5218_);
    lean_dec(v_as_5217_);
    lean_dec_ref(v_type_5216_);
    lean_dec_ref(v_a_5215_);
    return v_res_5228_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__0___redArg(
    mut v_e_5229_: *mut LeanObject,
    mut v___y_5230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5232_: u8 = 0;
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5246_: u8 = 0;
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5252_: u8 = 0;
    let mut v_unused_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5232_ = l_Lean_Expr_hasMVar(v_e_5229_);
                if v___x_5232_ == 0 {
                    v___x_5233_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5233_, 0, v_e_5229_);
                    return v___x_5233_;
                } else {
                    v___x_5234_ = lean_st_ref_get(v___y_5230_);
                    v_mctx_5235_ = lean_ctor_get(v___x_5234_, 0);
                    lean_inc_ref(v_mctx_5235_);
                    lean_dec(v___x_5234_);
                    v___x_5236_ = l_Lean_instantiateMVarsCore(v_mctx_5235_, v_e_5229_);
                    v_fst_5237_ = lean_ctor_get(v___x_5236_, 0);
                    lean_inc(v_fst_5237_);
                    v_snd_5238_ = lean_ctor_get(v___x_5236_, 1);
                    lean_inc(v_snd_5238_);
                    lean_dec_ref(v___x_5236_);
                    v___x_5239_ = lean_st_ref_take(v___y_5230_);
                    v_cache_5240_ = lean_ctor_get(v___x_5239_, 1);
                    v_zetaDeltaFVarIds_5241_ = lean_ctor_get(v___x_5239_, 2);
                    v_postponed_5242_ = lean_ctor_get(v___x_5239_, 3);
                    v_diag_5243_ = lean_ctor_get(v___x_5239_, 4);
                    v_isSharedCheck_5252_ = (!lean_is_exclusive(v___x_5239_)) as u8;
                    if v_isSharedCheck_5252_ == 0 {
                        v_unused_5253_ = lean_ctor_get(v___x_5239_, 0);
                        lean_dec(v_unused_5253_);
                        v___x_5245_ = v___x_5239_;
                        v_isShared_5246_ = v_isSharedCheck_5252_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_5243_);
                        lean_inc(v_postponed_5242_);
                        lean_inc(v_zetaDeltaFVarIds_5241_);
                        lean_inc(v_cache_5240_);
                        lean_dec(v___x_5239_);
                        v___x_5245_ = lean_box(0);
                        v_isShared_5246_ = v_isSharedCheck_5252_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5246_ == 0 {
                    lean_ctor_set(v___x_5245_, 0, v_snd_5238_);
                    v___x_5248_ = v___x_5245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5251_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_snd_5238_);
                    lean_ctor_set(v_reuseFailAlloc_5251_, 1, v_cache_5240_);
                    lean_ctor_set(v_reuseFailAlloc_5251_, 2, v_zetaDeltaFVarIds_5241_);
                    lean_ctor_set(v_reuseFailAlloc_5251_, 3, v_postponed_5242_);
                    lean_ctor_set(v_reuseFailAlloc_5251_, 4, v_diag_5243_);
                    v___x_5248_ = v_reuseFailAlloc_5251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5249_ = lean_st_ref_set(v___y_5230_, v___x_5248_);
                v___x_5250_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5250_, 0, v_fst_5237_);
                return v___x_5250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__0___redArg___boxed(
    mut v_e_5254_: *mut LeanObject,
    mut v___y_5255_: *mut LeanObject,
    mut v___y_5256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5257_: *mut LeanObject = core::ptr::null_mut();
    v_res_5257_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__0___redArg(
            v_e_5254_,
            v___y_5255_,
        );
    lean_dec(v___y_5255_);
    return v_res_5257_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__0(
    mut v_e_5258_: *mut LeanObject,
    mut v___y_5259_: *mut LeanObject,
    mut v___y_5260_: *mut LeanObject,
    mut v___y_5261_: *mut LeanObject,
    mut v___y_5262_: *mut LeanObject,
    mut v___y_5263_: *mut LeanObject,
    mut v___y_5264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    v___x_5266_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__0___redArg(
            v_e_5258_,
            v___y_5262_,
        );
    return v___x_5266_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__0___boxed(
    mut v_e_5267_: *mut LeanObject,
    mut v___y_5268_: *mut LeanObject,
    mut v___y_5269_: *mut LeanObject,
    mut v___y_5270_: *mut LeanObject,
    mut v___y_5271_: *mut LeanObject,
    mut v___y_5272_: *mut LeanObject,
    mut v___y_5273_: *mut LeanObject,
    mut v___y_5274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5275_: *mut LeanObject = core::ptr::null_mut();
    v_res_5275_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__0(
        v_e_5267_,
        v___y_5268_,
        v___y_5269_,
        v___y_5270_,
        v___y_5271_,
        v___y_5272_,
        v___y_5273_,
    );
    lean_dec(v___y_5273_);
    lean_dec_ref(v___y_5272_);
    lean_dec(v___y_5271_);
    lean_dec_ref(v___y_5270_);
    lean_dec(v___y_5269_);
    lean_dec_ref(v___y_5268_);
    return v_res_5275_;
}
pub unsafe fn _init_l_panic___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__5___closed__0()
-> *mut LeanObject {
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    v___x_5276_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
    return v___x_5276_;
}
pub unsafe fn l_panic___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__5(
    mut v_msg_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
    mut v___y_5279_: *mut LeanObject,
    mut v___y_5280_: *mut LeanObject,
    mut v___y_5281_: *mut LeanObject,
    mut v___y_5282_: *mut LeanObject,
    mut v___y_5283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_39551__overap_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    v___x_5285_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__5___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__5___closed__0_once
        ),
        _init_l_panic___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__5___closed__0,
    );
    v___x_39551__overap_5286_ = lean_panic_fn_borrowed(v___x_5285_, v_msg_5277_);
    lean_inc(v___y_5283_);
    lean_inc_ref(v___y_5282_);
    lean_inc(v___y_5281_);
    lean_inc_ref(v___y_5280_);
    lean_inc(v___y_5279_);
    lean_inc_ref(v___y_5278_);
    v___x_5287_ = lean_apply_7(
        v___x_39551__overap_5286_,
        v___y_5278_,
        v___y_5279_,
        v___y_5280_,
        v___y_5281_,
        v___y_5282_,
        v___y_5283_,
        lean_box(0),
    );
    return v___x_5287_;
}
pub unsafe fn l_panic___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__5___boxed(
    mut v_msg_5288_: *mut LeanObject,
    mut v___y_5289_: *mut LeanObject,
    mut v___y_5290_: *mut LeanObject,
    mut v___y_5291_: *mut LeanObject,
    mut v___y_5292_: *mut LeanObject,
    mut v___y_5293_: *mut LeanObject,
    mut v___y_5294_: *mut LeanObject,
    mut v___y_5295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5296_: *mut LeanObject = core::ptr::null_mut();
    v_res_5296_ = l_panic___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__5(
        v_msg_5288_,
        v___y_5289_,
        v___y_5290_,
        v___y_5291_,
        v___y_5292_,
        v___y_5293_,
        v___y_5294_,
    );
    lean_dec(v___y_5294_);
    lean_dec_ref(v___y_5293_);
    lean_dec(v___y_5292_);
    lean_dec_ref(v___y_5291_);
    lean_dec(v___y_5290_);
    lean_dec_ref(v___y_5289_);
    return v_res_5296_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__0(
    mut v___y_5297_: *mut LeanObject,
    mut v___y_5298_: *mut LeanObject,
    mut v___y_5299_: *mut LeanObject,
    mut v___y_5300_: *mut LeanObject,
    mut v___y_5301_: *mut LeanObject,
    mut v___y_5302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: u8 = 0;
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5304_ = lean_ctor_get(v___y_5301_, 5);
    v___x_5305_ = 0;
    v___x_5306_ = l_Lean_SourceInfo_fromRef(v_ref_5304_, v___x_5305_);
    v___x_5307_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5307_, 0, v___x_5306_);
    return v___x_5307_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__0___boxed(
    mut v___y_5308_: *mut LeanObject,
    mut v___y_5309_: *mut LeanObject,
    mut v___y_5310_: *mut LeanObject,
    mut v___y_5311_: *mut LeanObject,
    mut v___y_5312_: *mut LeanObject,
    mut v___y_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5315_: *mut LeanObject = core::ptr::null_mut();
    v_res_5315_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__0(
        v___y_5308_,
        v___y_5309_,
        v___y_5310_,
        v___y_5311_,
        v___y_5312_,
        v___y_5313_,
    );
    lean_dec(v___y_5313_);
    lean_dec_ref(v___y_5312_);
    lean_dec(v___y_5311_);
    lean_dec_ref(v___y_5310_);
    lean_dec(v___y_5309_);
    lean_dec_ref(v___y_5308_);
    return v_res_5315_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__3(
    mut v_type_x27_5316_: *mut LeanObject,
    mut v_sz_5317_: usize,
    mut v_i_5318_: usize,
    mut v_bs_5319_: *mut LeanObject,
    mut v___y_5320_: *mut LeanObject,
    mut v___y_5321_: *mut LeanObject,
    mut v___y_5322_: *mut LeanObject,
    mut v___y_5323_: *mut LeanObject,
    mut v___y_5324_: *mut LeanObject,
    mut v___y_5325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5327_: u8 = 0;
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: u8 = 0;
    let mut v___x_5337_: usize = 0;
    let mut v___x_5338_: usize = 0;
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5345_: u8 = 0;
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5349_: u8 = 0;
    let mut v_a_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5353_: u8 = 0;
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5327_ = lean_usize_dec_lt(v_i_5318_, v_sz_5317_);
                if v___x_5327_ == 0 {
                    v___x_5328_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5328_, 0, v_bs_5319_);
                    return v___x_5328_;
                } else {
                    v_v_5329_ = lean_array_uget_borrowed(v_bs_5319_, v_i_5318_);
                    lean_inc(v___y_5325_);
                    lean_inc_ref(v___y_5324_);
                    lean_inc(v___y_5323_);
                    lean_inc_ref(v___y_5322_);
                    lean_inc(v_v_5329_);
                    v___x_5330_ = lean_infer_type(
                        v_v_5329_,
                        v___y_5322_,
                        v___y_5323_,
                        v___y_5324_,
                        v___y_5325_,
                    );
                    if lean_obj_tag(v___x_5330_) == 0 {
                        v_a_5331_ = lean_ctor_get(v___x_5330_, 0);
                        lean_inc(v_a_5331_);
                        lean_dec_ref_known(v___x_5330_, 1);
                        v___x_5332_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__0___redArg(v_a_5331_, v___y_5323_);
                        if lean_obj_tag(v___x_5332_) == 0 {
                            v_a_5333_ = lean_ctor_get(v___x_5332_, 0);
                            lean_inc(v_a_5333_);
                            lean_dec_ref_known(v___x_5332_, 1);
                            v___x_5334_ = lean_unsigned_to_nat(0);
                            v_bs_x27_5335_ = lean_array_uset(v_bs_5319_, v_i_5318_, v___x_5334_);
                            v___x_5336_ = lean_expr_eqv(v_a_5333_, v_type_x27_5316_);
                            lean_dec(v_a_5333_);
                            v___x_5337_ = 1usize;
                            v___x_5338_ = lean_usize_add(v_i_5318_, v___x_5337_);
                            v___x_5339_ = lean_box((v___x_5336_) as usize);
                            v___x_5340_ = lean_array_uset(v_bs_x27_5335_, v_i_5318_, v___x_5339_);
                            v_i_5318_ = v___x_5338_;
                            v_bs_5319_ = v___x_5340_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_bs_5319_);
                            v_a_5342_ = lean_ctor_get(v___x_5332_, 0);
                            v_isSharedCheck_5349_ = (!lean_is_exclusive(v___x_5332_)) as u8;
                            if v_isSharedCheck_5349_ == 0 {
                                v___x_5344_ = v___x_5332_;
                                v_isShared_5345_ = v_isSharedCheck_5349_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_5342_);
                                lean_dec(v___x_5332_);
                                v___x_5344_ = lean_box(0);
                                v_isShared_5345_ = v_isSharedCheck_5349_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_bs_5319_);
                        v_a_5350_ = lean_ctor_get(v___x_5330_, 0);
                        v_isSharedCheck_5357_ = (!lean_is_exclusive(v___x_5330_)) as u8;
                        if v_isSharedCheck_5357_ == 0 {
                            v___x_5352_ = v___x_5330_;
                            v_isShared_5353_ = v_isSharedCheck_5357_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5350_);
                            lean_dec(v___x_5330_);
                            v___x_5352_ = lean_box(0);
                            v_isShared_5353_ = v_isSharedCheck_5357_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5345_ == 0 {
                    v___x_5347_ = v___x_5344_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5348_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_a_5342_);
                    v___x_5347_ = v_reuseFailAlloc_5348_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5347_;
            }
            3 => {
                if v_isShared_5353_ == 0 {
                    v___x_5355_ = v___x_5352_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5356_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5350_);
                    v___x_5355_ = v_reuseFailAlloc_5356_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__3___boxed(
    mut v_type_x27_5358_: *mut LeanObject,
    mut v_sz_5359_: *mut LeanObject,
    mut v_i_5360_: *mut LeanObject,
    mut v_bs_5361_: *mut LeanObject,
    mut v___y_5362_: *mut LeanObject,
    mut v___y_5363_: *mut LeanObject,
    mut v___y_5364_: *mut LeanObject,
    mut v___y_5365_: *mut LeanObject,
    mut v___y_5366_: *mut LeanObject,
    mut v___y_5367_: *mut LeanObject,
    mut v___y_5368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5369_: usize = 0;
    let mut v_i_boxed_5370_: usize = 0;
    let mut v_res_5371_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5369_ = lean_unbox_usize(v_sz_5359_);
    lean_dec(v_sz_5359_);
    v_i_boxed_5370_ = lean_unbox_usize(v_i_5360_);
    lean_dec(v_i_5360_);
    v_res_5371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__3(v_type_x27_5358_, v_sz_boxed_5369_, v_i_boxed_5370_, v_bs_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_);
    lean_dec(v___y_5367_);
    lean_dec_ref(v___y_5366_);
    lean_dec(v___y_5365_);
    lean_dec_ref(v___y_5364_);
    lean_dec(v___y_5363_);
    lean_dec_ref(v___y_5362_);
    lean_dec_ref(v_type_x27_5358_);
    return v_res_5371_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___lam__0(
    mut v___x_5372_: u8,
    mut v___y_5373_: *mut LeanObject,
    mut v___y_5374_: *mut LeanObject,
    mut v___y_5375_: *mut LeanObject,
    mut v___y_5376_: *mut LeanObject,
    mut v___y_5377_: *mut LeanObject,
    mut v___y_5378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5380_ = lean_ctor_get(v___y_5377_, 5);
    v___x_5381_ = l_Lean_SourceInfo_fromRef(v_ref_5380_, v___x_5372_);
    v___x_5382_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5382_, 0, v___x_5381_);
    return v___x_5382_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___lam__0___boxed(
    mut v___x_5383_: *mut LeanObject,
    mut v___y_5384_: *mut LeanObject,
    mut v___y_5385_: *mut LeanObject,
    mut v___y_5386_: *mut LeanObject,
    mut v___y_5387_: *mut LeanObject,
    mut v___y_5388_: *mut LeanObject,
    mut v___y_5389_: *mut LeanObject,
    mut v___y_5390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_41239__boxed_5391_: u8 = 0;
    let mut v_res_5392_: *mut LeanObject = core::ptr::null_mut();
    v___x_41239__boxed_5391_ = (lean_unbox(v___x_5383_) as u8);
    v_res_5392_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___lam__0(v___x_41239__boxed_5391_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_);
    lean_dec(v___y_5389_);
    lean_dec_ref(v___y_5388_);
    lean_dec(v___y_5387_);
    lean_dec_ref(v___y_5386_);
    lean_dec(v___y_5385_);
    lean_dec_ref(v___y_5384_);
    return v_res_5392_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__12()
-> *mut LeanObject {
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    v___x_5410_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__11;
    v___x_5411_ = l_String_toRawSubstring_x27(v___x_5410_);
    return v___x_5411_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__22()
-> *mut LeanObject {
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    v___x_5434_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__21;
    v___x_5435_ = l_String_toRawSubstring_x27(v___x_5434_);
    return v___x_5435_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26()
-> *mut LeanObject {
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    v___x_5441_ = l_Array_mkArray0(lean_box(0));
    return v___x_5441_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4(
    mut v___x_5459_: *mut LeanObject,
    mut v_as_5460_: *mut LeanObject,
    mut v_i_5461_: usize,
    mut v_stop_5462_: usize,
    mut v_b_5463_: *mut LeanObject,
    mut v___y_5464_: *mut LeanObject,
    mut v___y_5465_: *mut LeanObject,
    mut v___y_5466_: *mut LeanObject,
    mut v___y_5467_: *mut LeanObject,
    mut v___y_5468_: *mut LeanObject,
    mut v___y_5469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5471_: u8 = 0;
    let mut v___x_5472_: usize = 0;
    let mut v___x_5473_: usize = 0;
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: u8 = 0;
    let mut v_snd_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5481_: u8 = 0;
    let mut v_fst_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5485_: u8 = 0;
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5540_: u8 = 0;
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5544_: u8 = 0;
    let mut v_isSharedCheck_5545_: u8 = 0;
    let mut v_unused_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5547_: u8 = 0;
    let mut v_unused_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5552_: u8 = 0;
    let mut v_fst_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5556_: u8 = 0;
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5606_: u8 = 0;
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5610_: u8 = 0;
    let mut v_isSharedCheck_5611_: u8 = 0;
    let mut v_unused_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5613_: u8 = 0;
    let mut v_unused_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5471_ = lean_usize_dec_eq(v_i_5461_, v_stop_5462_);
                if v___x_5471_ == 0 {
                    v___x_5472_ = 1usize;
                    v___x_5473_ = lean_usize_sub(v_i_5461_, v___x_5472_);
                    v___x_5474_ = lean_array_uget(v_as_5460_, v___x_5473_);
                    v_fst_5475_ = lean_ctor_get(v___x_5474_, 0);
                    lean_inc(v_fst_5475_);
                    v_snd_5476_ = lean_ctor_get(v_fst_5475_, 1);
                    v___x_5477_ = (lean_unbox(v_snd_5476_) as u8);
                    if v___x_5477_ == 0 {
                        v_snd_5478_ = lean_ctor_get(v___x_5474_, 1);
                        v_isSharedCheck_5547_ = (!lean_is_exclusive(v___x_5474_)) as u8;
                        if v_isSharedCheck_5547_ == 0 {
                            v_unused_5548_ = lean_ctor_get(v___x_5474_, 0);
                            lean_dec(v_unused_5548_);
                            v___x_5480_ = v___x_5474_;
                            v_isShared_5481_ = v_isSharedCheck_5547_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_5478_);
                            lean_dec(v___x_5474_);
                            v___x_5480_ = lean_box(0);
                            v_isShared_5481_ = v_isSharedCheck_5547_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_snd_5549_ = lean_ctor_get(v___x_5474_, 1);
                        v_isSharedCheck_5613_ = (!lean_is_exclusive(v___x_5474_)) as u8;
                        if v_isSharedCheck_5613_ == 0 {
                            v_unused_5614_ = lean_ctor_get(v___x_5474_, 0);
                            lean_dec(v_unused_5614_);
                            v___x_5551_ = v___x_5474_;
                            v_isShared_5552_ = v_isSharedCheck_5613_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_snd_5549_);
                            lean_dec(v___x_5474_);
                            v___x_5551_ = lean_box(0);
                            v_isShared_5552_ = v_isSharedCheck_5613_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_5459_);
                    v___x_5615_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5615_, 0, v_b_5463_);
                    return v___x_5615_;
                }
            }
            1 => {
                v_fst_5482_ = lean_ctor_get(v_fst_5475_, 0);
                v_isSharedCheck_5545_ = (!lean_is_exclusive(v_fst_5475_)) as u8;
                if v_isSharedCheck_5545_ == 0 {
                    v_unused_5546_ = lean_ctor_get(v_fst_5475_, 1);
                    lean_dec(v_unused_5546_);
                    v___x_5484_ = v_fst_5475_;
                    v_isShared_5485_ = v_isSharedCheck_5545_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fst_5482_);
                    lean_dec(v_fst_5475_);
                    v___x_5484_ = lean_box(0);
                    v_isShared_5485_ = v_isSharedCheck_5545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5486_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___lam__0(v___x_5471_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
                if lean_obj_tag(v___x_5486_) == 0 {
                    v_a_5487_ = lean_ctor_get(v___x_5486_, 0);
                    lean_inc_n(v_a_5487_, 5);
                    lean_dec_ref_known(v___x_5486_, 1);
                    v_quotContext_5488_ = lean_ctor_get(v___y_5468_, 10);
                    v_currMacroScope_5489_ = lean_ctor_get(v___y_5468_, 11);
                    v___x_5490_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__6;
                    v___x_5491_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__10;
                    v___x_5492_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__12);
                    v___x_5493_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__13;
                    lean_inc_n(v_currMacroScope_5489_, 2);
                    lean_inc_n(v_quotContext_5488_, 2);
                    v___x_5494_ = l_Lean_addMacroScope(
                        v_quotContext_5488_,
                        v___x_5493_,
                        v_currMacroScope_5489_,
                    );
                    v___x_5495_ = lean_box(0);
                    v___x_5496_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__16;
                    v___x_5497_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_5497_, 0, v_a_5487_);
                    lean_ctor_set(v___x_5497_, 1, v___x_5492_);
                    lean_ctor_set(v___x_5497_, 2, v___x_5494_);
                    lean_ctor_set(v___x_5497_, 3, v___x_5496_);
                    v___x_5498_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__18;
                    v___x_5499_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__20;
                    v___x_5500_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__22), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__22_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__22);
                    v___x_5501_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__23;
                    v___x_5502_ = l_Lean_addMacroScope(
                        v_quotContext_5488_,
                        v___x_5501_,
                        v_currMacroScope_5489_,
                    );
                    v___x_5503_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_5503_, 0, v_a_5487_);
                    lean_ctor_set(v___x_5503_, 1, v___x_5500_);
                    lean_ctor_set(v___x_5503_, 2, v___x_5502_);
                    lean_ctor_set(v___x_5503_, 3, v___x_5495_);
                    v___x_5504_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__25;
                    v___x_5505_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26);
                    v___x_5506_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_5506_, 0, v_a_5487_);
                    lean_ctor_set(v___x_5506_, 1, v___x_5504_);
                    lean_ctor_set(v___x_5506_, 2, v___x_5505_);
                    v___x_5507_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__27;
                    if v_isShared_5485_ == 0 {
                        lean_ctor_set_tag(v___x_5484_, 2);
                        lean_ctor_set(v___x_5484_, 1, v___x_5507_);
                        lean_ctor_set(v___x_5484_, 0, v_a_5487_);
                        v___x_5509_ = v___x_5484_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5536_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_a_5487_);
                        lean_ctor_set(v_reuseFailAlloc_5536_, 1, v___x_5507_);
                        v___x_5509_ = v_reuseFailAlloc_5536_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5484_);
                    lean_dec(v_fst_5482_);
                    lean_del_object(v___x_5480_);
                    lean_dec(v_snd_5478_);
                    lean_dec(v_b_5463_);
                    lean_dec(v___x_5459_);
                    v_a_5537_ = lean_ctor_get(v___x_5486_, 0);
                    v_isSharedCheck_5544_ = (!lean_is_exclusive(v___x_5486_)) as u8;
                    if v_isSharedCheck_5544_ == 0 {
                        v___x_5539_ = v___x_5486_;
                        v_isShared_5540_ = v_isSharedCheck_5544_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5537_);
                        lean_dec(v___x_5486_);
                        v___x_5539_ = lean_box(0);
                        v_isShared_5540_ = v_isSharedCheck_5544_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5510_ = l_Nat_reprFast(v_fst_5482_);
                v___x_5511_ = lean_box(2);
                v___x_5512_ = l_Lean_Syntax_mkNumLit(v___x_5510_, v___x_5511_);
                v___x_5513_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__28;
                lean_inc(v_a_5487_);
                if v_isShared_5481_ == 0 {
                    lean_ctor_set_tag(v___x_5480_, 2);
                    lean_ctor_set(v___x_5480_, 1, v___x_5513_);
                    lean_ctor_set(v___x_5480_, 0, v_a_5487_);
                    v___x_5515_ = v___x_5480_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5487_);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 1, v___x_5513_);
                    v___x_5515_ = v_reuseFailAlloc_5535_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5516_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__29;
                lean_inc_n(v_a_5487_, 11);
                v___x_5517_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5517_, 0, v_a_5487_);
                lean_ctor_set(v___x_5517_, 1, v___x_5516_);
                lean_inc_ref(v___x_5506_);
                v___x_5518_ = l_Lean_Syntax_node7(
                    v_a_5487_,
                    v___x_5499_,
                    v___x_5503_,
                    v___x_5506_,
                    v___x_5509_,
                    v___x_5512_,
                    v___x_5515_,
                    v___x_5506_,
                    v___x_5517_,
                );
                v___x_5519_ = l_Lean_Syntax_node1(v_a_5487_, v___x_5498_, v___x_5518_);
                v___x_5520_ = l_Lean_Syntax_node2(v_a_5487_, v___x_5491_, v___x_5497_, v___x_5519_);
                v___x_5521_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__30;
                v___x_5522_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5522_, 0, v_a_5487_);
                lean_ctor_set(v___x_5522_, 1, v___x_5521_);
                v___x_5523_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__31;
                v___x_5524_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__32;
                v___x_5525_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5525_, 0, v_a_5487_);
                lean_ctor_set(v___x_5525_, 1, v___x_5523_);
                v___x_5526_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__34;
                v___x_5527_ = l_Lean_Syntax_node1(v_a_5487_, v___x_5498_, v_snd_5478_);
                v___x_5528_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5528_, 0, v_a_5487_);
                lean_ctor_set(v___x_5528_, 1, v___x_5498_);
                lean_ctor_set(v___x_5528_, 2, v___x_5505_);
                v___x_5529_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__35;
                v___x_5530_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5530_, 0, v_a_5487_);
                lean_ctor_set(v___x_5530_, 1, v___x_5529_);
                v___x_5531_ = l_Lean_Syntax_node4(
                    v_a_5487_,
                    v___x_5526_,
                    v___x_5527_,
                    v___x_5528_,
                    v___x_5530_,
                    v_b_5463_,
                );
                v___x_5532_ = l_Lean_Syntax_node2(v_a_5487_, v___x_5524_, v___x_5525_, v___x_5531_);
                v___x_5533_ = l_Lean_Syntax_node3(
                    v_a_5487_,
                    v___x_5490_,
                    v___x_5520_,
                    v___x_5522_,
                    v___x_5532_,
                );
                v_i_5461_ = v___x_5473_;
                v_b_5463_ = v___x_5533_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_5540_ == 0 {
                    v___x_5542_ = v___x_5539_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5543_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5543_, 0, v_a_5537_);
                    v___x_5542_ = v_reuseFailAlloc_5543_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5542_;
            }
            7 => {
                v_fst_5553_ = lean_ctor_get(v_fst_5475_, 0);
                v_isSharedCheck_5611_ = (!lean_is_exclusive(v_fst_5475_)) as u8;
                if v_isSharedCheck_5611_ == 0 {
                    v_unused_5612_ = lean_ctor_get(v_fst_5475_, 1);
                    lean_dec(v_unused_5612_);
                    v___x_5555_ = v_fst_5475_;
                    v_isShared_5556_ = v_isSharedCheck_5611_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_fst_5553_);
                    lean_dec(v_fst_5475_);
                    v___x_5555_ = lean_box(0);
                    v_isShared_5556_ = v_isSharedCheck_5611_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5557_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___lam__0(v___x_5471_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
                if lean_obj_tag(v___x_5557_) == 0 {
                    v_a_5558_ = lean_ctor_get(v___x_5557_, 0);
                    lean_inc_n(v_a_5558_, 4);
                    lean_dec_ref_known(v___x_5557_, 1);
                    v_quotContext_5559_ = lean_ctor_get(v___y_5468_, 10);
                    v_currMacroScope_5560_ = lean_ctor_get(v___y_5468_, 11);
                    v___x_5561_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__6;
                    v___x_5562_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__10;
                    v___x_5563_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__18;
                    v___x_5564_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__20;
                    v___x_5565_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__22), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__22_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__22);
                    v___x_5566_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__23;
                    lean_inc(v_currMacroScope_5560_);
                    lean_inc(v_quotContext_5559_);
                    v___x_5567_ = l_Lean_addMacroScope(
                        v_quotContext_5559_,
                        v___x_5566_,
                        v_currMacroScope_5560_,
                    );
                    v___x_5568_ = lean_box(0);
                    v___x_5569_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_5569_, 0, v_a_5558_);
                    lean_ctor_set(v___x_5569_, 1, v___x_5565_);
                    lean_ctor_set(v___x_5569_, 2, v___x_5567_);
                    lean_ctor_set(v___x_5569_, 3, v___x_5568_);
                    v___x_5570_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__25;
                    v___x_5571_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26);
                    v___x_5572_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_5572_, 0, v_a_5558_);
                    lean_ctor_set(v___x_5572_, 1, v___x_5570_);
                    lean_ctor_set(v___x_5572_, 2, v___x_5571_);
                    v___x_5573_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__27;
                    if v_isShared_5556_ == 0 {
                        lean_ctor_set_tag(v___x_5555_, 2);
                        lean_ctor_set(v___x_5555_, 1, v___x_5573_);
                        lean_ctor_set(v___x_5555_, 0, v_a_5558_);
                        v___x_5575_ = v___x_5555_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_5602_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_a_5558_);
                        lean_ctor_set(v_reuseFailAlloc_5602_, 1, v___x_5573_);
                        v___x_5575_ = v_reuseFailAlloc_5602_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5555_);
                    lean_dec(v_fst_5553_);
                    lean_del_object(v___x_5551_);
                    lean_dec(v_snd_5549_);
                    lean_dec(v_b_5463_);
                    lean_dec(v___x_5459_);
                    v_a_5603_ = lean_ctor_get(v___x_5557_, 0);
                    v_isSharedCheck_5610_ = (!lean_is_exclusive(v___x_5557_)) as u8;
                    if v_isSharedCheck_5610_ == 0 {
                        v___x_5605_ = v___x_5557_;
                        v_isShared_5606_ = v_isSharedCheck_5610_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5603_);
                        lean_dec(v___x_5557_);
                        v___x_5605_ = lean_box(0);
                        v_isShared_5606_ = v_isSharedCheck_5610_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                v___x_5576_ = l_Nat_reprFast(v_fst_5553_);
                v___x_5577_ = lean_box(2);
                v___x_5578_ = l_Lean_Syntax_mkNumLit(v___x_5576_, v___x_5577_);
                v___x_5579_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__28;
                lean_inc(v_a_5558_);
                if v_isShared_5552_ == 0 {
                    lean_ctor_set_tag(v___x_5551_, 2);
                    lean_ctor_set(v___x_5551_, 1, v___x_5579_);
                    lean_ctor_set(v___x_5551_, 0, v_a_5558_);
                    v___x_5581_ = v___x_5551_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5601_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_a_5558_);
                    lean_ctor_set(v_reuseFailAlloc_5601_, 1, v___x_5579_);
                    v___x_5581_ = v_reuseFailAlloc_5601_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5582_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__29;
                lean_inc_n(v_a_5558_, 11);
                v___x_5583_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5583_, 0, v_a_5558_);
                lean_ctor_set(v___x_5583_, 1, v___x_5582_);
                lean_inc_ref(v___x_5572_);
                v___x_5584_ = l_Lean_Syntax_node7(
                    v_a_5558_,
                    v___x_5564_,
                    v___x_5569_,
                    v___x_5572_,
                    v___x_5575_,
                    v___x_5578_,
                    v___x_5581_,
                    v___x_5572_,
                    v___x_5583_,
                );
                v___x_5585_ = l_Lean_Syntax_node1(v_a_5558_, v___x_5563_, v___x_5584_);
                lean_inc(v___x_5459_);
                v___x_5586_ = l_Lean_Syntax_node2(v_a_5558_, v___x_5562_, v___x_5459_, v___x_5585_);
                v___x_5587_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__30;
                v___x_5588_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5588_, 0, v_a_5558_);
                lean_ctor_set(v___x_5588_, 1, v___x_5587_);
                v___x_5589_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__31;
                v___x_5590_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__32;
                v___x_5591_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5591_, 0, v_a_5558_);
                lean_ctor_set(v___x_5591_, 1, v___x_5589_);
                v___x_5592_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__34;
                v___x_5593_ = l_Lean_Syntax_node1(v_a_5558_, v___x_5563_, v_snd_5549_);
                v___x_5594_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5594_, 0, v_a_5558_);
                lean_ctor_set(v___x_5594_, 1, v___x_5563_);
                lean_ctor_set(v___x_5594_, 2, v___x_5571_);
                v___x_5595_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__35;
                v___x_5596_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5596_, 0, v_a_5558_);
                lean_ctor_set(v___x_5596_, 1, v___x_5595_);
                v___x_5597_ = l_Lean_Syntax_node4(
                    v_a_5558_,
                    v___x_5592_,
                    v___x_5593_,
                    v___x_5594_,
                    v___x_5596_,
                    v_b_5463_,
                );
                v___x_5598_ = l_Lean_Syntax_node2(v_a_5558_, v___x_5590_, v___x_5591_, v___x_5597_);
                v___x_5599_ = l_Lean_Syntax_node3(
                    v_a_5558_,
                    v___x_5561_,
                    v___x_5586_,
                    v___x_5588_,
                    v___x_5598_,
                );
                v_i_5461_ = v___x_5473_;
                v_b_5463_ = v___x_5599_;
                state = 0;
                continue;
            }
            11 => {
                if v_isShared_5606_ == 0 {
                    v___x_5608_ = v___x_5605_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5609_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5603_);
                    v___x_5608_ = v_reuseFailAlloc_5609_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___boxed(
    mut v___x_5616_: *mut LeanObject,
    mut v_as_5617_: *mut LeanObject,
    mut v_i_5618_: *mut LeanObject,
    mut v_stop_5619_: *mut LeanObject,
    mut v_b_5620_: *mut LeanObject,
    mut v___y_5621_: *mut LeanObject,
    mut v___y_5622_: *mut LeanObject,
    mut v___y_5623_: *mut LeanObject,
    mut v___y_5624_: *mut LeanObject,
    mut v___y_5625_: *mut LeanObject,
    mut v___y_5626_: *mut LeanObject,
    mut v___y_5627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5628_: usize = 0;
    let mut v_stop_boxed_5629_: usize = 0;
    let mut v_res_5630_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5628_ = lean_unbox_usize(v_i_5618_);
    lean_dec(v_i_5618_);
    v_stop_boxed_5629_ = lean_unbox_usize(v_stop_5619_);
    lean_dec(v_stop_5619_);
    v_res_5630_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4(v___x_5616_, v_as_5617_, v_i_boxed_5628_, v_stop_boxed_5629_, v_b_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_);
    lean_dec(v___y_5626_);
    lean_dec_ref(v___y_5625_);
    lean_dec(v___y_5624_);
    lean_dec_ref(v___y_5623_);
    lean_dec(v___y_5622_);
    lean_dec_ref(v___y_5621_);
    lean_dec_ref(v_as_5617_);
    return v_res_5630_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg(
    mut v_sz_5634_: usize,
    mut v_i_5635_: usize,
    mut v_bs_5636_: *mut LeanObject,
    mut v___y_5637_: *mut LeanObject,
    mut v___y_5638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5640_: u8 = 0;
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: usize = 0;
    let mut v___x_5649_: usize = 0;
    let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5655_: u8 = 0;
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5640_ = lean_usize_dec_lt(v_i_5635_, v_sz_5634_);
                if v___x_5640_ == 0 {
                    v___x_5641_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5641_, 0, v_bs_5636_);
                    return v___x_5641_;
                } else {
                    v___x_5642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg___closed__1;
                    v___x_5643_ =
                        l_Lean_Core_mkFreshUserName(v___x_5642_, v___y_5637_, v___y_5638_);
                    if lean_obj_tag(v___x_5643_) == 0 {
                        v_a_5644_ = lean_ctor_get(v___x_5643_, 0);
                        lean_inc(v_a_5644_);
                        lean_dec_ref_known(v___x_5643_, 1);
                        v___x_5645_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5646_ = lean_array_uset(v_bs_5636_, v_i_5635_, v___x_5645_);
                        v___x_5647_ = lean_mk_syntax_ident(v_a_5644_);
                        v___x_5648_ = 1usize;
                        v___x_5649_ = lean_usize_add(v_i_5635_, v___x_5648_);
                        v___x_5650_ = lean_array_uset(v_bs_x27_5646_, v_i_5635_, v___x_5647_);
                        v_i_5635_ = v___x_5649_;
                        v_bs_5636_ = v___x_5650_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5636_);
                        v_a_5652_ = lean_ctor_get(v___x_5643_, 0);
                        v_isSharedCheck_5659_ = (!lean_is_exclusive(v___x_5643_)) as u8;
                        if v_isSharedCheck_5659_ == 0 {
                            v___x_5654_ = v___x_5643_;
                            v_isShared_5655_ = v_isSharedCheck_5659_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5652_);
                            lean_dec(v___x_5643_);
                            v___x_5654_ = lean_box(0);
                            v_isShared_5655_ = v_isSharedCheck_5659_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5655_ == 0 {
                    v___x_5657_ = v___x_5654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5658_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_a_5652_);
                    v___x_5657_ = v_reuseFailAlloc_5658_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5657_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg___boxed(
    mut v_sz_5660_: *mut LeanObject,
    mut v_i_5661_: *mut LeanObject,
    mut v_bs_5662_: *mut LeanObject,
    mut v___y_5663_: *mut LeanObject,
    mut v___y_5664_: *mut LeanObject,
    mut v___y_5665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5666_: usize = 0;
    let mut v_i_boxed_5667_: usize = 0;
    let mut v_res_5668_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5666_ = lean_unbox_usize(v_sz_5660_);
    lean_dec(v_sz_5660_);
    v_i_boxed_5667_ = lean_unbox_usize(v_i_5661_);
    lean_dec(v_i_5661_);
    v_res_5668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg(v_sz_boxed_5666_, v_i_boxed_5667_, v_bs_5662_, v___y_5663_, v___y_5664_);
    lean_dec(v___y_5664_);
    lean_dec_ref(v___y_5663_);
    return v_res_5668_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__2(
    mut v_sz_5669_: usize,
    mut v_i_5670_: usize,
    mut v_bs_5671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5672_: u8 = 0;
    let mut v_v_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: usize = 0;
    let mut v___x_5677_: usize = 0;
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5672_ = lean_usize_dec_lt(v_i_5670_, v_sz_5669_);
                if v___x_5672_ == 0 {
                    return v_bs_5671_;
                } else {
                    v_v_5673_ = lean_array_uget(v_bs_5671_, v_i_5670_);
                    v___x_5674_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5675_ = lean_array_uset(v_bs_5671_, v_i_5670_, v___x_5674_);
                    v___x_5676_ = 1usize;
                    v___x_5677_ = lean_usize_add(v_i_5670_, v___x_5676_);
                    v___x_5678_ = lean_array_uset(v_bs_x27_5675_, v_i_5670_, v_v_5673_);
                    v_i_5670_ = v___x_5677_;
                    v_bs_5671_ = v___x_5678_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__2___boxed(
    mut v_sz_5680_: *mut LeanObject,
    mut v_i_5681_: *mut LeanObject,
    mut v_bs_5682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5683_: usize = 0;
    let mut v_i_boxed_5684_: usize = 0;
    let mut v_res_5685_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5683_ = lean_unbox_usize(v_sz_5680_);
    lean_dec(v_sz_5680_);
    v_i_boxed_5684_ = lean_unbox_usize(v_i_5681_);
    lean_dec(v_i_5681_);
    v_res_5685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__2(v_sz_boxed_5683_, v_i_boxed_5684_, v_bs_5682_);
    return v_res_5685_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
    v___x_5692_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__1;
    v___x_5693_ = l_String_toRawSubstring_x27(v___x_5692_);
    return v___x_5693_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__16()
-> *mut LeanObject {
    let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    v___x_5723_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__15;
    v___x_5724_ = l_String_toRawSubstring_x27(v___x_5723_);
    return v___x_5724_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__40()
-> *mut LeanObject {
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    v___x_5781_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__39;
    v___x_5782_ = l_String_toRawSubstring_x27(v___x_5781_);
    return v___x_5782_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__47()
-> *mut LeanObject {
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    v___x_5795_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__46;
    v___x_5796_ = l_String_toRawSubstring_x27(v___x_5795_);
    return v___x_5796_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__55()
-> *mut LeanObject {
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    v___x_5806_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__54;
    v___x_5807_ = lean_unsigned_to_nat(43);
    v___x_5808_ = lean_unsigned_to_nat(53);
    v___x_5809_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__53;
    v___x_5810_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__52;
    v___x_5811_ = l_mkPanicMessageWithDecl(
        v___x_5810_,
        v___x_5809_,
        v___x_5808_,
        v___x_5807_,
        v___x_5806_,
    );
    return v___x_5811_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg(
    mut v_a_5812_: *mut LeanObject,
    mut v_type_x27_5813_: *mut LeanObject,
    mut v___x_5814_: *mut LeanObject,
    mut v_as_x27_5815_: *mut LeanObject,
    mut v_b_5816_: *mut LeanObject,
    mut v___y_5817_: *mut LeanObject,
    mut v___y_5818_: *mut LeanObject,
    mut v___y_5819_: *mut LeanObject,
    mut v___y_5820_: *mut LeanObject,
    mut v___y_5821_: *mut LeanObject,
    mut v___y_5822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: u8 = 0;
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: u8 = 0;
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5840_: u8 = 0;
    let mut v_str_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5842_: usize = 0;
    let mut v___x_5843_: usize = 0;
    let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5871_: usize = 0;
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: u8 = 0;
    let mut v___x_5927_: usize = 0;
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5933_: u8 = 0;
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5937_: u8 = 0;
    let mut v_a_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5941_: u8 = 0;
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5945_: u8 = 0;
    let mut v_a_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5949_: u8 = 0;
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5953_: u8 = 0;
    let mut v_isSharedCheck_5954_: u8 = 0;
    let mut v_unused_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5962_: u8 = 0;
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5966_: u8 = 0;
    let mut v_a_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5970_: u8 = 0;
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5974_: u8 = 0;
    let mut v_a_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5978_: u8 = 0;
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_5815_) == 0 {
                    lean_dec(v___x_5814_);
                    v___x_5824_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5824_, 0, v_b_5816_);
                    return v___x_5824_;
                } else {
                    v_head_5825_ = lean_ctor_get(v_as_x27_5815_, 0);
                    v_tail_5826_ = lean_ctor_get(v_as_x27_5815_, 1);
                    v___x_5827_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_useCtor(v_a_5812_, v_head_5825_);
                    if v___x_5827_ == 0 {
                        v_as_x27_5815_ = v_tail_5826_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5829_ = lean_box(0);
                        lean_inc(v_head_5825_);
                        v___x_5830_ = l_Lean_mkConst(v_head_5825_, v___x_5829_);
                        lean_inc(v___y_5822_);
                        lean_inc_ref(v___y_5821_);
                        lean_inc(v___y_5820_);
                        lean_inc_ref(v___y_5819_);
                        v___x_5831_ = lean_infer_type(
                            v___x_5830_,
                            v___y_5819_,
                            v___y_5820_,
                            v___y_5821_,
                            v___y_5822_,
                        );
                        if lean_obj_tag(v___x_5831_) == 0 {
                            v_a_5832_ = lean_ctor_get(v___x_5831_, 0);
                            lean_inc(v_a_5832_);
                            lean_dec_ref_known(v___x_5831_, 1);
                            v___x_5833_ = lean_box(0);
                            v___x_5834_ = 0;
                            v___x_5835_ = l_Lean_Meta_forallMetaTelescopeReducing(
                                v_a_5832_,
                                v___x_5833_,
                                v___x_5834_,
                                v___y_5819_,
                                v___y_5820_,
                                v___y_5821_,
                                v___y_5822_,
                            );
                            if lean_obj_tag(v___x_5835_) == 0 {
                                v_a_5836_ = lean_ctor_get(v___x_5835_, 0);
                                lean_inc(v_a_5836_);
                                lean_dec_ref_known(v___x_5835_, 1);
                                if lean_obj_tag(v_head_5825_) == 1 {
                                    v_fst_5837_ = lean_ctor_get(v_a_5836_, 0);
                                    v_isSharedCheck_5954_ = (!lean_is_exclusive(v_a_5836_)) as u8;
                                    if v_isSharedCheck_5954_ == 0 {
                                        v_unused_5955_ = lean_ctor_get(v_a_5836_, 1);
                                        lean_dec(v_unused_5955_);
                                        v___x_5839_ = v_a_5836_;
                                        v_isShared_5840_ = v_isSharedCheck_5954_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_fst_5837_);
                                        lean_dec(v_a_5836_);
                                        v___x_5839_ = lean_box(0);
                                        v_isShared_5840_ = v_isSharedCheck_5954_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_5836_);
                                    v___x_5956_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__55), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__55_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__55);
                                    v___x_5957_ = l_panic___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__5(v___x_5956_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_);
                                    if lean_obj_tag(v___x_5957_) == 0 {
                                        lean_dec_ref_known(v___x_5957_, 1);
                                        v_as_x27_5815_ = v_tail_5826_;
                                        state = 0;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_b_5816_);
                                        lean_dec(v___x_5814_);
                                        v_a_5959_ = lean_ctor_get(v___x_5957_, 0);
                                        v_isSharedCheck_5966_ =
                                            (!lean_is_exclusive(v___x_5957_)) as u8;
                                        if v_isSharedCheck_5966_ == 0 {
                                            v___x_5961_ = v___x_5957_;
                                            v_isShared_5962_ = v_isSharedCheck_5966_;
                                            state = 10;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5959_);
                                            lean_dec(v___x_5957_);
                                            v___x_5961_ = lean_box(0);
                                            v_isShared_5962_ = v_isSharedCheck_5966_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v_b_5816_);
                                lean_dec(v___x_5814_);
                                v_a_5967_ = lean_ctor_get(v___x_5835_, 0);
                                v_isSharedCheck_5974_ = (!lean_is_exclusive(v___x_5835_)) as u8;
                                if v_isSharedCheck_5974_ == 0 {
                                    v___x_5969_ = v___x_5835_;
                                    v_isShared_5970_ = v_isSharedCheck_5974_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_5967_);
                                    lean_dec(v___x_5835_);
                                    v___x_5969_ = lean_box(0);
                                    v_isShared_5970_ = v_isSharedCheck_5974_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_b_5816_);
                            lean_dec(v___x_5814_);
                            v_a_5975_ = lean_ctor_get(v___x_5831_, 0);
                            v_isSharedCheck_5982_ = (!lean_is_exclusive(v___x_5831_)) as u8;
                            if v_isSharedCheck_5982_ == 0 {
                                v___x_5977_ = v___x_5831_;
                                v_isShared_5978_ = v_isSharedCheck_5982_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_5975_);
                                lean_dec(v___x_5831_);
                                v___x_5977_ = lean_box(0);
                                v_isShared_5978_ = v_isSharedCheck_5982_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_str_5841_ = lean_ctor_get(v_head_5825_, 1);
                v_sz_5842_ = lean_array_size(v_fst_5837_);
                v___x_5843_ = 0usize;
                lean_inc(v_fst_5837_);
                v___x_5844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg(v_sz_5842_, v___x_5843_, v_fst_5837_, v___y_5821_, v___y_5822_);
                if lean_obj_tag(v___x_5844_) == 0 {
                    v_a_5845_ = lean_ctor_get(v___x_5844_, 0);
                    lean_inc_n(v_a_5845_, 2);
                    lean_dec_ref_known(v___x_5844_, 1);
                    v___x_5846_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__0(
                        v___y_5817_,
                        v___y_5818_,
                        v___y_5819_,
                        v___y_5820_,
                        v___y_5821_,
                        v___y_5822_,
                    );
                    v_a_5847_ = lean_ctor_get(v___x_5846_, 0);
                    lean_inc_n(v_a_5847_, 9);
                    lean_dec_ref(v___x_5846_);
                    v_quotContext_5848_ = lean_ctor_get(v___y_5821_, 10);
                    v_currMacroScope_5849_ = lean_ctor_get(v___y_5821_, 11);
                    v___x_5850_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__10;
                    v___x_5851_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__2);
                    v___x_5852_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__3;
                    lean_inc_n(v_currMacroScope_5849_, 2);
                    lean_inc_n(v_quotContext_5848_, 2);
                    v___x_5853_ = l_Lean_addMacroScope(
                        v_quotContext_5848_,
                        v___x_5852_,
                        v_currMacroScope_5849_,
                    );
                    v___x_5854_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__7;
                    v___x_5855_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_5855_, 0, v_a_5847_);
                    lean_ctor_set(v___x_5855_, 1, v___x_5851_);
                    lean_ctor_set(v___x_5855_, 2, v___x_5853_);
                    lean_ctor_set(v___x_5855_, 3, v___x_5854_);
                    v___x_5856_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__18;
                    v___x_5857_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__9;
                    v___x_5858_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__11;
                    v___x_5859_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__12;
                    v___x_5860_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_5860_, 0, v_a_5847_);
                    lean_ctor_set(v___x_5860_, 1, v___x_5859_);
                    v___x_5861_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__14;
                    v___x_5862_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__16), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__16_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__16);
                    v___x_5863_ = lean_box(0);
                    v___x_5864_ = l_Lean_addMacroScope(
                        v_quotContext_5848_,
                        v___x_5863_,
                        v_currMacroScope_5849_,
                    );
                    v___x_5865_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__35;
                    lean_inc(v___x_5864_);
                    v___x_5866_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_5866_, 0, v_a_5847_);
                    lean_ctor_set(v___x_5866_, 1, v___x_5862_);
                    lean_ctor_set(v___x_5866_, 2, v___x_5864_);
                    lean_ctor_set(v___x_5866_, 3, v___x_5865_);
                    v___x_5867_ = l_Lean_Syntax_node1(v_a_5847_, v___x_5861_, v___x_5866_);
                    v___x_5868_ =
                        l_Lean_Syntax_node2(v_a_5847_, v___x_5858_, v___x_5860_, v___x_5867_);
                    lean_inc_ref(v_head_5825_);
                    v___x_5869_ = l_Lean_mkCIdent(v_head_5825_);
                    v___x_5870_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26);
                    v_sz_5871_ = lean_array_size(v_a_5845_);
                    v___x_5872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__2(v_sz_5871_, v___x_5843_, v_a_5845_);
                    v___x_5873_ = l_Array_append___redArg(v___x_5870_, v___x_5872_);
                    lean_dec_ref(v___x_5872_);
                    v___x_5874_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_5874_, 0, v_a_5847_);
                    lean_ctor_set(v___x_5874_, 1, v___x_5856_);
                    lean_ctor_set(v___x_5874_, 2, v___x_5873_);
                    v___x_5875_ =
                        l_Lean_Syntax_node2(v_a_5847_, v___x_5850_, v___x_5869_, v___x_5874_);
                    v___x_5876_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__36;
                    v___x_5877_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_5877_, 0, v_a_5847_);
                    lean_ctor_set(v___x_5877_, 1, v___x_5876_);
                    lean_inc(v_fst_5837_);
                    v___x_5878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__3(v_type_x27_5813_, v_sz_5842_, v___x_5843_, v_fst_5837_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_);
                    if lean_obj_tag(v___x_5878_) == 0 {
                        v_a_5879_ = lean_ctor_get(v___x_5878_, 0);
                        lean_inc(v_a_5879_);
                        lean_dec_ref_known(v___x_5878_, 1);
                        lean_inc_n(v_a_5847_, 2);
                        v___x_5880_ = l_Lean_Syntax_node3(
                            v_a_5847_,
                            v___x_5857_,
                            v___x_5868_,
                            v___x_5875_,
                            v___x_5877_,
                        );
                        v___x_5881_ = l_Lean_Syntax_node1(v_a_5847_, v___x_5856_, v___x_5880_);
                        v___x_5882_ =
                            l_Lean_Syntax_node2(v_a_5847_, v___x_5850_, v___x_5855_, v___x_5881_);
                        v___x_5883_ = lean_array_get_size(v_fst_5837_);
                        lean_dec(v_fst_5837_);
                        v___x_5921_ = l_Array_range(v___x_5883_);
                        v___x_5922_ = l_Array_zip___redArg(v___x_5921_, v_a_5879_);
                        lean_dec(v_a_5879_);
                        lean_dec_ref(v___x_5921_);
                        v___x_5923_ = l_Array_zip___redArg(v___x_5922_, v_a_5845_);
                        lean_dec(v_a_5845_);
                        lean_dec_ref(v___x_5922_);
                        v___x_5924_ = lean_array_get_size(v___x_5923_);
                        v___x_5925_ = lean_unsigned_to_nat(0);
                        v___x_5926_ = lean_nat_dec_lt(v___x_5925_, v___x_5924_);
                        if v___x_5926_ == 0 {
                            lean_dec_ref(v___x_5923_);
                            v_a_5885_ = v___x_5882_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5927_ = lean_usize_of_nat(v___x_5924_);
                            lean_inc(v___x_5814_);
                            v___x_5928_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4(v___x_5814_, v___x_5923_, v___x_5927_, v___x_5843_, v___x_5882_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_);
                            lean_dec_ref(v___x_5923_);
                            if lean_obj_tag(v___x_5928_) == 0 {
                                v_a_5929_ = lean_ctor_get(v___x_5928_, 0);
                                lean_inc(v_a_5929_);
                                lean_dec_ref_known(v___x_5928_, 1);
                                v_a_5885_ = v_a_5929_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_5864_);
                                lean_del_object(v___x_5839_);
                                lean_dec_ref(v_b_5816_);
                                lean_dec(v___x_5814_);
                                v_a_5930_ = lean_ctor_get(v___x_5928_, 0);
                                v_isSharedCheck_5937_ = (!lean_is_exclusive(v___x_5928_)) as u8;
                                if v_isSharedCheck_5937_ == 0 {
                                    v___x_5932_ = v___x_5928_;
                                    v_isShared_5933_ = v_isSharedCheck_5937_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_5930_);
                                    lean_dec(v___x_5928_);
                                    v___x_5932_ = lean_box(0);
                                    v_isShared_5933_ = v_isSharedCheck_5937_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref_known(v___x_5877_, 2);
                        lean_dec(v___x_5875_);
                        lean_dec(v___x_5868_);
                        lean_dec(v___x_5864_);
                        lean_dec_ref_known(v___x_5855_, 4);
                        lean_dec(v_a_5847_);
                        lean_dec(v_a_5845_);
                        lean_del_object(v___x_5839_);
                        lean_dec(v_fst_5837_);
                        lean_dec_ref(v_b_5816_);
                        lean_dec(v___x_5814_);
                        v_a_5938_ = lean_ctor_get(v___x_5878_, 0);
                        v_isSharedCheck_5945_ = (!lean_is_exclusive(v___x_5878_)) as u8;
                        if v_isSharedCheck_5945_ == 0 {
                            v___x_5940_ = v___x_5878_;
                            v_isShared_5941_ = v_isSharedCheck_5945_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5938_);
                            lean_dec(v___x_5878_);
                            v___x_5940_ = lean_box(0);
                            v_isShared_5941_ = v_isSharedCheck_5945_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5839_);
                    lean_dec(v_fst_5837_);
                    lean_dec_ref(v_b_5816_);
                    lean_dec(v___x_5814_);
                    v_a_5946_ = lean_ctor_get(v___x_5844_, 0);
                    v_isSharedCheck_5953_ = (!lean_is_exclusive(v___x_5844_)) as u8;
                    if v_isSharedCheck_5953_ == 0 {
                        v___x_5948_ = v___x_5844_;
                        v_isShared_5949_ = v_isSharedCheck_5953_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5946_);
                        lean_dec(v___x_5844_);
                        v___x_5948_ = lean_box(0);
                        v_isShared_5949_ = v_isSharedCheck_5953_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5886_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__0(
                    v___y_5817_,
                    v___y_5818_,
                    v___y_5819_,
                    v___y_5820_,
                    v___y_5821_,
                    v___y_5822_,
                );
                v_a_5887_ = lean_ctor_get(v___x_5886_, 0);
                lean_inc_n(v_a_5887_, 14);
                lean_dec_ref(v___x_5886_);
                v___x_5888_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__38;
                v___x_5889_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__40), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__40_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__40);
                v___x_5890_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__41;
                lean_inc_n(v_currMacroScope_5849_, 2);
                lean_inc_n(v_quotContext_5848_, 2);
                v___x_5891_ =
                    l_Lean_addMacroScope(v_quotContext_5848_, v___x_5890_, v_currMacroScope_5849_);
                v___x_5892_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__43;
                v___x_5893_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5893_, 0, v_a_5887_);
                lean_ctor_set(v___x_5893_, 1, v___x_5889_);
                lean_ctor_set(v___x_5893_, 2, v___x_5891_);
                lean_ctor_set(v___x_5893_, 3, v___x_5892_);
                v___x_5894_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5894_, 0, v_a_5887_);
                lean_ctor_set(v___x_5894_, 1, v___x_5859_);
                v___x_5895_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5895_, 0, v_a_5887_);
                lean_ctor_set(v___x_5895_, 1, v___x_5862_);
                lean_ctor_set(v___x_5895_, 2, v___x_5864_);
                lean_ctor_set(v___x_5895_, 3, v___x_5865_);
                v___x_5896_ = l_Lean_Syntax_node1(v_a_5887_, v___x_5861_, v___x_5895_);
                v___x_5897_ = l_Lean_Syntax_node2(v_a_5887_, v___x_5858_, v___x_5894_, v___x_5896_);
                v___x_5898_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__45;
                v___x_5899_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__47), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__47_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__47);
                v___x_5900_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__49;
                v___x_5901_ =
                    l_Lean_addMacroScope(v_quotContext_5848_, v___x_5900_, v_currMacroScope_5849_);
                v___x_5902_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5902_, 0, v_a_5887_);
                lean_ctor_set(v___x_5902_, 1, v___x_5899_);
                lean_ctor_set(v___x_5902_, 2, v___x_5901_);
                lean_ctor_set(v___x_5902_, 3, v___x_5829_);
                v___x_5903_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__50;
                v___x_5904_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5904_, 0, v_a_5887_);
                lean_ctor_set(v___x_5904_, 1, v___x_5903_);
                v___x_5905_ = l_Nat_reprFast(v___x_5883_);
                v___x_5906_ = lean_box(2);
                v___x_5907_ = l_Lean_Syntax_mkNumLit(v___x_5905_, v___x_5906_);
                v___x_5908_ = l_Lean_Syntax_node3(
                    v_a_5887_,
                    v___x_5898_,
                    v___x_5902_,
                    v___x_5904_,
                    v___x_5907_,
                );
                v___x_5909_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5909_, 0, v_a_5887_);
                lean_ctor_set(v___x_5909_, 1, v___x_5876_);
                v___x_5910_ = l_Lean_Syntax_node3(
                    v_a_5887_,
                    v___x_5857_,
                    v___x_5897_,
                    v___x_5908_,
                    v___x_5909_,
                );
                v___x_5911_ = l_Lean_Syntax_node1(v_a_5887_, v___x_5856_, v___x_5910_);
                v___x_5912_ = l_Lean_Syntax_node2(v_a_5887_, v___x_5850_, v___x_5893_, v___x_5911_);
                v___x_5913_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__51;
                v___x_5914_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5914_, 0, v_a_5887_);
                lean_ctor_set(v___x_5914_, 1, v___x_5913_);
                v___x_5915_ = l_Lean_Syntax_node3(
                    v_a_5887_,
                    v___x_5888_,
                    v___x_5912_,
                    v___x_5914_,
                    v_a_5885_,
                );
                lean_inc_ref(v_str_5841_);
                if v_isShared_5840_ == 0 {
                    lean_ctor_set(v___x_5839_, 1, v___x_5915_);
                    lean_ctor_set(v___x_5839_, 0, v_str_5841_);
                    v___x_5917_ = v___x_5839_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5920_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_str_5841_);
                    lean_ctor_set(v_reuseFailAlloc_5920_, 1, v___x_5915_);
                    v___x_5917_ = v_reuseFailAlloc_5920_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5918_ = lean_array_push(v_b_5816_, v___x_5917_);
                v_as_x27_5815_ = v_tail_5826_;
                v_b_5816_ = v___x_5918_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_5933_ == 0 {
                    v___x_5935_ = v___x_5932_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5936_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 0, v_a_5930_);
                    v___x_5935_ = v_reuseFailAlloc_5936_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5935_;
            }
            6 => {
                if v_isShared_5941_ == 0 {
                    v___x_5943_ = v___x_5940_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5944_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5944_, 0, v_a_5938_);
                    v___x_5943_ = v_reuseFailAlloc_5944_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5943_;
            }
            8 => {
                if v_isShared_5949_ == 0 {
                    v___x_5951_ = v___x_5948_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5952_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_a_5946_);
                    v___x_5951_ = v_reuseFailAlloc_5952_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5951_;
            }
            10 => {
                if v_isShared_5962_ == 0 {
                    v___x_5964_ = v___x_5961_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5965_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5965_, 0, v_a_5959_);
                    v___x_5964_ = v_reuseFailAlloc_5965_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5964_;
            }
            12 => {
                if v_isShared_5970_ == 0 {
                    v___x_5972_ = v___x_5969_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5973_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5973_, 0, v_a_5967_);
                    v___x_5972_ = v_reuseFailAlloc_5973_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5972_;
            }
            14 => {
                if v_isShared_5978_ == 0 {
                    v___x_5980_ = v___x_5977_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5981_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5981_, 0, v_a_5975_);
                    v___x_5980_ = v_reuseFailAlloc_5981_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___boxed(
    mut v_a_5983_: *mut LeanObject,
    mut v_type_x27_5984_: *mut LeanObject,
    mut v___x_5985_: *mut LeanObject,
    mut v_as_x27_5986_: *mut LeanObject,
    mut v_b_5987_: *mut LeanObject,
    mut v___y_5988_: *mut LeanObject,
    mut v___y_5989_: *mut LeanObject,
    mut v___y_5990_: *mut LeanObject,
    mut v___y_5991_: *mut LeanObject,
    mut v___y_5992_: *mut LeanObject,
    mut v___y_5993_: *mut LeanObject,
    mut v___y_5994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5995_: *mut LeanObject = core::ptr::null_mut();
    v_res_5995_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg(
            v_a_5983_,
            v_type_x27_5984_,
            v___x_5985_,
            v_as_x27_5986_,
            v_b_5987_,
            v___y_5988_,
            v___y_5989_,
            v___y_5990_,
            v___y_5991_,
            v___y_5992_,
            v___y_5993_,
        );
    lean_dec(v___y_5993_);
    lean_dec_ref(v___y_5992_);
    lean_dec(v___y_5991_);
    lean_dec_ref(v___y_5990_);
    lean_dec(v___y_5989_);
    lean_dec_ref(v___y_5988_);
    lean_dec(v_as_x27_5986_);
    lean_dec_ref(v_type_x27_5984_);
    lean_dec_ref(v_a_5983_);
    return v_res_5995_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__4() -> *mut LeanObject
{
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    v___x_6003_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__3;
    v___x_6004_ = l_String_toRawSubstring_x27(v___x_6003_);
    return v___x_6004_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__7() -> *mut LeanObject
{
    let mut v___x_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    v___x_6008_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__6;
    v___x_6009_ = l_String_toRawSubstring_x27(v___x_6008_);
    return v___x_6009_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__20() -> *mut LeanObject
{
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
    v___x_6023_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__2;
    v___x_6024_ = l_String_toRawSubstring_x27(v___x_6023_);
    return v___x_6024_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__24() -> *mut LeanObject
{
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    v___x_6029_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__23;
    v___x_6030_ = l_String_toRawSubstring_x27(v___x_6029_);
    return v___x_6030_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__27() -> *mut LeanObject
{
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    v___x_6034_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__26;
    v___x_6035_ = l_String_toRawSubstring_x27(v___x_6034_);
    return v___x_6035_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__34() -> *mut LeanObject
{
    let mut v___x_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    v___x_6049_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__33;
    v___x_6050_ = l_String_toRawSubstring_x27(v___x_6049_);
    return v___x_6050_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__48() -> *mut LeanObject
{
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut LeanObject = core::ptr::null_mut();
    v___x_6068_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__47;
    v___x_6069_ = l_String_toRawSubstring_x27(v___x_6068_);
    return v___x_6069_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__52() -> *mut LeanObject
{
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    v___x_6074_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__51;
    v___x_6075_ = l_String_toRawSubstring_x27(v___x_6074_);
    return v___x_6075_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__57() -> *mut LeanObject
{
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    v___x_6081_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__56;
    v___x_6082_ = l_String_toRawSubstring_x27(v___x_6081_);
    return v___x_6082_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1(
    mut v_cmdRef_6089_: *mut LeanObject,
    mut v_typeRef_6090_: *mut LeanObject,
    mut v___x_6091_: *mut LeanObject,
    mut v___x_6092_: *mut LeanObject,
    mut v___x_6093_: *mut LeanObject,
    mut v___f_6094_: *mut LeanObject,
    mut v___x_6095_: *mut LeanObject,
    mut v___x_6096_: *mut LeanObject,
    mut v_type_6097_: *mut LeanObject,
    mut v_kind_6098_: *mut LeanObject,
    mut v_vis_x3f_6099_: *mut LeanObject,
    mut v_type_x27_6100_: *mut LeanObject,
    mut v___y_6101_: *mut LeanObject,
    mut v___y_6102_: *mut LeanObject,
    mut v___y_6103_: *mut LeanObject,
    mut v___y_6104_: *mut LeanObject,
    mut v___y_6105_: *mut LeanObject,
    mut v___y_6106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6120_: u8 = 0;
    let mut v_cancelTk_x3f_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6122_: u8 = 0;
    let mut v_inheritedTraceOptions_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6133_: u8 = 0;
    let mut v___x_6134_: u8 = 0;
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6184_: u8 = 0;
    let mut v___x_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6189_: u8 = 0;
    let mut v___x_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: u8 = 0;
    let mut v___x_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: u8 = 0;
    let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6447_: u8 = 0;
    let mut v_a_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6451_: u8 = 0;
    let mut v___x_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6455_: u8 = 0;
    let mut v_isSharedCheck_6456_: u8 = 0;
    let mut v_a_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6460_: u8 = 0;
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6464_: u8 = 0;
    let mut v_a_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6468_: u8 = 0;
    let mut v___x_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6472_: u8 = 0;
    let mut v_a_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6476_: u8 = 0;
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6480_: u8 = 0;
    let mut v_a_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6484_: u8 = 0;
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6488_: u8 = 0;
    let mut v_isSharedCheck_6489_: u8 = 0;
    let mut v_unused_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6495_: u8 = 0;
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6499_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6108_ = lean_ctor_get(v___y_6105_, 0);
                v_fileMap_6109_ = lean_ctor_get(v___y_6105_, 1);
                v_options_6110_ = lean_ctor_get(v___y_6105_, 2);
                v_currRecDepth_6111_ = lean_ctor_get(v___y_6105_, 3);
                v_maxRecDepth_6112_ = lean_ctor_get(v___y_6105_, 4);
                v_ref_6113_ = lean_ctor_get(v___y_6105_, 5);
                v_currNamespace_6114_ = lean_ctor_get(v___y_6105_, 6);
                v_openDecls_6115_ = lean_ctor_get(v___y_6105_, 7);
                v_initHeartbeats_6116_ = lean_ctor_get(v___y_6105_, 8);
                v_maxHeartbeats_6117_ = lean_ctor_get(v___y_6105_, 9);
                v_quotContext_6118_ = lean_ctor_get(v___y_6105_, 10);
                v_currMacroScope_6119_ = lean_ctor_get(v___y_6105_, 11);
                v_diag_6120_ = lean_ctor_get_uint8(
                    v___y_6105_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6121_ = lean_ctor_get(v___y_6105_, 12);
                v_suppressElabErrors_6122_ = lean_ctor_get_uint8(
                    v___y_6105_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6123_ = lean_ctor_get(v___y_6105_, 13);
                v_ref_6124_ = l_Lean_replaceRef(v_cmdRef_6089_, v_ref_6113_);
                lean_inc_ref(v_inheritedTraceOptions_6123_);
                lean_inc(v_cancelTk_x3f_6121_);
                lean_inc(v_currMacroScope_6119_);
                lean_inc(v_quotContext_6118_);
                lean_inc(v_maxHeartbeats_6117_);
                lean_inc(v_initHeartbeats_6116_);
                lean_inc(v_openDecls_6115_);
                lean_inc(v_currNamespace_6114_);
                lean_inc(v_ref_6124_);
                lean_inc(v_maxRecDepth_6112_);
                lean_inc(v_currRecDepth_6111_);
                lean_inc_ref(v_options_6110_);
                lean_inc_ref(v_fileMap_6109_);
                lean_inc_ref(v_fileName_6108_);
                v___x_6125_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_6125_, 0, v_fileName_6108_);
                lean_ctor_set(v___x_6125_, 1, v_fileMap_6109_);
                lean_ctor_set(v___x_6125_, 2, v_options_6110_);
                lean_ctor_set(v___x_6125_, 3, v_currRecDepth_6111_);
                lean_ctor_set(v___x_6125_, 4, v_maxRecDepth_6112_);
                lean_ctor_set(v___x_6125_, 5, v_ref_6124_);
                lean_ctor_set(v___x_6125_, 6, v_currNamespace_6114_);
                lean_ctor_set(v___x_6125_, 7, v_openDecls_6115_);
                lean_ctor_set(v___x_6125_, 8, v_initHeartbeats_6116_);
                lean_ctor_set(v___x_6125_, 9, v_maxHeartbeats_6117_);
                lean_ctor_set(v___x_6125_, 10, v_quotContext_6118_);
                lean_ctor_set(v___x_6125_, 11, v_currMacroScope_6119_);
                lean_ctor_set(v___x_6125_, 12, v_cancelTk_x3f_6121_);
                lean_ctor_set(v___x_6125_, 13, v_inheritedTraceOptions_6123_);
                lean_ctor_set_uint8(
                    v___x_6125_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_6120_,
                );
                lean_ctor_set_uint8(
                    v___x_6125_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_6122_,
                );
                lean_inc_ref(v_type_x27_6100_);
                v___x_6126_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType(v_typeRef_6090_, v_type_x27_6100_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_, v___x_6125_, v___y_6106_);
                if lean_obj_tag(v___x_6126_) == 0 {
                    v_a_6127_ = lean_ctor_get(v___x_6126_, 0);
                    lean_inc(v_a_6127_);
                    lean_dec_ref_known(v___x_6126_, 1);
                    v_toConstantVal_6128_ = lean_ctor_get(v_a_6127_, 0);
                    lean_inc_ref(v_toConstantVal_6128_);
                    v_ctors_6129_ = lean_ctor_get(v_a_6127_, 4);
                    lean_inc(v_ctors_6129_);
                    v_name_6130_ = lean_ctor_get(v_toConstantVal_6128_, 0);
                    v_isSharedCheck_6489_ = (!lean_is_exclusive(v_toConstantVal_6128_)) as u8;
                    if v_isSharedCheck_6489_ == 0 {
                        v_unused_6490_ = lean_ctor_get(v_toConstantVal_6128_, 2);
                        lean_dec(v_unused_6490_);
                        v_unused_6491_ = lean_ctor_get(v_toConstantVal_6128_, 1);
                        lean_dec(v_unused_6491_);
                        v___x_6132_ = v_toConstantVal_6128_;
                        v_isShared_6133_ = v_isSharedCheck_6489_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_name_6130_);
                        lean_dec(v_toConstantVal_6128_);
                        v___x_6132_ = lean_box(0);
                        v_isShared_6133_ = v_isSharedCheck_6489_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_6125_, 14);
                    lean_dec(v_ref_6124_);
                    lean_dec_ref(v_type_x27_6100_);
                    lean_dec(v_vis_x3f_6099_);
                    lean_dec(v_kind_6098_);
                    lean_dec_ref(v___x_6096_);
                    lean_dec_ref(v___x_6095_);
                    lean_dec_ref(v___f_6094_);
                    lean_dec(v___x_6093_);
                    lean_dec_ref(v___x_6092_);
                    lean_dec_ref(v___x_6091_);
                    v_a_6492_ = lean_ctor_get(v___x_6126_, 0);
                    v_isSharedCheck_6499_ = (!lean_is_exclusive(v___x_6126_)) as u8;
                    if v_isSharedCheck_6499_ == 0 {
                        v___x_6494_ = v___x_6126_;
                        v_isShared_6495_ = v_isSharedCheck_6499_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_6492_);
                        lean_dec(v___x_6126_);
                        v___x_6494_ = lean_box(0);
                        v_isShared_6495_ = v_isSharedCheck_6499_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6134_ = 0;
                lean_inc(v_name_6130_);
                v___x_6135_ = l_Lean_mkCIdentFrom(v_typeRef_6090_, v_name_6130_, v___x_6134_);
                v___x_6136_ = l_Lean_SourceInfo_fromRef(v_ref_6124_, v___x_6134_);
                lean_dec(v_ref_6124_);
                v___x_6137_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__7;
                v___x_6138_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__8;
                v___x_6139_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__9;
                lean_inc_ref(v___x_6091_);
                v___x_6140_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6138_, v___x_6139_);
                lean_inc_ref_n(v___x_6092_, 2);
                v___x_6141_ = l_String_toRawSubstring_x27(v___x_6092_);
                v___x_6142_ = l_Lean_Name_mkStr1(v___x_6092_);
                lean_inc(v_currMacroScope_6119_);
                lean_inc(v_quotContext_6118_);
                v___x_6143_ =
                    l_Lean_addMacroScope(v_quotContext_6118_, v___x_6142_, v_currMacroScope_6119_);
                v___x_6144_ = lean_box(0);
                lean_inc(v___x_6093_);
                v___x_6145_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6145_, 0, v___x_6093_);
                lean_ctor_set(v___x_6145_, 1, v___x_6144_);
                v___x_6146_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6146_, 0, v___x_6093_);
                lean_inc_ref(v___x_6146_);
                v___x_6147_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6147_, 0, v___x_6146_);
                lean_ctor_set(v___x_6147_, 1, v___x_6144_);
                v___x_6148_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6148_, 0, v___x_6145_);
                lean_ctor_set(v___x_6148_, 1, v___x_6147_);
                lean_inc_ref(v___x_6148_);
                lean_inc(v___x_6143_);
                lean_inc_ref(v___x_6141_);
                lean_inc_n(v___x_6136_, 2);
                v___x_6149_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6149_, 0, v___x_6136_);
                lean_ctor_set(v___x_6149_, 1, v___x_6141_);
                lean_ctor_set(v___x_6149_, 2, v___x_6143_);
                lean_ctor_set(v___x_6149_, 3, v___x_6148_);
                v___x_6150_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__18;
                lean_inc(v___x_6135_);
                v___x_6151_ = l_Lean_Syntax_node1(v___x_6136_, v___x_6150_, v___x_6135_);
                lean_inc(v___x_6140_);
                v___x_6152_ =
                    l_Lean_Syntax_node2(v___x_6136_, v___x_6140_, v___x_6149_, v___x_6151_);
                v___x_6153_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__0;
                v___x_6154_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__1;
                v___x_6155_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(
                    v___x_6153_,
                    v___x_6154_,
                    v___x_6152_,
                    v___y_6101_,
                    v___y_6102_,
                    v___y_6103_,
                    v___y_6104_,
                    v___x_6125_,
                    v___y_6106_,
                );
                if lean_obj_tag(v___x_6155_) == 0 {
                    v_a_6156_ = lean_ctor_get(v___x_6155_, 0);
                    lean_inc_n(v_a_6156_, 2);
                    lean_dec_ref_known(v___x_6155_, 1);
                    v___x_6157_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__2;
                    v___x_6158_ = lean_box(0);
                    v___x_6159_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__2;
                    v___x_6160_ = l_Lean_Name_append(v_a_6156_, v___x_6159_);
                    v___x_6161_ = lean_mk_syntax_ident(v___x_6160_);
                    lean_inc(v___x_6161_);
                    v___x_6162_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg(v_a_6127_, v_type_x27_6100_, v___x_6161_, v_ctors_6129_, v___x_6154_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_, v___x_6125_, v___y_6106_);
                    lean_dec(v_ctors_6129_);
                    lean_dec(v_a_6127_);
                    if lean_obj_tag(v___x_6162_) == 0 {
                        v_a_6163_ = lean_ctor_get(v___x_6162_, 0);
                        lean_inc(v_a_6163_);
                        lean_dec_ref_known(v___x_6162_, 1);
                        lean_inc_ref(v___f_6094_);
                        lean_inc(v___y_6106_);
                        lean_inc_ref(v___x_6125_);
                        lean_inc(v___y_6104_);
                        lean_inc_ref(v___y_6103_);
                        lean_inc(v___y_6102_);
                        lean_inc_ref(v___y_6101_);
                        v___x_6164_ = lean_apply_7(
                            v___f_6094_,
                            v___y_6101_,
                            v___y_6102_,
                            v___y_6103_,
                            v___y_6104_,
                            v___x_6125_,
                            v___y_6106_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_6164_) == 0 {
                            v_a_6165_ = lean_ctor_get(v___x_6164_, 0);
                            lean_inc(v_a_6165_);
                            lean_dec_ref_known(v___x_6164_, 1);
                            lean_inc_ref(v___f_6094_);
                            lean_inc(v___y_6106_);
                            lean_inc_ref(v___x_6125_);
                            lean_inc(v___y_6104_);
                            lean_inc_ref(v___y_6103_);
                            lean_inc(v___y_6102_);
                            lean_inc_ref(v___y_6101_);
                            v___x_6166_ = lean_apply_7(
                                v___f_6094_,
                                v___y_6101_,
                                v___y_6102_,
                                v___y_6103_,
                                v___y_6104_,
                                v___x_6125_,
                                v___y_6106_,
                                lean_box(0),
                            );
                            if lean_obj_tag(v___x_6166_) == 0 {
                                v_a_6167_ = lean_ctor_get(v___x_6166_, 0);
                                lean_inc(v_a_6167_);
                                lean_dec_ref_known(v___x_6166_, 1);
                                v___x_6168_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__4_once), _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__4);
                                v___x_6169_ =
                                    l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__5;
                                lean_inc_n(v_currMacroScope_6119_, 2);
                                lean_inc_n(v_quotContext_6118_, 2);
                                v___x_6170_ = l_Lean_addMacroScope(
                                    v_quotContext_6118_,
                                    v___x_6169_,
                                    v_currMacroScope_6119_,
                                );
                                lean_inc(v___x_6170_);
                                v___x_6171_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_6171_, 0, v_a_6165_);
                                lean_ctor_set(v___x_6171_, 1, v___x_6168_);
                                lean_ctor_set(v___x_6171_, 2, v___x_6170_);
                                lean_ctor_set(v___x_6171_, 3, v___x_6144_);
                                v___x_6172_ =
                                    l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__6;
                                v___x_6173_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__7_once), _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__7);
                                v___x_6174_ =
                                    l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__8;
                                v___x_6175_ = l_Lean_addMacroScope(
                                    v_quotContext_6118_,
                                    v___x_6174_,
                                    v_currMacroScope_6119_,
                                );
                                lean_inc_ref(v___x_6096_);
                                lean_inc_ref(v___x_6095_);
                                lean_inc_ref(v___x_6091_);
                                v___x_6176_ = l_Lean_Name_mkStr4(
                                    v___x_6091_,
                                    v___x_6095_,
                                    v___x_6096_,
                                    v___x_6172_,
                                );
                                v___x_6177_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_6177_, 0, v___x_6176_);
                                lean_ctor_set(v___x_6177_, 1, v___x_6144_);
                                v___x_6178_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_6178_, 0, v___x_6177_);
                                lean_ctor_set(v___x_6178_, 1, v___x_6144_);
                                v___x_6179_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_6179_, 0, v_a_6167_);
                                lean_ctor_set(v___x_6179_, 1, v___x_6173_);
                                lean_ctor_set(v___x_6179_, 2, v___x_6175_);
                                lean_ctor_set(v___x_6179_, 3, v___x_6178_);
                                v___x_6180_ = l_Lean_Elab_ConfigEval_makeStringMatcher(
                                    v___x_6171_,
                                    v_a_6163_,
                                    v___x_6179_,
                                    v___y_6101_,
                                    v___y_6102_,
                                    v___y_6103_,
                                    v___y_6104_,
                                    v___x_6125_,
                                    v___y_6106_,
                                );
                                if lean_obj_tag(v___x_6180_) == 0 {
                                    v_a_6181_ = lean_ctor_get(v___x_6180_, 0);
                                    v_isSharedCheck_6456_ = (!lean_is_exclusive(v___x_6180_)) as u8;
                                    if v_isSharedCheck_6456_ == 0 {
                                        v___x_6183_ = v___x_6180_;
                                        v_isShared_6184_ = v_isSharedCheck_6456_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6181_);
                                        lean_dec(v___x_6180_);
                                        v___x_6183_ = lean_box(0);
                                        v_isShared_6184_ = v_isSharedCheck_6456_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_6170_);
                                    lean_dec(v___x_6161_);
                                    lean_dec(v_a_6156_);
                                    lean_dec_ref_known(v___x_6148_, 2);
                                    lean_dec_ref_known(v___x_6146_, 1);
                                    lean_dec(v___x_6143_);
                                    lean_dec_ref(v___x_6141_);
                                    lean_dec(v___x_6140_);
                                    lean_dec(v___x_6135_);
                                    lean_del_object(v___x_6132_);
                                    lean_dec(v_name_6130_);
                                    lean_dec_ref_known(v___x_6125_, 14);
                                    lean_dec_ref(v_type_x27_6100_);
                                    lean_dec(v_vis_x3f_6099_);
                                    lean_dec(v_kind_6098_);
                                    lean_dec_ref(v___x_6096_);
                                    lean_dec_ref(v___x_6095_);
                                    lean_dec_ref(v___f_6094_);
                                    lean_dec_ref(v___x_6092_);
                                    lean_dec_ref(v___x_6091_);
                                    return v___x_6180_;
                                }
                            } else {
                                lean_dec(v_a_6165_);
                                lean_dec(v_a_6163_);
                                lean_dec(v___x_6161_);
                                lean_dec(v_a_6156_);
                                lean_dec_ref_known(v___x_6148_, 2);
                                lean_dec_ref_known(v___x_6146_, 1);
                                lean_dec(v___x_6143_);
                                lean_dec_ref(v___x_6141_);
                                lean_dec(v___x_6140_);
                                lean_dec(v___x_6135_);
                                lean_del_object(v___x_6132_);
                                lean_dec(v_name_6130_);
                                lean_dec_ref_known(v___x_6125_, 14);
                                lean_dec_ref(v_type_x27_6100_);
                                lean_dec(v_vis_x3f_6099_);
                                lean_dec(v_kind_6098_);
                                lean_dec_ref(v___x_6096_);
                                lean_dec_ref(v___x_6095_);
                                lean_dec_ref(v___f_6094_);
                                lean_dec_ref(v___x_6092_);
                                lean_dec_ref(v___x_6091_);
                                v_a_6457_ = lean_ctor_get(v___x_6166_, 0);
                                v_isSharedCheck_6464_ = (!lean_is_exclusive(v___x_6166_)) as u8;
                                if v_isSharedCheck_6464_ == 0 {
                                    v___x_6459_ = v___x_6166_;
                                    v_isShared_6460_ = v_isSharedCheck_6464_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_6457_);
                                    lean_dec(v___x_6166_);
                                    v___x_6459_ = lean_box(0);
                                    v_isShared_6460_ = v_isSharedCheck_6464_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_6163_);
                            lean_dec(v___x_6161_);
                            lean_dec(v_a_6156_);
                            lean_dec_ref_known(v___x_6148_, 2);
                            lean_dec_ref_known(v___x_6146_, 1);
                            lean_dec(v___x_6143_);
                            lean_dec_ref(v___x_6141_);
                            lean_dec(v___x_6140_);
                            lean_dec(v___x_6135_);
                            lean_del_object(v___x_6132_);
                            lean_dec(v_name_6130_);
                            lean_dec_ref_known(v___x_6125_, 14);
                            lean_dec_ref(v_type_x27_6100_);
                            lean_dec(v_vis_x3f_6099_);
                            lean_dec(v_kind_6098_);
                            lean_dec_ref(v___x_6096_);
                            lean_dec_ref(v___x_6095_);
                            lean_dec_ref(v___f_6094_);
                            lean_dec_ref(v___x_6092_);
                            lean_dec_ref(v___x_6091_);
                            v_a_6465_ = lean_ctor_get(v___x_6164_, 0);
                            v_isSharedCheck_6472_ = (!lean_is_exclusive(v___x_6164_)) as u8;
                            if v_isSharedCheck_6472_ == 0 {
                                v___x_6467_ = v___x_6164_;
                                v_isShared_6468_ = v_isSharedCheck_6472_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_6465_);
                                lean_dec(v___x_6164_);
                                v___x_6467_ = lean_box(0);
                                v_isShared_6468_ = v_isSharedCheck_6472_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_6161_);
                        lean_dec(v_a_6156_);
                        lean_dec_ref_known(v___x_6148_, 2);
                        lean_dec_ref_known(v___x_6146_, 1);
                        lean_dec(v___x_6143_);
                        lean_dec_ref(v___x_6141_);
                        lean_dec(v___x_6140_);
                        lean_dec(v___x_6135_);
                        lean_del_object(v___x_6132_);
                        lean_dec(v_name_6130_);
                        lean_dec_ref_known(v___x_6125_, 14);
                        lean_dec_ref(v_type_x27_6100_);
                        lean_dec(v_vis_x3f_6099_);
                        lean_dec(v_kind_6098_);
                        lean_dec_ref(v___x_6096_);
                        lean_dec_ref(v___x_6095_);
                        lean_dec_ref(v___f_6094_);
                        lean_dec_ref(v___x_6092_);
                        lean_dec_ref(v___x_6091_);
                        v_a_6473_ = lean_ctor_get(v___x_6162_, 0);
                        v_isSharedCheck_6480_ = (!lean_is_exclusive(v___x_6162_)) as u8;
                        if v_isSharedCheck_6480_ == 0 {
                            v___x_6475_ = v___x_6162_;
                            v_isShared_6476_ = v_isSharedCheck_6480_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_6473_);
                            lean_dec(v___x_6162_);
                            v___x_6475_ = lean_box(0);
                            v_isShared_6476_ = v_isSharedCheck_6480_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_6148_, 2);
                    lean_dec_ref_known(v___x_6146_, 1);
                    lean_dec(v___x_6143_);
                    lean_dec_ref(v___x_6141_);
                    lean_dec(v___x_6140_);
                    lean_dec(v___x_6135_);
                    lean_del_object(v___x_6132_);
                    lean_dec(v_name_6130_);
                    lean_dec(v_ctors_6129_);
                    lean_dec(v_a_6127_);
                    lean_dec_ref_known(v___x_6125_, 14);
                    lean_dec_ref(v_type_x27_6100_);
                    lean_dec(v_vis_x3f_6099_);
                    lean_dec(v_kind_6098_);
                    lean_dec_ref(v___x_6096_);
                    lean_dec_ref(v___x_6095_);
                    lean_dec_ref(v___f_6094_);
                    lean_dec_ref(v___x_6092_);
                    lean_dec_ref(v___x_6091_);
                    v_a_6481_ = lean_ctor_get(v___x_6155_, 0);
                    v_isSharedCheck_6488_ = (!lean_is_exclusive(v___x_6155_)) as u8;
                    if v_isSharedCheck_6488_ == 0 {
                        v___x_6483_ = v___x_6155_;
                        v_isShared_6484_ = v_isSharedCheck_6488_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_6481_);
                        lean_dec(v___x_6155_);
                        v___x_6483_ = lean_box(0);
                        v_isShared_6484_ = v_isSharedCheck_6488_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v___y_6106_);
                lean_inc(v___y_6104_);
                lean_inc_ref(v___y_6103_);
                lean_inc(v___y_6102_);
                lean_inc_ref(v___y_6101_);
                v___x_6185_ = lean_apply_7(
                    v___f_6094_,
                    v___y_6101_,
                    v___y_6102_,
                    v___y_6103_,
                    v___y_6104_,
                    v___x_6125_,
                    v___y_6106_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6185_) == 0 {
                    v_a_6186_ = lean_ctor_get(v___x_6185_, 0);
                    v_isSharedCheck_6447_ = (!lean_is_exclusive(v___x_6185_)) as u8;
                    if v_isSharedCheck_6447_ == 0 {
                        v___x_6188_ = v___x_6185_;
                        v_isShared_6189_ = v_isSharedCheck_6447_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6186_);
                        lean_dec(v___x_6185_);
                        v___x_6188_ = lean_box(0);
                        v_isShared_6189_ = v_isSharedCheck_6447_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6183_);
                    lean_dec(v_a_6181_);
                    lean_dec(v___x_6170_);
                    lean_dec(v___x_6161_);
                    lean_dec(v_a_6156_);
                    lean_dec_ref_known(v___x_6148_, 2);
                    lean_dec_ref_known(v___x_6146_, 1);
                    lean_dec(v___x_6143_);
                    lean_dec_ref(v___x_6141_);
                    lean_dec(v___x_6140_);
                    lean_dec(v___x_6135_);
                    lean_del_object(v___x_6132_);
                    lean_dec(v_name_6130_);
                    lean_dec_ref(v_type_x27_6100_);
                    lean_dec(v_vis_x3f_6099_);
                    lean_dec(v_kind_6098_);
                    lean_dec_ref(v___x_6096_);
                    lean_dec_ref(v___x_6095_);
                    lean_dec_ref(v___x_6092_);
                    lean_dec_ref(v___x_6091_);
                    v_a_6448_ = lean_ctor_get(v___x_6185_, 0);
                    v_isSharedCheck_6455_ = (!lean_is_exclusive(v___x_6185_)) as u8;
                    if v_isSharedCheck_6455_ == 0 {
                        v___x_6450_ = v___x_6185_;
                        v_isShared_6451_ = v_isSharedCheck_6455_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_6448_);
                        lean_dec(v___x_6185_);
                        v___x_6450_ = lean_box(0);
                        v_isShared_6451_ = v_isSharedCheck_6455_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6190_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__21;
                v___x_6191_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__9;
                lean_inc_ref_n(v___x_6091_, 2);
                v___x_6192_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6190_, v___x_6191_);
                v___x_6193_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__10;
                v___x_6194_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6190_, v___x_6193_);
                v___x_6195_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26);
                lean_inc(v_a_6186_);
                if v_isShared_6133_ == 0 {
                    lean_ctor_set_tag(v___x_6132_, 1);
                    lean_ctor_set(v___x_6132_, 2, v___x_6195_);
                    lean_ctor_set(v___x_6132_, 1, v___x_6150_);
                    lean_ctor_set(v___x_6132_, 0, v_a_6186_);
                    v___x_6197_ = v___x_6132_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6446_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6446_, 0, v_a_6186_);
                    lean_ctor_set(v_reuseFailAlloc_6446_, 1, v___x_6150_);
                    lean_ctor_set(v_reuseFailAlloc_6446_, 2, v___x_6195_);
                    v___x_6197_ = v_reuseFailAlloc_6446_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if lean_obj_tag(v_vis_x3f_6099_) == 1 {
                    v_val_6443_ = lean_ctor_get(v_vis_x3f_6099_, 0);
                    lean_inc(v_val_6443_);
                    lean_dec_ref_known(v_vis_x3f_6099_, 1);
                    v___x_6444_ = l_Array_mkArray1___redArg(v_val_6443_);
                    v___y_6358_ = v___x_6444_;
                    state = 8;
                    continue;
                } else {
                    lean_dec(v_vis_x3f_6099_);
                    v___x_6445_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__61;
                    v___y_6358_ = v___x_6445_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_6215_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__31;
                lean_inc_ref_n(v___x_6091_, 15);
                v___x_6216_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6138_, v___x_6215_);
                lean_inc_n(v_a_6186_, 30);
                v___x_6217_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6217_, 0, v_a_6186_);
                lean_ctor_set(v___x_6217_, 1, v___x_6215_);
                v___x_6218_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__33;
                v___x_6219_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6138_, v___x_6218_);
                v___x_6220_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6220_, 0, v_a_6186_);
                lean_ctor_set(v___x_6220_, 1, v___x_6168_);
                lean_ctor_set(v___x_6220_, 2, v___x_6170_);
                lean_ctor_set(v___x_6220_, 3, v___x_6144_);
                v___x_6221_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__22), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__22_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__22);
                v___x_6222_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__23;
                lean_inc_n(v_currMacroScope_6119_, 5);
                lean_inc_n(v_quotContext_6118_, 5);
                v___x_6223_ =
                    l_Lean_addMacroScope(v_quotContext_6118_, v___x_6222_, v_currMacroScope_6119_);
                v___x_6224_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6224_, 0, v_a_6186_);
                lean_ctor_set(v___x_6224_, 1, v___x_6221_);
                lean_ctor_set(v___x_6224_, 2, v___x_6223_);
                lean_ctor_set(v___x_6224_, 3, v___x_6144_);
                v___x_6225_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6150_, v___x_6220_, v___x_6224_);
                v___x_6226_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__35;
                v___x_6227_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6227_, 0, v_a_6186_);
                lean_ctor_set(v___x_6227_, 1, v___x_6226_);
                lean_inc_ref_n(v___x_6197_, 18);
                v___x_6228_ = l_Lean_Syntax_node4(
                    v_a_6186_,
                    v___x_6219_,
                    v___x_6225_,
                    v___x_6197_,
                    v___x_6227_,
                    v_a_6181_,
                );
                v___x_6229_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6216_, v___x_6217_, v___x_6228_);
                lean_inc(v___y_6214_);
                v___x_6230_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6150_, v___y_6214_, v___x_6229_);
                lean_inc_n(v___x_6140_, 2);
                v___x_6231_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6140_, v___y_6207_, v___x_6230_);
                v___x_6232_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__11;
                v___x_6233_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__12;
                v___x_6234_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6232_, v___x_6233_);
                v___x_6235_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6234_, v___x_6197_, v___x_6197_);
                lean_inc_n(v___y_6210_, 2);
                v___x_6236_ = l_Lean_Syntax_node4(
                    v_a_6186_,
                    v___y_6203_,
                    v___y_6210_,
                    v___x_6231_,
                    v___x_6235_,
                    v___x_6197_,
                );
                v___x_6237_ = l_Lean_Syntax_node5(
                    v_a_6186_,
                    v___y_6206_,
                    v___y_6202_,
                    v___y_6213_,
                    v___y_6201_,
                    v___x_6236_,
                    v___x_6197_,
                );
                lean_inc(v___x_6192_);
                v___x_6238_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6192_, v___y_6204_, v___x_6237_);
                v___x_6239_ = l_Lean_Syntax_node7(
                    v_a_6186_,
                    v___x_6194_,
                    v___x_6197_,
                    v___x_6197_,
                    v___y_6199_,
                    v___x_6197_,
                    v___x_6197_,
                    v___x_6197_,
                    v___x_6197_,
                );
                v___x_6240_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__13;
                v___x_6241_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6190_, v___x_6240_);
                v___x_6242_ = 1;
                v___x_6243_ = l_Lean_SourceInfo_fromRef(v_cmdRef_6089_, v___x_6242_);
                v___x_6244_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6244_, 0, v___x_6243_);
                lean_ctor_set(v___x_6244_, 1, v___x_6240_);
                v___x_6245_ = lean_expr_eqv(v_type_6097_, v_type_x27_6100_);
                lean_dec_ref(v_type_x27_6100_);
                v___x_6246_ = l_Lean_mkIdentFrom(v_cmdRef_6089_, v_a_6156_, v___x_6245_);
                v___x_6247_ = l_Lean_Syntax_node2(v_a_6186_, v___y_6209_, v___x_6246_, v___x_6197_);
                v___x_6248_ = l_Lean_Syntax_node1(v_a_6186_, v___x_6150_, v___x_6247_);
                v___x_6249_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__14;
                v___x_6250_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6190_, v___x_6249_);
                v___x_6251_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6251_, 0, v_a_6186_);
                lean_ctor_set(v___x_6251_, 1, v___x_6141_);
                lean_ctor_set(v___x_6251_, 2, v___x_6143_);
                lean_ctor_set(v___x_6251_, 3, v___x_6148_);
                v___x_6252_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6140_, v___x_6251_, v___y_6208_);
                v___x_6253_ = l_Lean_Syntax_node2(v_a_6186_, v___y_6205_, v___y_6211_, v___x_6252_);
                v___x_6254_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6250_, v___x_6197_, v___x_6253_);
                v___x_6255_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__15;
                v___x_6256_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6190_, v___x_6255_);
                v___x_6257_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__16;
                v___x_6258_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6258_, 0, v_a_6186_);
                lean_ctor_set(v___x_6258_, 1, v___x_6257_);
                v___x_6259_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__17;
                v___x_6260_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6138_, v___x_6259_);
                v___x_6261_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__18;
                v___x_6262_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6138_, v___x_6261_);
                v___x_6263_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__19;
                v___x_6264_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6138_, v___x_6263_);
                v___x_6265_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__20_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__20,
                );
                v___x_6266_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__21;
                v___x_6267_ =
                    l_Lean_addMacroScope(v_quotContext_6118_, v___x_6266_, v_currMacroScope_6119_);
                lean_inc_ref(v___x_6092_);
                lean_inc_ref_n(v___x_6096_, 2);
                lean_inc_ref_n(v___x_6095_, 3);
                v___x_6268_ = l_Lean_Name_mkStr5(
                    v___x_6091_,
                    v___x_6095_,
                    v___x_6096_,
                    v___x_6092_,
                    v___x_6157_,
                );
                v___x_6269_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6269_, 0, v___x_6268_);
                lean_ctor_set(v___x_6269_, 1, v___x_6144_);
                v___x_6270_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6270_, 0, v___x_6269_);
                lean_ctor_set(v___x_6270_, 1, v___x_6144_);
                v___x_6271_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6271_, 0, v_a_6186_);
                lean_ctor_set(v___x_6271_, 1, v___x_6265_);
                lean_ctor_set(v___x_6271_, 2, v___x_6267_);
                lean_ctor_set(v___x_6271_, 3, v___x_6270_);
                lean_inc(v___x_6264_);
                v___x_6272_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6264_, v___x_6271_, v___x_6197_);
                v___x_6273_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__22;
                v___x_6274_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6138_, v___x_6273_);
                lean_inc(v___x_6274_);
                v___x_6275_ = l_Lean_Syntax_node3(
                    v_a_6186_,
                    v___x_6274_,
                    v___y_6210_,
                    v___x_6197_,
                    v___x_6161_,
                );
                v___x_6276_ = l_Lean_Syntax_node3(
                    v_a_6186_,
                    v___x_6150_,
                    v___x_6197_,
                    v___x_6197_,
                    v___x_6275_,
                );
                lean_inc(v___x_6262_);
                v___x_6277_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6262_, v___x_6272_, v___x_6276_);
                v___x_6278_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__23;
                v___x_6279_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__24
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__24_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__24,
                );
                v___x_6280_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__25;
                v___x_6281_ =
                    l_Lean_addMacroScope(v_quotContext_6118_, v___x_6280_, v_currMacroScope_6119_);
                v___x_6282_ = l_Lean_Name_mkStr5(
                    v___x_6091_,
                    v___x_6095_,
                    v___x_6096_,
                    v___x_6092_,
                    v___x_6278_,
                );
                v___x_6283_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6283_, 0, v___x_6282_);
                lean_ctor_set(v___x_6283_, 1, v___x_6144_);
                v___x_6284_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6284_, 0, v___x_6283_);
                lean_ctor_set(v___x_6284_, 1, v___x_6144_);
                v___x_6285_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6285_, 0, v_a_6186_);
                lean_ctor_set(v___x_6285_, 1, v___x_6279_);
                lean_ctor_set(v___x_6285_, 2, v___x_6281_);
                lean_ctor_set(v___x_6285_, 3, v___x_6284_);
                v___x_6286_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6264_, v___x_6285_, v___x_6197_);
                v___x_6287_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__27_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__27,
                );
                v___x_6288_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__28;
                v___x_6289_ =
                    l_Lean_addMacroScope(v_quotContext_6118_, v___x_6288_, v_currMacroScope_6119_);
                v___x_6290_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__32;
                v___x_6291_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6291_, 0, v_a_6186_);
                lean_ctor_set(v___x_6291_, 1, v___x_6287_);
                lean_ctor_set(v___x_6291_, 2, v___x_6289_);
                lean_ctor_set(v___x_6291_, 3, v___x_6290_);
                v___x_6292_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__8;
                v___x_6293_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6138_, v___x_6292_);
                v___x_6294_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__10;
                v___x_6295_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6138_, v___x_6294_);
                v___x_6296_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__12;
                v___x_6297_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6297_, 0, v_a_6186_);
                lean_ctor_set(v___x_6297_, 1, v___x_6296_);
                v___x_6298_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__14;
                v___x_6299_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__16), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__16_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__16);
                v___x_6300_ =
                    l_Lean_addMacroScope(v_quotContext_6118_, v___x_6158_, v_currMacroScope_6119_);
                v___x_6301_ = l_Lean_Name_mkStr3(v___x_6091_, v___x_6095_, v___x_6096_);
                if v_isShared_6184_ == 0 {
                    lean_ctor_set(v___x_6183_, 0, v___x_6301_);
                    v___x_6303_ = v___x_6183_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6356_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6356_, 0, v___x_6301_);
                    v___x_6303_ = v_reuseFailAlloc_6356_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_inc_ref(v___y_6200_);
                lean_inc_ref_n(v___x_6091_, 4);
                v___x_6304_ = l_Lean_Name_mkStr3(v___x_6091_, v___y_6200_, v___x_6190_);
                v___x_6305_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6305_, 0, v___x_6304_);
                lean_inc_ref(v___x_6095_);
                v___x_6306_ = l_Lean_Name_mkStr3(v___x_6091_, v___x_6095_, v___x_6190_);
                v___x_6307_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6307_, 0, v___x_6306_);
                v___x_6308_ = l_Lean_Name_mkStr3(v___x_6091_, v___x_6095_, v___x_6138_);
                v___x_6309_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6309_, 0, v___x_6308_);
                v___x_6310_ = l_Lean_Name_mkStr2(v___x_6091_, v___y_6200_);
                v___x_6311_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6311_, 0, v___x_6310_);
                v___x_6312_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6312_, 0, v___x_6311_);
                lean_ctor_set(v___x_6312_, 1, v___x_6144_);
                v___x_6313_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6313_, 0, v___x_6309_);
                lean_ctor_set(v___x_6313_, 1, v___x_6312_);
                v___x_6314_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6314_, 0, v___x_6307_);
                lean_ctor_set(v___x_6314_, 1, v___x_6313_);
                v___x_6315_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6315_, 0, v___x_6305_);
                lean_ctor_set(v___x_6315_, 1, v___x_6314_);
                v___x_6316_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6316_, 0, v___x_6146_);
                lean_ctor_set(v___x_6316_, 1, v___x_6315_);
                v___x_6317_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6317_, 0, v___x_6303_);
                lean_ctor_set(v___x_6317_, 1, v___x_6316_);
                lean_inc_n(v_a_6186_, 21);
                v___x_6318_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6318_, 0, v_a_6186_);
                lean_ctor_set(v___x_6318_, 1, v___x_6299_);
                lean_ctor_set(v___x_6318_, 2, v___x_6300_);
                lean_ctor_set(v___x_6318_, 3, v___x_6317_);
                v___x_6319_ = l_Lean_Syntax_node1(v_a_6186_, v___x_6298_, v___x_6318_);
                v___x_6320_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6295_, v___x_6297_, v___x_6319_);
                v___x_6321_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__34
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__34_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__34,
                );
                v___x_6322_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__35;
                lean_inc_ref(v___y_6212_);
                v___x_6323_ = l_Lean_Name_mkStr2(v___y_6212_, v___x_6322_);
                lean_inc(v_currMacroScope_6119_);
                lean_inc(v_quotContext_6118_);
                v___x_6324_ =
                    l_Lean_addMacroScope(v_quotContext_6118_, v___x_6323_, v_currMacroScope_6119_);
                v___x_6325_ = l_Lean_Name_mkStr3(v___x_6091_, v___y_6212_, v___x_6322_);
                lean_inc(v___x_6325_);
                v___x_6326_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6326_, 0, v___x_6325_);
                lean_ctor_set(v___x_6326_, 1, v___x_6144_);
                v___x_6327_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6327_, 0, v___x_6325_);
                v___x_6328_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6328_, 0, v___x_6327_);
                lean_ctor_set(v___x_6328_, 1, v___x_6144_);
                v___x_6329_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6329_, 0, v___x_6326_);
                lean_ctor_set(v___x_6329_, 1, v___x_6328_);
                v___x_6330_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6330_, 0, v_a_6186_);
                lean_ctor_set(v___x_6330_, 1, v___x_6321_);
                lean_ctor_set(v___x_6330_, 2, v___x_6324_);
                lean_ctor_set(v___x_6330_, 3, v___x_6329_);
                v___x_6331_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__37;
                v___x_6332_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__27;
                v___x_6333_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6333_, 0, v_a_6186_);
                lean_ctor_set(v___x_6333_, 1, v___x_6332_);
                v___x_6334_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__28;
                v___x_6335_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6335_, 0, v_a_6186_);
                lean_ctor_set(v___x_6335_, 1, v___x_6334_);
                lean_inc_ref_n(v___x_6197_, 6);
                v___x_6336_ = l_Lean_Syntax_node3(
                    v_a_6186_,
                    v___x_6331_,
                    v___x_6333_,
                    v___x_6197_,
                    v___x_6335_,
                );
                v___x_6337_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6150_, v___y_6214_, v___x_6336_);
                lean_inc(v___x_6140_);
                v___x_6338_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6140_, v___x_6330_, v___x_6337_);
                v___x_6339_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__36;
                v___x_6340_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6340_, 0, v_a_6186_);
                lean_ctor_set(v___x_6340_, 1, v___x_6339_);
                v___x_6341_ = l_Lean_Syntax_node3(
                    v_a_6186_,
                    v___x_6293_,
                    v___x_6320_,
                    v___x_6338_,
                    v___x_6340_,
                );
                v___x_6342_ = l_Lean_Syntax_node1(v_a_6186_, v___x_6150_, v___x_6341_);
                v___x_6343_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6140_, v___x_6291_, v___x_6342_);
                v___x_6344_ = l_Lean_Syntax_node3(
                    v_a_6186_,
                    v___x_6274_,
                    v___y_6210_,
                    v___x_6197_,
                    v___x_6343_,
                );
                v___x_6345_ = l_Lean_Syntax_node3(
                    v_a_6186_,
                    v___x_6150_,
                    v___x_6197_,
                    v___x_6197_,
                    v___x_6344_,
                );
                v___x_6346_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6262_, v___x_6286_, v___x_6345_);
                v___x_6347_ = l_Lean_Syntax_node3(
                    v_a_6186_,
                    v___x_6150_,
                    v___x_6277_,
                    v___x_6197_,
                    v___x_6346_,
                );
                v___x_6348_ = l_Lean_Syntax_node1(v_a_6186_, v___x_6260_, v___x_6347_);
                v___x_6349_ = l_Lean_Syntax_node3(
                    v_a_6186_,
                    v___x_6256_,
                    v___x_6258_,
                    v___x_6348_,
                    v___x_6197_,
                );
                v___x_6350_ = l_Lean_Syntax_node6(
                    v_a_6186_,
                    v___x_6241_,
                    v_kind_6098_,
                    v___x_6244_,
                    v___x_6197_,
                    v___x_6248_,
                    v___x_6254_,
                    v___x_6349_,
                );
                v___x_6351_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6192_, v___x_6239_, v___x_6350_);
                v___x_6352_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6150_, v___x_6238_, v___x_6351_);
                if v_isShared_6189_ == 0 {
                    lean_ctor_set(v___x_6188_, 0, v___x_6352_);
                    v___x_6354_ = v___x_6188_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6355_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6355_, 0, v___x_6352_);
                    v___x_6354_ = v_reuseFailAlloc_6355_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6354_;
            }
            8 => {
                v___x_6359_ = l_Array_append___redArg(v___x_6195_, v___y_6358_);
                lean_dec_ref(v___y_6358_);
                lean_inc_n(v_a_6186_, 18);
                v___x_6360_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6360_, 0, v_a_6186_);
                lean_ctor_set(v___x_6360_, 1, v___x_6150_);
                lean_ctor_set(v___x_6360_, 2, v___x_6359_);
                v___x_6361_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__38;
                lean_inc_ref_n(v___x_6091_, 10);
                v___x_6362_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6190_, v___x_6361_);
                v___x_6363_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6363_, 0, v_a_6186_);
                lean_ctor_set(v___x_6363_, 1, v___x_6361_);
                v___x_6364_ = l_Lean_Syntax_node1(v_a_6186_, v___x_6362_, v___x_6363_);
                v___x_6365_ = l_Lean_Syntax_node1(v_a_6186_, v___x_6150_, v___x_6364_);
                lean_inc_ref(v___x_6360_);
                lean_inc_ref_n(v___x_6197_, 6);
                lean_inc(v___x_6194_);
                v___x_6366_ = l_Lean_Syntax_node7(
                    v_a_6186_,
                    v___x_6194_,
                    v___x_6197_,
                    v___x_6197_,
                    v___x_6360_,
                    v___x_6197_,
                    v___x_6197_,
                    v___x_6197_,
                    v___x_6365_,
                );
                v___x_6367_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__39;
                v___x_6368_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6190_, v___x_6367_);
                v___x_6369_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__40;
                v___x_6370_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6370_, 0, v_a_6186_);
                lean_ctor_set(v___x_6370_, 1, v___x_6369_);
                v___x_6371_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__41;
                v___x_6372_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6190_, v___x_6371_);
                v___x_6373_ = lean_box(2);
                v___x_6374_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__42;
                v___x_6375_ = lean_unsigned_to_nat(2);
                v___x_6376_ = lean_mk_empty_array_with_capacity(v___x_6375_);
                lean_inc(v___x_6161_);
                v___x_6377_ = lean_array_push(v___x_6376_, v___x_6161_);
                v___x_6378_ = lean_array_push(v___x_6377_, v___x_6374_);
                lean_inc(v___x_6372_);
                v___x_6379_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6379_, 0, v___x_6373_);
                lean_ctor_set(v___x_6379_, 1, v___x_6372_);
                lean_ctor_set(v___x_6379_, 2, v___x_6378_);
                v___x_6380_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__43;
                v___x_6381_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6190_, v___x_6380_);
                v___x_6382_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__44;
                v___x_6383_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6138_, v___x_6382_);
                v___x_6384_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__45;
                v___x_6385_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6385_, 0, v_a_6186_);
                lean_ctor_set(v___x_6385_, 1, v___x_6384_);
                v___x_6386_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__46;
                v___x_6387_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6138_, v___x_6386_);
                v___x_6388_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__47;
                v___x_6389_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__48
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__48_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__48,
                );
                v___x_6390_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__49;
                lean_inc_n(v_currMacroScope_6119_, 3);
                lean_inc_n(v_quotContext_6118_, 3);
                v___x_6391_ =
                    l_Lean_addMacroScope(v_quotContext_6118_, v___x_6390_, v_currMacroScope_6119_);
                v___x_6392_ = l_Lean_Name_mkStr2(v___x_6091_, v___x_6388_);
                lean_inc(v___x_6392_);
                v___x_6393_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6393_, 0, v___x_6392_);
                lean_ctor_set(v___x_6393_, 1, v___x_6144_);
                v___x_6394_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6394_, 0, v___x_6392_);
                v___x_6395_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6395_, 0, v___x_6394_);
                lean_ctor_set(v___x_6395_, 1, v___x_6144_);
                v___x_6396_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6396_, 0, v___x_6393_);
                lean_ctor_set(v___x_6396_, 1, v___x_6395_);
                v___x_6397_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6397_, 0, v_a_6186_);
                lean_ctor_set(v___x_6397_, 1, v___x_6389_);
                lean_ctor_set(v___x_6397_, 2, v___x_6391_);
                lean_ctor_set(v___x_6397_, 3, v___x_6396_);
                v___x_6398_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__50;
                v___x_6399_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6399_, 0, v_a_6186_);
                lean_ctor_set(v___x_6399_, 1, v___x_6398_);
                v___x_6400_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__51;
                v___x_6401_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__52
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__52_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__52,
                );
                v___x_6402_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__53;
                v___x_6403_ =
                    l_Lean_addMacroScope(v_quotContext_6118_, v___x_6402_, v_currMacroScope_6119_);
                v___x_6404_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__20;
                v___x_6405_ = l_Lean_Name_mkStr3(v___x_6091_, v___x_6404_, v___x_6400_);
                lean_inc(v___x_6405_);
                v___x_6406_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6406_, 0, v___x_6405_);
                lean_ctor_set(v___x_6406_, 1, v___x_6144_);
                v___x_6407_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6407_, 0, v___x_6405_);
                v___x_6408_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6408_, 0, v___x_6407_);
                lean_ctor_set(v___x_6408_, 1, v___x_6144_);
                v___x_6409_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6409_, 0, v___x_6406_);
                lean_ctor_set(v___x_6409_, 1, v___x_6408_);
                v___x_6410_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6410_, 0, v_a_6186_);
                lean_ctor_set(v___x_6410_, 1, v___x_6401_);
                lean_ctor_set(v___x_6410_, 2, v___x_6403_);
                lean_ctor_set(v___x_6410_, 3, v___x_6409_);
                v___x_6411_ = l_Lean_Syntax_node1(v_a_6186_, v___x_6150_, v___x_6135_);
                lean_inc(v___x_6411_);
                lean_inc(v___x_6140_);
                v___x_6412_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6140_, v___x_6410_, v___x_6411_);
                v___x_6413_ = l_Lean_Syntax_node3(
                    v_a_6186_,
                    v___x_6387_,
                    v___x_6397_,
                    v___x_6399_,
                    v___x_6412_,
                );
                lean_inc_ref(v___x_6385_);
                lean_inc(v___x_6383_);
                v___x_6414_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6383_, v___x_6385_, v___x_6413_);
                v___x_6415_ = l_Lean_Syntax_node1(v_a_6186_, v___x_6150_, v___x_6414_);
                v___x_6416_ = l_Lean_Syntax_node2(v_a_6186_, v___x_6381_, v___x_6197_, v___x_6415_);
                v___x_6417_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__54;
                v___x_6418_ =
                    l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6190_, v___x_6417_);
                v___x_6419_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__55;
                v___x_6420_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6420_, 0, v_a_6186_);
                lean_ctor_set(v___x_6420_, 1, v___x_6419_);
                v___x_6421_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__56;
                v___x_6422_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__57
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__57_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__57,
                );
                v___x_6423_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__58;
                v___x_6424_ =
                    l_Lean_addMacroScope(v_quotContext_6118_, v___x_6423_, v_currMacroScope_6119_);
                lean_inc_ref(v___x_6092_);
                lean_inc_ref(v___x_6096_);
                lean_inc_ref(v___x_6095_);
                v___x_6425_ = l_Lean_Name_mkStr5(
                    v___x_6091_,
                    v___x_6095_,
                    v___x_6096_,
                    v___x_6092_,
                    v___x_6421_,
                );
                v___x_6426_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6426_, 0, v___x_6425_);
                lean_ctor_set(v___x_6426_, 1, v___x_6144_);
                v___x_6427_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6427_, 0, v___x_6426_);
                lean_ctor_set(v___x_6427_, 1, v___x_6144_);
                v___x_6428_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6428_, 0, v_a_6186_);
                lean_ctor_set(v___x_6428_, 1, v___x_6422_);
                lean_ctor_set(v___x_6428_, 2, v___x_6424_);
                lean_ctor_set(v___x_6428_, 3, v___x_6427_);
                lean_inc(v_name_6130_);
                v___x_6429_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_6144_,
                    v_name_6130_,
                );
                if lean_obj_tag(v___x_6429_) == 0 {
                    v___x_6430_ = l_Lean_quoteNameMk(v_name_6130_);
                    v___y_6199_ = v___x_6360_;
                    v___y_6200_ = v___x_6404_;
                    v___y_6201_ = v___x_6416_;
                    v___y_6202_ = v___x_6370_;
                    v___y_6203_ = v___x_6418_;
                    v___y_6204_ = v___x_6366_;
                    v___y_6205_ = v___x_6383_;
                    v___y_6206_ = v___x_6368_;
                    v___y_6207_ = v___x_6428_;
                    v___y_6208_ = v___x_6411_;
                    v___y_6209_ = v___x_6372_;
                    v___y_6210_ = v___x_6420_;
                    v___y_6211_ = v___x_6385_;
                    v___y_6212_ = v___x_6388_;
                    v___y_6213_ = v___x_6379_;
                    v___y_6214_ = v___x_6430_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v_name_6130_);
                    v_val_6431_ = lean_ctor_get(v___x_6429_, 0);
                    lean_inc(v_val_6431_);
                    lean_dec_ref_known(v___x_6429_, 1);
                    v___x_6432_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__59;
                    lean_inc_ref(v___x_6091_);
                    v___x_6433_ =
                        l_Lean_Name_mkStr4(v___x_6091_, v___x_6137_, v___x_6138_, v___x_6432_);
                    v___x_6434_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__2;
                    v___x_6435_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__60;
                    v___x_6436_ = lean_string_intercalate(v___x_6435_, v_val_6431_);
                    v___x_6437_ = lean_string_append(v___x_6434_, v___x_6436_);
                    lean_dec_ref(v___x_6436_);
                    v___x_6438_ = l_Lean_Syntax_mkNameLit(v___x_6437_, v___x_6373_);
                    v___x_6439_ = lean_unsigned_to_nat(1);
                    v___x_6440_ = lean_mk_empty_array_with_capacity(v___x_6439_);
                    v___x_6441_ = lean_array_push(v___x_6440_, v___x_6438_);
                    v___x_6442_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_6442_, 0, v___x_6373_);
                    lean_ctor_set(v___x_6442_, 1, v___x_6433_);
                    lean_ctor_set(v___x_6442_, 2, v___x_6441_);
                    v___y_6199_ = v___x_6360_;
                    v___y_6200_ = v___x_6404_;
                    v___y_6201_ = v___x_6416_;
                    v___y_6202_ = v___x_6370_;
                    v___y_6203_ = v___x_6418_;
                    v___y_6204_ = v___x_6366_;
                    v___y_6205_ = v___x_6383_;
                    v___y_6206_ = v___x_6368_;
                    v___y_6207_ = v___x_6428_;
                    v___y_6208_ = v___x_6411_;
                    v___y_6209_ = v___x_6372_;
                    v___y_6210_ = v___x_6420_;
                    v___y_6211_ = v___x_6385_;
                    v___y_6212_ = v___x_6388_;
                    v___y_6213_ = v___x_6379_;
                    v___y_6214_ = v___x_6442_;
                    state = 5;
                    continue;
                }
            }
            9 => {
                if v_isShared_6451_ == 0 {
                    v___x_6453_ = v___x_6450_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6454_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6454_, 0, v_a_6448_);
                    v___x_6453_ = v_reuseFailAlloc_6454_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6453_;
            }
            11 => {
                if v_isShared_6460_ == 0 {
                    v___x_6462_ = v___x_6459_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6463_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6463_, 0, v_a_6457_);
                    v___x_6462_ = v_reuseFailAlloc_6463_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6462_;
            }
            13 => {
                if v_isShared_6468_ == 0 {
                    v___x_6470_ = v___x_6467_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6471_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6471_, 0, v_a_6465_);
                    v___x_6470_ = v_reuseFailAlloc_6471_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6470_;
            }
            15 => {
                if v_isShared_6476_ == 0 {
                    v___x_6478_ = v___x_6475_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6479_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6479_, 0, v_a_6473_);
                    v___x_6478_ = v_reuseFailAlloc_6479_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6478_;
            }
            17 => {
                if v_isShared_6484_ == 0 {
                    v___x_6486_ = v___x_6483_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6487_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6487_, 0, v_a_6481_);
                    v___x_6486_ = v_reuseFailAlloc_6487_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6486_;
            }
            19 => {
                if v_isShared_6495_ == 0 {
                    v___x_6497_ = v___x_6494_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6498_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6498_, 0, v_a_6492_);
                    v___x_6497_ = v_reuseFailAlloc_6498_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6497_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cmdRef_6500_: *mut LeanObject = *_args.add(0);
    let mut v_typeRef_6501_: *mut LeanObject = *_args.add(1);
    let mut v___x_6502_: *mut LeanObject = *_args.add(2);
    let mut v___x_6503_: *mut LeanObject = *_args.add(3);
    let mut v___x_6504_: *mut LeanObject = *_args.add(4);
    let mut v___f_6505_: *mut LeanObject = *_args.add(5);
    let mut v___x_6506_: *mut LeanObject = *_args.add(6);
    let mut v___x_6507_: *mut LeanObject = *_args.add(7);
    let mut v_type_6508_: *mut LeanObject = *_args.add(8);
    let mut v_kind_6509_: *mut LeanObject = *_args.add(9);
    let mut v_vis_x3f_6510_: *mut LeanObject = *_args.add(10);
    let mut v_type_x27_6511_: *mut LeanObject = *_args.add(11);
    let mut v___y_6512_: *mut LeanObject = *_args.add(12);
    let mut v___y_6513_: *mut LeanObject = *_args.add(13);
    let mut v___y_6514_: *mut LeanObject = *_args.add(14);
    let mut v___y_6515_: *mut LeanObject = *_args.add(15);
    let mut v___y_6516_: *mut LeanObject = *_args.add(16);
    let mut v___y_6517_: *mut LeanObject = *_args.add(17);
    let mut v___y_6518_: *mut LeanObject = *_args.add(18);
    let mut v_res_6519_: *mut LeanObject = core::ptr::null_mut();
    v_res_6519_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1(
        v_cmdRef_6500_,
        v_typeRef_6501_,
        v___x_6502_,
        v___x_6503_,
        v___x_6504_,
        v___f_6505_,
        v___x_6506_,
        v___x_6507_,
        v_type_6508_,
        v_kind_6509_,
        v_vis_x3f_6510_,
        v_type_x27_6511_,
        v___y_6512_,
        v___y_6513_,
        v___y_6514_,
        v___y_6515_,
        v___y_6516_,
        v___y_6517_,
    );
    lean_dec(v___y_6517_);
    lean_dec_ref(v___y_6516_);
    lean_dec(v___y_6515_);
    lean_dec_ref(v___y_6514_);
    lean_dec(v___y_6513_);
    lean_dec_ref(v___y_6512_);
    lean_dec_ref(v_type_6508_);
    lean_dec(v_typeRef_6501_);
    lean_dec(v_cmdRef_6500_);
    return v_res_6519_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ensureEvalExpr(
    mut v_vis_x3f_6521_: *mut LeanObject,
    mut v_kind_6522_: *mut LeanObject,
    mut v_cmdRef_6523_: *mut LeanObject,
    mut v_typeRef_6524_: *mut LeanObject,
    mut v_type_6525_: *mut LeanObject,
    mut v_a_6526_: *mut LeanObject,
    mut v_a_6527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    v___f_6529_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___closed__0;
    v___x_6530_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0;
    v___x_6531_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__3;
    v___x_6532_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__4;
    v___x_6533_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__1;
    v___x_6534_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__0;
    lean_inc_ref(v_type_6525_);
    lean_inc(v_typeRef_6524_);
    v___f_6535_ = lean_alloc_closure(
        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___boxed as *mut core::ffi::c_void,
        19,
        11,
    );
    lean_closure_set(v___f_6535_, 0, v_cmdRef_6523_);
    lean_closure_set(v___f_6535_, 1, v_typeRef_6524_);
    lean_closure_set(v___f_6535_, 2, v___x_6530_);
    lean_closure_set(v___f_6535_, 3, v___x_6533_);
    lean_closure_set(v___f_6535_, 4, v___x_6534_);
    lean_closure_set(v___f_6535_, 5, v___f_6529_);
    lean_closure_set(v___f_6535_, 6, v___x_6531_);
    lean_closure_set(v___f_6535_, 7, v___x_6532_);
    lean_closure_set(v___f_6535_, 8, v_type_6525_);
    lean_closure_set(v___f_6535_, 9, v_kind_6522_);
    lean_closure_set(v___f_6535_, 10, v_vis_x3f_6521_);
    v___x_6536_ = lean_alloc_closure(l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps___boxed as *mut core::ffi::c_void, 9, 1);
    lean_closure_set(v___x_6536_, 0, v_typeRef_6524_);
    v___x_6537_ = l_Lean_Elab_ConfigEval_withClassInstDeps(
        v___x_6534_,
        v_type_6525_,
        v___x_6536_,
        v___f_6535_,
        v_a_6526_,
        v_a_6527_,
    );
    return v___x_6537_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ensureEvalExpr___boxed(
    mut v_vis_x3f_6538_: *mut LeanObject,
    mut v_kind_6539_: *mut LeanObject,
    mut v_cmdRef_6540_: *mut LeanObject,
    mut v_typeRef_6541_: *mut LeanObject,
    mut v_type_6542_: *mut LeanObject,
    mut v_a_6543_: *mut LeanObject,
    mut v_a_6544_: *mut LeanObject,
    mut v_a_6545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6546_: *mut LeanObject = core::ptr::null_mut();
    v_res_6546_ = l_Lean_Elab_ConfigEval_ensureEvalExpr(
        v_vis_x3f_6538_,
        v_kind_6539_,
        v_cmdRef_6540_,
        v_typeRef_6541_,
        v_type_6542_,
        v_a_6543_,
        v_a_6544_,
    );
    lean_dec(v_a_6544_);
    lean_dec_ref(v_a_6543_);
    return v_res_6546_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1(
    mut v_sz_6547_: usize,
    mut v_i_6548_: usize,
    mut v_bs_6549_: *mut LeanObject,
    mut v___y_6550_: *mut LeanObject,
    mut v___y_6551_: *mut LeanObject,
    mut v___y_6552_: *mut LeanObject,
    mut v___y_6553_: *mut LeanObject,
    mut v___y_6554_: *mut LeanObject,
    mut v___y_6555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    v___x_6557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___redArg(v_sz_6547_, v_i_6548_, v_bs_6549_, v___y_6554_, v___y_6555_);
    return v___x_6557_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1___boxed(
    mut v_sz_6558_: *mut LeanObject,
    mut v_i_6559_: *mut LeanObject,
    mut v_bs_6560_: *mut LeanObject,
    mut v___y_6561_: *mut LeanObject,
    mut v___y_6562_: *mut LeanObject,
    mut v___y_6563_: *mut LeanObject,
    mut v___y_6564_: *mut LeanObject,
    mut v___y_6565_: *mut LeanObject,
    mut v___y_6566_: *mut LeanObject,
    mut v___y_6567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6568_: usize = 0;
    let mut v_i_boxed_6569_: usize = 0;
    let mut v_res_6570_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6568_ = lean_unbox_usize(v_sz_6558_);
    lean_dec(v_sz_6558_);
    v_i_boxed_6569_ = lean_unbox_usize(v_i_6559_);
    lean_dec(v_i_6559_);
    v_res_6570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__1(v_sz_boxed_6568_, v_i_boxed_6569_, v_bs_6560_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_, v___y_6565_, v___y_6566_);
    lean_dec(v___y_6566_);
    lean_dec_ref(v___y_6565_);
    lean_dec(v___y_6564_);
    lean_dec_ref(v___y_6563_);
    lean_dec(v___y_6562_);
    lean_dec_ref(v___y_6561_);
    return v_res_6570_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6(
    mut v_a_6571_: *mut LeanObject,
    mut v_type_x27_6572_: *mut LeanObject,
    mut v___x_6573_: *mut LeanObject,
    mut v_as_6574_: *mut LeanObject,
    mut v_as_x27_6575_: *mut LeanObject,
    mut v_b_6576_: *mut LeanObject,
    mut v_a_6577_: *mut LeanObject,
    mut v___y_6578_: *mut LeanObject,
    mut v___y_6579_: *mut LeanObject,
    mut v___y_6580_: *mut LeanObject,
    mut v___y_6581_: *mut LeanObject,
    mut v___y_6582_: *mut LeanObject,
    mut v___y_6583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6585_: *mut LeanObject = core::ptr::null_mut();
    v___x_6585_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg(
            v_a_6571_,
            v_type_x27_6572_,
            v___x_6573_,
            v_as_x27_6575_,
            v_b_6576_,
            v___y_6578_,
            v___y_6579_,
            v___y_6580_,
            v___y_6581_,
            v___y_6582_,
            v___y_6583_,
        );
    return v___x_6585_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___boxed(
    mut v_a_6586_: *mut LeanObject,
    mut v_type_x27_6587_: *mut LeanObject,
    mut v___x_6588_: *mut LeanObject,
    mut v_as_6589_: *mut LeanObject,
    mut v_as_x27_6590_: *mut LeanObject,
    mut v_b_6591_: *mut LeanObject,
    mut v_a_6592_: *mut LeanObject,
    mut v___y_6593_: *mut LeanObject,
    mut v___y_6594_: *mut LeanObject,
    mut v___y_6595_: *mut LeanObject,
    mut v___y_6596_: *mut LeanObject,
    mut v___y_6597_: *mut LeanObject,
    mut v___y_6598_: *mut LeanObject,
    mut v___y_6599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6600_: *mut LeanObject = core::ptr::null_mut();
    v_res_6600_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6(
        v_a_6586_,
        v_type_x27_6587_,
        v___x_6588_,
        v_as_6589_,
        v_as_x27_6590_,
        v_b_6591_,
        v_a_6592_,
        v___y_6593_,
        v___y_6594_,
        v___y_6595_,
        v___y_6596_,
        v___y_6597_,
        v___y_6598_,
    );
    lean_dec(v___y_6598_);
    lean_dec_ref(v___y_6597_);
    lean_dec(v___y_6596_);
    lean_dec_ref(v___y_6595_);
    lean_dec(v___y_6594_);
    lean_dec_ref(v___y_6593_);
    lean_dec(v_as_x27_6590_);
    lean_dec(v_as_6589_);
    lean_dec_ref(v_type_x27_6587_);
    lean_dec_ref(v_a_6586_);
    return v_res_6600_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    v___x_6601_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6601_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    v___x_6602_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__0);
    v___x_6603_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6603_, 0, v___x_6602_);
    return v___x_6603_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut LeanObject = core::ptr::null_mut();
    v___x_6604_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__1);
    v___x_6605_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6605_, 0, v___x_6604_);
    lean_ctor_set(v___x_6605_, 1, v___x_6604_);
    return v___x_6605_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    v___x_6606_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__1);
    v___x_6607_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_6607_, 0, v___x_6606_);
    lean_ctor_set(v___x_6607_, 1, v___x_6606_);
    lean_ctor_set(v___x_6607_, 2, v___x_6606_);
    lean_ctor_set(v___x_6607_, 3, v___x_6606_);
    lean_ctor_set(v___x_6607_, 4, v___x_6606_);
    lean_ctor_set(v___x_6607_, 5, v___x_6606_);
    return v___x_6607_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg(
    mut v_env_6608_: *mut LeanObject,
    mut v___y_6609_: *mut LeanObject,
    mut v___y_6610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6622_: u8 = 0;
    let mut v___x_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6634_: u8 = 0;
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6642_: u8 = 0;
    let mut v_unused_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6645_: u8 = 0;
    let mut v_unused_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6612_ = lean_st_ref_take(v___y_6610_);
                v_nextMacroScope_6613_ = lean_ctor_get(v___x_6612_, 1);
                v_ngen_6614_ = lean_ctor_get(v___x_6612_, 2);
                v_auxDeclNGen_6615_ = lean_ctor_get(v___x_6612_, 3);
                v_traceState_6616_ = lean_ctor_get(v___x_6612_, 4);
                v_messages_6617_ = lean_ctor_get(v___x_6612_, 6);
                v_infoState_6618_ = lean_ctor_get(v___x_6612_, 7);
                v_snapshotTasks_6619_ = lean_ctor_get(v___x_6612_, 8);
                v_isSharedCheck_6645_ = (!lean_is_exclusive(v___x_6612_)) as u8;
                if v_isSharedCheck_6645_ == 0 {
                    v_unused_6646_ = lean_ctor_get(v___x_6612_, 5);
                    lean_dec(v_unused_6646_);
                    v_unused_6647_ = lean_ctor_get(v___x_6612_, 0);
                    lean_dec(v_unused_6647_);
                    v___x_6621_ = v___x_6612_;
                    v_isShared_6622_ = v_isSharedCheck_6645_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6619_);
                    lean_inc(v_infoState_6618_);
                    lean_inc(v_messages_6617_);
                    lean_inc(v_traceState_6616_);
                    lean_inc(v_auxDeclNGen_6615_);
                    lean_inc(v_ngen_6614_);
                    lean_inc(v_nextMacroScope_6613_);
                    lean_dec(v___x_6612_);
                    v___x_6621_ = lean_box(0);
                    v_isShared_6622_ = v_isSharedCheck_6645_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6623_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__2);
                if v_isShared_6622_ == 0 {
                    lean_ctor_set(v___x_6621_, 5, v___x_6623_);
                    lean_ctor_set(v___x_6621_, 0, v_env_6608_);
                    v___x_6625_ = v___x_6621_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6644_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6644_, 0, v_env_6608_);
                    lean_ctor_set(v_reuseFailAlloc_6644_, 1, v_nextMacroScope_6613_);
                    lean_ctor_set(v_reuseFailAlloc_6644_, 2, v_ngen_6614_);
                    lean_ctor_set(v_reuseFailAlloc_6644_, 3, v_auxDeclNGen_6615_);
                    lean_ctor_set(v_reuseFailAlloc_6644_, 4, v_traceState_6616_);
                    lean_ctor_set(v_reuseFailAlloc_6644_, 5, v___x_6623_);
                    lean_ctor_set(v_reuseFailAlloc_6644_, 6, v_messages_6617_);
                    lean_ctor_set(v_reuseFailAlloc_6644_, 7, v_infoState_6618_);
                    lean_ctor_set(v_reuseFailAlloc_6644_, 8, v_snapshotTasks_6619_);
                    v___x_6625_ = v_reuseFailAlloc_6644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6626_ = lean_st_ref_set(v___y_6610_, v___x_6625_);
                v___x_6627_ = lean_st_ref_take(v___y_6609_);
                v_mctx_6628_ = lean_ctor_get(v___x_6627_, 0);
                v_zetaDeltaFVarIds_6629_ = lean_ctor_get(v___x_6627_, 2);
                v_postponed_6630_ = lean_ctor_get(v___x_6627_, 3);
                v_diag_6631_ = lean_ctor_get(v___x_6627_, 4);
                v_isSharedCheck_6642_ = (!lean_is_exclusive(v___x_6627_)) as u8;
                if v_isSharedCheck_6642_ == 0 {
                    v_unused_6643_ = lean_ctor_get(v___x_6627_, 1);
                    lean_dec(v_unused_6643_);
                    v___x_6633_ = v___x_6627_;
                    v_isShared_6634_ = v_isSharedCheck_6642_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_6631_);
                    lean_inc(v_postponed_6630_);
                    lean_inc(v_zetaDeltaFVarIds_6629_);
                    lean_inc(v_mctx_6628_);
                    lean_dec(v___x_6627_);
                    v___x_6633_ = lean_box(0);
                    v_isShared_6634_ = v_isSharedCheck_6642_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6635_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__3);
                if v_isShared_6634_ == 0 {
                    lean_ctor_set(v___x_6633_, 1, v___x_6635_);
                    v___x_6637_ = v___x_6633_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6641_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6641_, 0, v_mctx_6628_);
                    lean_ctor_set(v_reuseFailAlloc_6641_, 1, v___x_6635_);
                    lean_ctor_set(v_reuseFailAlloc_6641_, 2, v_zetaDeltaFVarIds_6629_);
                    lean_ctor_set(v_reuseFailAlloc_6641_, 3, v_postponed_6630_);
                    lean_ctor_set(v_reuseFailAlloc_6641_, 4, v_diag_6631_);
                    v___x_6637_ = v_reuseFailAlloc_6641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6638_ = lean_st_ref_set(v___y_6609_, v___x_6637_);
                v___x_6639_ = lean_box(0);
                v___x_6640_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6640_, 0, v___x_6639_);
                return v___x_6640_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___boxed(
    mut v_env_6648_: *mut LeanObject,
    mut v___y_6649_: *mut LeanObject,
    mut v___y_6650_: *mut LeanObject,
    mut v___y_6651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6652_: *mut LeanObject = core::ptr::null_mut();
    v_res_6652_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg(v_env_6648_, v___y_6649_, v___y_6650_);
    lean_dec(v___y_6650_);
    lean_dec(v___y_6649_);
    return v_res_6652_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0___redArg(
    mut v_env_6653_: *mut LeanObject,
    mut v_x_6654_: *mut LeanObject,
    mut v___y_6655_: *mut LeanObject,
    mut v___y_6656_: *mut LeanObject,
    mut v___y_6657_: *mut LeanObject,
    mut v___y_6658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6667_: u8 = 0;
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6671_: u8 = 0;
    let mut v_unused_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6679_: u8 = 0;
    let mut v___x_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6683_: u8 = 0;
    let mut v_unused_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6660_ = lean_st_ref_get(v___y_6658_);
                v_env_6661_ = lean_ctor_get(v___x_6660_, 0);
                lean_inc_ref(v_env_6661_);
                lean_dec(v___x_6660_);
                v___x_6673_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg(v_env_6653_, v___y_6656_, v___y_6658_);
                lean_dec_ref(v___x_6673_);
                lean_inc(v___y_6658_);
                lean_inc_ref(v___y_6657_);
                lean_inc(v___y_6656_);
                lean_inc_ref(v___y_6655_);
                v___x_6674_ = lean_apply_5(
                    v_x_6654_,
                    v___y_6655_,
                    v___y_6656_,
                    v___y_6657_,
                    v___y_6658_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6674_) == 0 {
                    v_a_6675_ = lean_ctor_get(v___x_6674_, 0);
                    lean_inc(v_a_6675_);
                    lean_dec_ref_known(v___x_6674_, 1);
                    v___x_6676_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg(v_env_6661_, v___y_6656_, v___y_6658_);
                    v_isSharedCheck_6683_ = (!lean_is_exclusive(v___x_6676_)) as u8;
                    if v_isSharedCheck_6683_ == 0 {
                        v_unused_6684_ = lean_ctor_get(v___x_6676_, 0);
                        lean_dec(v_unused_6684_);
                        v___x_6678_ = v___x_6676_;
                        v_isShared_6679_ = v_isSharedCheck_6683_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_6676_);
                        v___x_6678_ = lean_box(0);
                        v_isShared_6679_ = v_isSharedCheck_6683_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_6685_ = lean_ctor_get(v___x_6674_, 0);
                    lean_inc(v_a_6685_);
                    lean_dec_ref_known(v___x_6674_, 1);
                    v_a_6663_ = v_a_6685_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6664_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg(v_env_6661_, v___y_6656_, v___y_6658_);
                v_isSharedCheck_6671_ = (!lean_is_exclusive(v___x_6664_)) as u8;
                if v_isSharedCheck_6671_ == 0 {
                    v_unused_6672_ = lean_ctor_get(v___x_6664_, 0);
                    lean_dec(v_unused_6672_);
                    v___x_6666_ = v___x_6664_;
                    v_isShared_6667_ = v_isSharedCheck_6671_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_6664_);
                    v___x_6666_ = lean_box(0);
                    v_isShared_6667_ = v_isSharedCheck_6671_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6667_ == 0 {
                    lean_ctor_set_tag(v___x_6666_, 1);
                    lean_ctor_set(v___x_6666_, 0, v_a_6663_);
                    v___x_6669_ = v___x_6666_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6670_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 0, v_a_6663_);
                    v___x_6669_ = v_reuseFailAlloc_6670_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6669_;
            }
            4 => {
                if v_isShared_6679_ == 0 {
                    lean_ctor_set(v___x_6678_, 0, v_a_6675_);
                    v___x_6681_ = v___x_6678_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6682_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6682_, 0, v_a_6675_);
                    v___x_6681_ = v_reuseFailAlloc_6682_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0___redArg___boxed(
    mut v_env_6686_: *mut LeanObject,
    mut v_x_6687_: *mut LeanObject,
    mut v___y_6688_: *mut LeanObject,
    mut v___y_6689_: *mut LeanObject,
    mut v___y_6690_: *mut LeanObject,
    mut v___y_6691_: *mut LeanObject,
    mut v___y_6692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6693_: *mut LeanObject = core::ptr::null_mut();
    v_res_6693_ = l_Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0___redArg(
        v_env_6686_,
        v_x_6687_,
        v___y_6688_,
        v___y_6689_,
        v___y_6690_,
        v___y_6691_,
    );
    lean_dec(v___y_6691_);
    lean_dec_ref(v___y_6690_);
    lean_dec(v___y_6689_);
    lean_dec_ref(v___y_6688_);
    return v_res_6693_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5_spec__8___redArg(
    mut v_a_6694_: *mut LeanObject,
    mut v_x_6695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: u8 = 0;
    let mut v___x_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6695_) == 0 {
                    v___x_6696_ = lean_box(0);
                    return v___x_6696_;
                } else {
                    v_key_6697_ = lean_ctor_get(v_x_6695_, 0);
                    v_value_6698_ = lean_ctor_get(v_x_6695_, 1);
                    v_tail_6699_ = lean_ctor_get(v_x_6695_, 2);
                    v___x_6700_ = lean_name_eq(v_key_6697_, v_a_6694_);
                    if v___x_6700_ == 0 {
                        v_x_6695_ = v_tail_6699_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_6698_);
                        v___x_6702_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_6702_, 0, v_value_6698_);
                        return v___x_6702_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5_spec__8___redArg___boxed(
    mut v_a_6703_: *mut LeanObject,
    mut v_x_6704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6705_: *mut LeanObject = core::ptr::null_mut();
    v_res_6705_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5_spec__8___redArg(v_a_6703_, v_x_6704_);
    lean_dec(v_x_6704_);
    lean_dec(v_a_6703_);
    return v_res_6705_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: u64 = 0;
    v___x_6706_ = lean_unsigned_to_nat(1723);
    v___x_6707_ = lean_uint64_of_nat(v___x_6706_);
    return v___x_6707_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5___redArg(
    mut v_m_6708_: *mut LeanObject,
    mut v_a_6709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6713_: u64 = 0;
    let mut v___x_6714_: u64 = 0;
    let mut v___x_6715_: u64 = 0;
    let mut v_fold_6716_: u64 = 0;
    let mut v___x_6717_: u64 = 0;
    let mut v___x_6718_: u64 = 0;
    let mut v___x_6719_: u64 = 0;
    let mut v___x_6720_: usize = 0;
    let mut v___x_6721_: usize = 0;
    let mut v___x_6722_: usize = 0;
    let mut v___x_6723_: usize = 0;
    let mut v___x_6724_: usize = 0;
    let mut v___x_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: u64 = 0;
    let mut v_hash_6728_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_6710_ = lean_ctor_get(v_m_6708_, 1);
                v___x_6711_ = lean_array_get_size(v_buckets_6710_);
                if lean_obj_tag(v_a_6709_) == 0 {
                    v___x_6727_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5___redArg___closed__0);
                    v___y_6713_ = v___x_6727_;
                    state = 1;
                    continue;
                } else {
                    v_hash_6728_ = lean_ctor_get_uint64(
                        v_a_6709_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_6713_ = v_hash_6728_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6714_ = 32u64;
                v___x_6715_ = lean_uint64_shift_right(v___y_6713_, v___x_6714_);
                v_fold_6716_ = lean_uint64_xor(v___y_6713_, v___x_6715_);
                v___x_6717_ = 16u64;
                v___x_6718_ = lean_uint64_shift_right(v_fold_6716_, v___x_6717_);
                v___x_6719_ = lean_uint64_xor(v_fold_6716_, v___x_6718_);
                v___x_6720_ = lean_uint64_to_usize(v___x_6719_);
                v___x_6721_ = lean_usize_of_nat(v___x_6711_);
                v___x_6722_ = 1usize;
                v___x_6723_ = lean_usize_sub(v___x_6721_, v___x_6722_);
                v___x_6724_ = lean_usize_land(v___x_6720_, v___x_6723_);
                v___x_6725_ = lean_array_uget_borrowed(v_buckets_6710_, v___x_6724_);
                v___x_6726_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5_spec__8___redArg(v_a_6709_, v___x_6725_);
                return v___x_6726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5___redArg___boxed(
    mut v_m_6729_: *mut LeanObject,
    mut v_a_6730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6731_: *mut LeanObject = core::ptr::null_mut();
    v_res_6731_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5___redArg(v_m_6729_, v_a_6730_);
    lean_dec(v_a_6730_);
    lean_dec_ref(v_m_6729_);
    return v_res_6731_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5___closed__0()
-> f64 {
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: f64 = 0.0;
    v___x_6732_ = lean_unsigned_to_nat(0);
    v___x_6733_ = lean_float_of_nat(v___x_6732_);
    return v___x_6733_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5(
    mut v_cls_6736_: *mut LeanObject,
    mut v_msg_6737_: *mut LeanObject,
    mut v___y_6738_: *mut LeanObject,
    mut v___y_6739_: *mut LeanObject,
    mut v___y_6740_: *mut LeanObject,
    mut v___y_6741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6748_: u8 = 0;
    let mut v___x_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6761_: u8 = 0;
    let mut v_tid_6762_: u64 = 0;
    let mut v_traces_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6766_: u8 = 0;
    let mut v___x_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: f64 = 0.0;
    let mut v___x_6769_: u8 = 0;
    let mut v___x_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6787_: u8 = 0;
    let mut v_isSharedCheck_6788_: u8 = 0;
    let mut v_isSharedCheck_6789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6743_ = lean_ctor_get(v___y_6740_, 5);
                v___x_6744_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__2(v_msg_6737_, v___y_6738_, v___y_6739_, v___y_6740_, v___y_6741_);
                v_a_6745_ = lean_ctor_get(v___x_6744_, 0);
                v_isSharedCheck_6789_ = (!lean_is_exclusive(v___x_6744_)) as u8;
                if v_isSharedCheck_6789_ == 0 {
                    v___x_6747_ = v___x_6744_;
                    v_isShared_6748_ = v_isSharedCheck_6789_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_6745_);
                    lean_dec(v___x_6744_);
                    v___x_6747_ = lean_box(0);
                    v_isShared_6748_ = v_isSharedCheck_6789_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6749_ = lean_st_ref_take(v___y_6741_);
                v_traceState_6750_ = lean_ctor_get(v___x_6749_, 4);
                v_env_6751_ = lean_ctor_get(v___x_6749_, 0);
                v_nextMacroScope_6752_ = lean_ctor_get(v___x_6749_, 1);
                v_ngen_6753_ = lean_ctor_get(v___x_6749_, 2);
                v_auxDeclNGen_6754_ = lean_ctor_get(v___x_6749_, 3);
                v_cache_6755_ = lean_ctor_get(v___x_6749_, 5);
                v_messages_6756_ = lean_ctor_get(v___x_6749_, 6);
                v_infoState_6757_ = lean_ctor_get(v___x_6749_, 7);
                v_snapshotTasks_6758_ = lean_ctor_get(v___x_6749_, 8);
                v_isSharedCheck_6788_ = (!lean_is_exclusive(v___x_6749_)) as u8;
                if v_isSharedCheck_6788_ == 0 {
                    v___x_6760_ = v___x_6749_;
                    v_isShared_6761_ = v_isSharedCheck_6788_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6758_);
                    lean_inc(v_infoState_6757_);
                    lean_inc(v_messages_6756_);
                    lean_inc(v_cache_6755_);
                    lean_inc(v_traceState_6750_);
                    lean_inc(v_auxDeclNGen_6754_);
                    lean_inc(v_ngen_6753_);
                    lean_inc(v_nextMacroScope_6752_);
                    lean_inc(v_env_6751_);
                    lean_dec(v___x_6749_);
                    v___x_6760_ = lean_box(0);
                    v_isShared_6761_ = v_isSharedCheck_6788_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_6762_ = lean_ctor_get_uint64(
                    v_traceState_6750_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_6763_ = lean_ctor_get(v_traceState_6750_, 0);
                v_isSharedCheck_6787_ = (!lean_is_exclusive(v_traceState_6750_)) as u8;
                if v_isSharedCheck_6787_ == 0 {
                    v___x_6765_ = v_traceState_6750_;
                    v_isShared_6766_ = v_isSharedCheck_6787_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_6763_);
                    lean_dec(v_traceState_6750_);
                    v___x_6765_ = lean_box(0);
                    v_isShared_6766_ = v_isSharedCheck_6787_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6767_ = lean_box(0);
                v___x_6768_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5___closed__0);
                v___x_6769_ = 0;
                v___x_6770_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__15;
                v___x_6771_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_6771_, 0, v_cls_6736_);
                lean_ctor_set(v___x_6771_, 1, v___x_6767_);
                lean_ctor_set(v___x_6771_, 2, v___x_6770_);
                lean_ctor_set_float(
                    v___x_6771_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_6768_,
                );
                lean_ctor_set_float(
                    v___x_6771_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_6768_,
                );
                lean_ctor_set_uint8(
                    v___x_6771_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_6769_,
                );
                v___x_6772_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5___closed__1;
                v___x_6773_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_6773_, 0, v___x_6771_);
                lean_ctor_set(v___x_6773_, 1, v_a_6745_);
                lean_ctor_set(v___x_6773_, 2, v___x_6772_);
                lean_inc(v_ref_6743_);
                v___x_6774_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6774_, 0, v_ref_6743_);
                lean_ctor_set(v___x_6774_, 1, v___x_6773_);
                v___x_6775_ = l_Lean_PersistentArray_push___redArg(v_traces_6763_, v___x_6774_);
                if v_isShared_6766_ == 0 {
                    lean_ctor_set(v___x_6765_, 0, v___x_6775_);
                    v___x_6777_ = v___x_6765_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6786_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6786_, 0, v___x_6775_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_6786_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_6762_,
                    );
                    v___x_6777_ = v_reuseFailAlloc_6786_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6761_ == 0 {
                    lean_ctor_set(v___x_6760_, 4, v___x_6777_);
                    v___x_6779_ = v___x_6760_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6785_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6785_, 0, v_env_6751_);
                    lean_ctor_set(v_reuseFailAlloc_6785_, 1, v_nextMacroScope_6752_);
                    lean_ctor_set(v_reuseFailAlloc_6785_, 2, v_ngen_6753_);
                    lean_ctor_set(v_reuseFailAlloc_6785_, 3, v_auxDeclNGen_6754_);
                    lean_ctor_set(v_reuseFailAlloc_6785_, 4, v___x_6777_);
                    lean_ctor_set(v_reuseFailAlloc_6785_, 5, v_cache_6755_);
                    lean_ctor_set(v_reuseFailAlloc_6785_, 6, v_messages_6756_);
                    lean_ctor_set(v_reuseFailAlloc_6785_, 7, v_infoState_6757_);
                    lean_ctor_set(v_reuseFailAlloc_6785_, 8, v_snapshotTasks_6758_);
                    v___x_6779_ = v_reuseFailAlloc_6785_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6780_ = lean_st_ref_set(v___y_6741_, v___x_6779_);
                v___x_6781_ = lean_box(0);
                if v_isShared_6748_ == 0 {
                    lean_ctor_set(v___x_6747_, 0, v___x_6781_);
                    v___x_6783_ = v___x_6747_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6784_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6784_, 0, v___x_6781_);
                    v___x_6783_ = v_reuseFailAlloc_6784_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5___boxed(
    mut v_cls_6790_: *mut LeanObject,
    mut v_msg_6791_: *mut LeanObject,
    mut v___y_6792_: *mut LeanObject,
    mut v___y_6793_: *mut LeanObject,
    mut v___y_6794_: *mut LeanObject,
    mut v___y_6795_: *mut LeanObject,
    mut v___y_6796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6797_: *mut LeanObject = core::ptr::null_mut();
    v_res_6797_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5(v_cls_6790_, v_msg_6791_, v___y_6792_, v___y_6793_, v___y_6794_, v___y_6795_);
    lean_dec(v___y_6795_);
    lean_dec_ref(v___y_6794_);
    lean_dec(v___y_6793_);
    lean_dec_ref(v___y_6792_);
    return v_res_6797_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5_spec__8___redArg(
    mut v_keys_6798_: *mut LeanObject,
    mut v_i_6799_: *mut LeanObject,
    mut v_k_6800_: *mut LeanObject,
) -> u8 {
    let mut v___x_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: u8 = 0;
    let mut v_k_x27_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: u8 = 0;
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6801_ = lean_array_get_size(v_keys_6798_);
                v___x_6802_ = lean_nat_dec_lt(v_i_6799_, v___x_6801_);
                if v___x_6802_ == 0 {
                    lean_dec(v_i_6799_);
                    return v___x_6802_;
                } else {
                    v_k_x27_6803_ = lean_array_fget_borrowed(v_keys_6798_, v_i_6799_);
                    v___x_6804_ = l_Lean_instBEqExtraModUse_beq(v_k_6800_, v_k_x27_6803_);
                    if v___x_6804_ == 0 {
                        v___x_6805_ = lean_unsigned_to_nat(1);
                        v___x_6806_ = lean_nat_add(v_i_6799_, v___x_6805_);
                        lean_dec(v_i_6799_);
                        v_i_6799_ = v___x_6806_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_6799_);
                        return v___x_6804_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5_spec__8___redArg___boxed(
    mut v_keys_6808_: *mut LeanObject,
    mut v_i_6809_: *mut LeanObject,
    mut v_k_6810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6811_: u8 = 0;
    let mut v_r_6812_: *mut LeanObject = core::ptr::null_mut();
    v_res_6811_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5_spec__8___redArg(v_keys_6808_, v_i_6809_, v_k_6810_);
    lean_dec_ref(v_k_6810_);
    lean_dec_ref(v_keys_6808_);
    v_r_6812_ = lean_box((v_res_6811_) as usize);
    return v_r_6812_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___closed__0()
-> usize {
    let mut v___x_6813_: usize = 0;
    let mut v___x_6814_: usize = 0;
    let mut v___x_6815_: usize = 0;
    v___x_6813_ = 5usize;
    v___x_6814_ = 1usize;
    v___x_6815_ = lean_usize_shift_left(v___x_6814_, v___x_6813_);
    return v___x_6815_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___closed__1()
-> usize {
    let mut v___x_6816_: usize = 0;
    let mut v___x_6817_: usize = 0;
    let mut v___x_6818_: usize = 0;
    v___x_6816_ = 1usize;
    v___x_6817_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
    v___x_6818_ = lean_usize_sub(v___x_6817_, v___x_6816_);
    return v___x_6818_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_x_6819_: *mut LeanObject,
    mut v_x_6820_: usize,
    mut v_x_6821_: *mut LeanObject,
) -> u8 {
    let mut v_es_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: usize = 0;
    let mut v___x_6825_: usize = 0;
    let mut v___x_6826_: usize = 0;
    let mut v_j_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: u8 = 0;
    let mut v_node_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: usize = 0;
    let mut v___x_6834_: u8 = 0;
    let mut v_ks_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6819_) == 0 {
                    v_es_6822_ = lean_ctor_get(v_x_6819_, 0);
                    v___x_6823_ = lean_box(2);
                    v___x_6824_ = 5usize;
                    v___x_6825_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
                    v___x_6826_ = lean_usize_land(v_x_6820_, v___x_6825_);
                    v_j_6827_ = lean_usize_to_nat(v___x_6826_);
                    v___x_6828_ = lean_array_get_borrowed(v___x_6823_, v_es_6822_, v_j_6827_);
                    lean_dec(v_j_6827_);
                    match lean_obj_tag(v___x_6828_) {
                        0 => {
                            v_key_6829_ = lean_ctor_get(v___x_6828_, 0);
                            v___x_6830_ = l_Lean_instBEqExtraModUse_beq(v_x_6821_, v_key_6829_);
                            return v___x_6830_;
                        }
                        1 => {
                            v_node_6831_ = lean_ctor_get(v___x_6828_, 0);
                            v___x_6832_ = lean_usize_shift_right(v_x_6820_, v___x_6824_);
                            v_x_6819_ = v_node_6831_;
                            v_x_6820_ = v___x_6832_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_6834_ = 0;
                            return v___x_6834_;
                        }
                    }
                } else {
                    v_ks_6835_ = lean_ctor_get(v_x_6819_, 0);
                    v___x_6836_ = lean_unsigned_to_nat(0);
                    v___x_6837_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5_spec__8___redArg(v_ks_6835_, v___x_6836_, v_x_6821_);
                    return v___x_6837_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_x_6838_: *mut LeanObject,
    mut v_x_6839_: *mut LeanObject,
    mut v_x_6840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7923__boxed_6841_: usize = 0;
    let mut v_res_6842_: u8 = 0;
    let mut v_r_6843_: *mut LeanObject = core::ptr::null_mut();
    v_x_7923__boxed_6841_ = lean_unbox_usize(v_x_6839_);
    lean_dec(v_x_6839_);
    v_res_6842_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg(v_x_6838_, v_x_7923__boxed_6841_, v_x_6840_);
    lean_dec_ref(v_x_6840_);
    lean_dec_ref(v_x_6838_);
    v_r_6843_ = lean_box((v_res_6842_) as usize);
    return v_r_6843_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4___redArg(
    mut v_x_6844_: *mut LeanObject,
    mut v_x_6845_: *mut LeanObject,
) -> u8 {
    let mut v___x_6846_: u64 = 0;
    let mut v___x_6847_: usize = 0;
    let mut v___x_6848_: u8 = 0;
    v___x_6846_ = l_Lean_instHashableExtraModUse_hash(v_x_6845_);
    v___x_6847_ = lean_uint64_to_usize(v___x_6846_);
    v___x_6848_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg(v_x_6844_, v___x_6847_, v_x_6845_);
    return v___x_6848_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_x_6849_: *mut LeanObject,
    mut v_x_6850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6851_: u8 = 0;
    let mut v_r_6852_: *mut LeanObject = core::ptr::null_mut();
    v_res_6851_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4___redArg(v_x_6849_, v_x_6850_);
    lean_dec_ref(v_x_6850_);
    lean_dec_ref(v_x_6849_);
    v_r_6852_ = lean_box((v_res_6851_) as usize);
    return v_r_6852_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__2()
-> *mut LeanObject {
    let mut v___x_6855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut LeanObject = core::ptr::null_mut();
    v___x_6855_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__1;
    v___x_6856_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__0;
    v___x_6857_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_6856_, v___x_6855_);
    return v___x_6857_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__6()
-> *mut LeanObject {
    let mut v___x_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut LeanObject = core::ptr::null_mut();
    v___x_6862_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__5;
    v___x_6863_ = l_Lean_stringToMessageData(v___x_6862_);
    return v___x_6863_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__8()
-> *mut LeanObject {
    let mut v___x_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut LeanObject = core::ptr::null_mut();
    v___x_6865_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__7;
    v___x_6866_ = l_Lean_stringToMessageData(v___x_6865_);
    return v___x_6866_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__9()
-> *mut LeanObject {
    let mut v___x_6867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut LeanObject = core::ptr::null_mut();
    v___x_6867_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__15;
    v___x_6868_ = l_Lean_stringToMessageData(v___x_6867_);
    return v___x_6868_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__12()
-> *mut LeanObject {
    let mut v_cls_6872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut LeanObject = core::ptr::null_mut();
    v_cls_6872_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__4;
    v___x_6873_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__11;
    v___x_6874_ = l_Lean_Name_append(v___x_6873_, v_cls_6872_);
    return v___x_6874_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__14()
-> *mut LeanObject {
    let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
    v___x_6876_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__13;
    v___x_6877_ = l_Lean_stringToMessageData(v___x_6876_);
    return v___x_6877_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__16()
-> *mut LeanObject {
    let mut v___x_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
    v___x_6879_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__15;
    v___x_6880_ = l_Lean_stringToMessageData(v___x_6879_);
    return v___x_6880_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3(
    mut v_mod_6885_: *mut LeanObject,
    mut v_isMeta_6886_: u8,
    mut v_hint_6887_: *mut LeanObject,
    mut v___y_6888_: *mut LeanObject,
    mut v___y_6889_: *mut LeanObject,
    mut v___y_6890_: *mut LeanObject,
    mut v___y_6891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_6895_: u8 = 0;
    let mut v___x_6896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_6899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6918_: u8 = 0;
    let mut v_asyncMode_6919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6932_: u8 = 0;
    let mut v___x_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6940_: u8 = 0;
    let mut v_unused_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6943_: u8 = 0;
    let mut v_unused_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6946_: u8 = 0;
    let mut v_options_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6948_: u8 = 0;
    let mut v_inheritedTraceOptions_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: u8 = 0;
    let mut v___x_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: u8 = 0;
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6893_ = lean_st_ref_get(v___y_6891_);
                v_env_6894_ = lean_ctor_get(v___x_6893_, 0);
                lean_inc_ref(v_env_6894_);
                lean_dec(v___x_6893_);
                v_isExporting_6895_ = lean_ctor_get_uint8(
                    v_env_6894_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_6894_);
                v___x_6896_ = lean_st_ref_get(v___y_6891_);
                v_env_6897_ = lean_ctor_get(v___x_6896_, 0);
                lean_inc_ref(v_env_6897_);
                lean_dec(v___x_6896_);
                v___x_6898_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__2);
                lean_inc(v_mod_6885_);
                v_entry_6899_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v_entry_6899_, 0, v_mod_6885_);
                lean_ctor_set_uint8(
                    v_entry_6899_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_isExporting_6895_,
                );
                lean_ctor_set_uint8(
                    v_entry_6899_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isMeta_6886_,
                );
                v___x_6900_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_6901_ = lean_box(1);
                v___x_6902_ = lean_box(0);
                v___x_6945_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_6898_,
                    v___x_6900_,
                    v_env_6897_,
                    v___x_6901_,
                    v___x_6902_,
                );
                v___x_6946_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4___redArg(v___x_6945_, v_entry_6899_);
                lean_dec(v___x_6945_);
                if v___x_6946_ == 0 {
                    v_options_6947_ = lean_ctor_get(v___y_6890_, 2);
                    v_hasTrace_6948_ = lean_ctor_get_uint8(
                        v_options_6947_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6948_ == 0 {
                        lean_dec(v_hint_6887_);
                        lean_dec(v_mod_6885_);
                        v___y_6904_ = v___y_6889_;
                        v___y_6905_ = v___y_6891_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_6949_ = lean_ctor_get(v___y_6890_, 13);
                        v_cls_6950_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__4;
                        v___x_6970_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__12);
                        v___x_6971_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_6949_,
                            v_options_6947_,
                            v___x_6970_,
                        );
                        if v___x_6971_ == 0 {
                            lean_dec(v_hint_6887_);
                            lean_dec(v_mod_6885_);
                            v___y_6904_ = v___y_6889_;
                            v___y_6905_ = v___y_6891_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6972_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__14);
                            if v_isExporting_6895_ == 0 {
                                v___x_6981_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__19;
                                v___y_6974_ = v___x_6981_;
                                state = 8;
                                continue;
                            } else {
                                v___x_6982_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__20;
                                v___y_6974_ = v___x_6982_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v_entry_6899_, 1);
                    lean_dec(v_hint_6887_);
                    lean_dec(v_mod_6885_);
                    v___x_6983_ = lean_box(0);
                    v___x_6984_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6984_, 0, v___x_6983_);
                    return v___x_6984_;
                }
            }
            1 => {
                v___x_6906_ = lean_st_ref_take(v___y_6905_);
                v_toEnvExtension_6907_ = lean_ctor_get(v___x_6900_, 0);
                v_env_6908_ = lean_ctor_get(v___x_6906_, 0);
                v_nextMacroScope_6909_ = lean_ctor_get(v___x_6906_, 1);
                v_ngen_6910_ = lean_ctor_get(v___x_6906_, 2);
                v_auxDeclNGen_6911_ = lean_ctor_get(v___x_6906_, 3);
                v_traceState_6912_ = lean_ctor_get(v___x_6906_, 4);
                v_messages_6913_ = lean_ctor_get(v___x_6906_, 6);
                v_infoState_6914_ = lean_ctor_get(v___x_6906_, 7);
                v_snapshotTasks_6915_ = lean_ctor_get(v___x_6906_, 8);
                v_isSharedCheck_6943_ = (!lean_is_exclusive(v___x_6906_)) as u8;
                if v_isSharedCheck_6943_ == 0 {
                    v_unused_6944_ = lean_ctor_get(v___x_6906_, 5);
                    lean_dec(v_unused_6944_);
                    v___x_6917_ = v___x_6906_;
                    v_isShared_6918_ = v_isSharedCheck_6943_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6915_);
                    lean_inc(v_infoState_6914_);
                    lean_inc(v_messages_6913_);
                    lean_inc(v_traceState_6912_);
                    lean_inc(v_auxDeclNGen_6911_);
                    lean_inc(v_ngen_6910_);
                    lean_inc(v_nextMacroScope_6909_);
                    lean_inc(v_env_6908_);
                    lean_dec(v___x_6906_);
                    v___x_6917_ = lean_box(0);
                    v_isShared_6918_ = v_isSharedCheck_6943_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_6919_ = lean_ctor_get(v_toEnvExtension_6907_, 2);
                v___x_6920_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_6900_,
                    v_env_6908_,
                    v_entry_6899_,
                    v_asyncMode_6919_,
                    v___x_6902_,
                );
                v___x_6921_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__2);
                if v_isShared_6918_ == 0 {
                    lean_ctor_set(v___x_6917_, 5, v___x_6921_);
                    lean_ctor_set(v___x_6917_, 0, v___x_6920_);
                    v___x_6923_ = v___x_6917_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6942_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6942_, 0, v___x_6920_);
                    lean_ctor_set(v_reuseFailAlloc_6942_, 1, v_nextMacroScope_6909_);
                    lean_ctor_set(v_reuseFailAlloc_6942_, 2, v_ngen_6910_);
                    lean_ctor_set(v_reuseFailAlloc_6942_, 3, v_auxDeclNGen_6911_);
                    lean_ctor_set(v_reuseFailAlloc_6942_, 4, v_traceState_6912_);
                    lean_ctor_set(v_reuseFailAlloc_6942_, 5, v___x_6921_);
                    lean_ctor_set(v_reuseFailAlloc_6942_, 6, v_messages_6913_);
                    lean_ctor_set(v_reuseFailAlloc_6942_, 7, v_infoState_6914_);
                    lean_ctor_set(v_reuseFailAlloc_6942_, 8, v_snapshotTasks_6915_);
                    v___x_6923_ = v_reuseFailAlloc_6942_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6924_ = lean_st_ref_set(v___y_6905_, v___x_6923_);
                v___x_6925_ = lean_st_ref_take(v___y_6904_);
                v_mctx_6926_ = lean_ctor_get(v___x_6925_, 0);
                v_zetaDeltaFVarIds_6927_ = lean_ctor_get(v___x_6925_, 2);
                v_postponed_6928_ = lean_ctor_get(v___x_6925_, 3);
                v_diag_6929_ = lean_ctor_get(v___x_6925_, 4);
                v_isSharedCheck_6940_ = (!lean_is_exclusive(v___x_6925_)) as u8;
                if v_isSharedCheck_6940_ == 0 {
                    v_unused_6941_ = lean_ctor_get(v___x_6925_, 1);
                    lean_dec(v_unused_6941_);
                    v___x_6931_ = v___x_6925_;
                    v_isShared_6932_ = v_isSharedCheck_6940_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_diag_6929_);
                    lean_inc(v_postponed_6928_);
                    lean_inc(v_zetaDeltaFVarIds_6927_);
                    lean_inc(v_mctx_6926_);
                    lean_dec(v___x_6925_);
                    v___x_6931_ = lean_box(0);
                    v_isShared_6932_ = v_isSharedCheck_6940_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6933_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg___closed__3);
                if v_isShared_6932_ == 0 {
                    lean_ctor_set(v___x_6931_, 1, v___x_6933_);
                    v___x_6935_ = v___x_6931_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6939_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6939_, 0, v_mctx_6926_);
                    lean_ctor_set(v_reuseFailAlloc_6939_, 1, v___x_6933_);
                    lean_ctor_set(v_reuseFailAlloc_6939_, 2, v_zetaDeltaFVarIds_6927_);
                    lean_ctor_set(v_reuseFailAlloc_6939_, 3, v_postponed_6928_);
                    lean_ctor_set(v_reuseFailAlloc_6939_, 4, v_diag_6929_);
                    v___x_6935_ = v_reuseFailAlloc_6939_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6936_ = lean_st_ref_set(v___y_6904_, v___x_6935_);
                v___x_6937_ = lean_box(0);
                v___x_6938_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6938_, 0, v___x_6937_);
                return v___x_6938_;
            }
            6 => {
                v___x_6954_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6954_, 0, v___y_6952_);
                lean_ctor_set(v___x_6954_, 1, v___y_6953_);
                v___x_6955_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__5(v_cls_6950_, v___x_6954_, v___y_6888_, v___y_6889_, v___y_6890_, v___y_6891_);
                if lean_obj_tag(v___x_6955_) == 0 {
                    lean_dec_ref_known(v___x_6955_, 1);
                    v___y_6904_ = v___y_6889_;
                    v___y_6905_ = v___y_6891_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_entry_6899_, 1);
                    return v___x_6955_;
                }
            }
            7 => {
                lean_inc_ref(v___y_6958_);
                v___x_6959_ = l_Lean_stringToMessageData(v___y_6958_);
                v___x_6960_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6960_, 0, v___y_6957_);
                lean_ctor_set(v___x_6960_, 1, v___x_6959_);
                v___x_6961_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__6);
                v___x_6962_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6962_, 0, v___x_6960_);
                lean_ctor_set(v___x_6962_, 1, v___x_6961_);
                v___x_6963_ = l_Lean_MessageData_ofName(v_mod_6885_);
                v___x_6964_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6964_, 0, v___x_6962_);
                lean_ctor_set(v___x_6964_, 1, v___x_6963_);
                v___x_6965_ = l_Lean_Name_isAnonymous(v_hint_6887_);
                if v___x_6965_ == 0 {
                    v___x_6966_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__8);
                    v___x_6967_ = l_Lean_MessageData_ofName(v_hint_6887_);
                    v___x_6968_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6968_, 0, v___x_6966_);
                    lean_ctor_set(v___x_6968_, 1, v___x_6967_);
                    v___y_6952_ = v___x_6964_;
                    v___y_6953_ = v___x_6968_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v_hint_6887_);
                    v___x_6969_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__9);
                    v___y_6952_ = v___x_6964_;
                    v___y_6953_ = v___x_6969_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                lean_inc_ref(v___y_6974_);
                v___x_6975_ = l_Lean_stringToMessageData(v___y_6974_);
                v___x_6976_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6976_, 0, v___x_6972_);
                lean_ctor_set(v___x_6976_, 1, v___x_6975_);
                v___x_6977_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__16);
                v___x_6978_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6978_, 0, v___x_6976_);
                lean_ctor_set(v___x_6978_, 1, v___x_6977_);
                if v_isMeta_6886_ == 0 {
                    v___x_6979_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__17;
                    v___y_6957_ = v___x_6978_;
                    v___y_6958_ = v___x_6979_;
                    state = 7;
                    continue;
                } else {
                    v___x_6980_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__18;
                    v___y_6957_ = v___x_6978_;
                    v___y_6958_ = v___x_6980_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___boxed(
    mut v_mod_6985_: *mut LeanObject,
    mut v_isMeta_6986_: *mut LeanObject,
    mut v_hint_6987_: *mut LeanObject,
    mut v___y_6988_: *mut LeanObject,
    mut v___y_6989_: *mut LeanObject,
    mut v___y_6990_: *mut LeanObject,
    mut v___y_6991_: *mut LeanObject,
    mut v___y_6992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_6993_: u8 = 0;
    let mut v_res_6994_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_6993_ = (lean_unbox(v_isMeta_6986_) as u8);
    v_res_6994_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3(v_mod_6985_, v_isMeta_boxed_6993_, v_hint_6987_, v___y_6988_, v___y_6989_, v___y_6990_, v___y_6991_);
    lean_dec(v___y_6991_);
    lean_dec_ref(v___y_6990_);
    lean_dec(v___y_6989_);
    lean_dec_ref(v___y_6988_);
    return v_res_6994_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__4(
    mut v___x_6995_: *mut LeanObject,
    mut v_declName_6996_: *mut LeanObject,
    mut v_as_6997_: *mut LeanObject,
    mut v_sz_6998_: usize,
    mut v_i_6999_: usize,
    mut v_b_7000_: *mut LeanObject,
    mut v___y_7001_: *mut LeanObject,
    mut v___y_7002_: *mut LeanObject,
    mut v___y_7003_: *mut LeanObject,
    mut v___y_7004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7006_: u8 = 0;
    let mut v___x_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: u8 = 0;
    let mut v___x_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: usize = 0;
    let mut v___x_7019_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7006_ = lean_usize_dec_lt(v_i_6999_, v_sz_6998_);
                if v___x_7006_ == 0 {
                    lean_dec(v_declName_6996_);
                    v___x_7007_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7007_, 0, v_b_7000_);
                    return v___x_7007_;
                } else {
                    v___x_7008_ = l_Lean_Environment_header(v___x_6995_);
                    v_modules_7009_ = lean_ctor_get(v___x_7008_, 3);
                    lean_inc_ref(v_modules_7009_);
                    lean_dec_ref(v___x_7008_);
                    v___x_7010_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_7011_ = lean_array_uget_borrowed(v_as_6997_, v_i_6999_);
                    v___x_7012_ = lean_array_get(v___x_7010_, v_modules_7009_, v_a_7011_);
                    lean_dec_ref(v_modules_7009_);
                    v_toImport_7013_ = lean_ctor_get(v___x_7012_, 0);
                    lean_inc_ref(v_toImport_7013_);
                    lean_dec(v___x_7012_);
                    v_module_7014_ = lean_ctor_get(v_toImport_7013_, 0);
                    lean_inc(v_module_7014_);
                    lean_dec_ref(v_toImport_7013_);
                    v___x_7015_ = 0;
                    lean_inc(v_declName_6996_);
                    v___x_7016_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3(v_module_7014_, v___x_7015_, v_declName_6996_, v___y_7001_, v___y_7002_, v___y_7003_, v___y_7004_);
                    if lean_obj_tag(v___x_7016_) == 0 {
                        lean_dec_ref_known(v___x_7016_, 1);
                        v___x_7017_ = lean_box(0);
                        v___x_7018_ = 1usize;
                        v___x_7019_ = lean_usize_add(v_i_6999_, v___x_7018_);
                        v_i_6999_ = v___x_7019_;
                        v_b_7000_ = v___x_7017_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declName_6996_);
                        return v___x_7016_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__4___boxed(
    mut v___x_7021_: *mut LeanObject,
    mut v_declName_7022_: *mut LeanObject,
    mut v_as_7023_: *mut LeanObject,
    mut v_sz_7024_: *mut LeanObject,
    mut v_i_7025_: *mut LeanObject,
    mut v_b_7026_: *mut LeanObject,
    mut v___y_7027_: *mut LeanObject,
    mut v___y_7028_: *mut LeanObject,
    mut v___y_7029_: *mut LeanObject,
    mut v___y_7030_: *mut LeanObject,
    mut v___y_7031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7032_: usize = 0;
    let mut v_i_boxed_7033_: usize = 0;
    let mut v_res_7034_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7032_ = lean_unbox_usize(v_sz_7024_);
    lean_dec(v_sz_7024_);
    v_i_boxed_7033_ = lean_unbox_usize(v_i_7025_);
    lean_dec(v_i_7025_);
    v_res_7034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__4(v___x_7021_, v_declName_7022_, v_as_7023_, v_sz_boxed_7032_, v_i_boxed_7033_, v_b_7026_, v___y_7027_, v___y_7028_, v___y_7029_, v___y_7030_);
    lean_dec(v___y_7030_);
    lean_dec_ref(v___y_7029_);
    lean_dec(v___y_7028_);
    lean_dec_ref(v___y_7027_);
    lean_dec_ref(v_as_7023_);
    lean_dec_ref(v___x_7021_);
    return v_res_7034_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__2()
-> *mut LeanObject {
    let mut v___x_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut LeanObject = core::ptr::null_mut();
    v___x_7037_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__1;
    v___x_7038_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__0;
    v___x_7039_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_7038_, v___x_7037_);
    return v___x_7039_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2(
    mut v_declName_7042_: *mut LeanObject,
    mut v_isMeta_7043_: u8,
    mut v___y_7044_: *mut LeanObject,
    mut v___y_7045_: *mut LeanObject,
    mut v___y_7046_: *mut LeanObject,
    mut v___y_7047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7057_: usize = 0;
    let mut v___x_7058_: usize = 0;
    let mut v___x_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7062_: u8 = 0;
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7066_: u8 = 0;
    let mut v_unused_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: u8 = 0;
    let mut v___x_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7079_: u8 = 0;
    let mut v_toImport_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: u8 = 0;
    let mut v___x_7091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7049_ = lean_st_ref_get(v___y_7047_);
                v_env_7053_ = lean_ctor_get(v___x_7049_, 0);
                lean_inc_ref(v_env_7053_);
                lean_dec(v___x_7049_);
                v___x_7068_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_7053_, v_declName_7042_);
                if lean_obj_tag(v___x_7068_) == 0 {
                    lean_dec_ref(v_env_7053_);
                    lean_dec(v_declName_7042_);
                    state = 1;
                    continue;
                } else {
                    v_val_7069_ = lean_ctor_get(v___x_7068_, 0);
                    lean_inc(v_val_7069_);
                    lean_dec_ref_known(v___x_7068_, 1);
                    v___x_7070_ = l_Lean_Environment_header(v_env_7053_);
                    v_modules_7071_ = lean_ctor_get(v___x_7070_, 3);
                    lean_inc_ref(v_modules_7071_);
                    lean_dec_ref(v___x_7070_);
                    v___x_7072_ = lean_array_get_size(v_modules_7071_);
                    v___x_7073_ = lean_nat_dec_lt(v_val_7069_, v___x_7072_);
                    if v___x_7073_ == 0 {
                        lean_dec_ref(v_modules_7071_);
                        lean_dec(v_val_7069_);
                        lean_dec_ref(v_env_7053_);
                        lean_dec(v_declName_7042_);
                        state = 1;
                        continue;
                    } else {
                        v___x_7074_ = lean_st_ref_get(v___y_7047_);
                        v_env_7075_ = lean_ctor_get(v___x_7074_, 0);
                        lean_inc_ref(v_env_7075_);
                        lean_dec(v___x_7074_);
                        v___x_7076_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__2);
                        v___x_7077_ = lean_array_fget(v_modules_7071_, v_val_7069_);
                        lean_dec(v_val_7069_);
                        lean_dec_ref(v_modules_7071_);
                        if v_isMeta_7043_ == 0 {
                            lean_dec_ref(v_env_7075_);
                            v___y_7079_ = v_isMeta_7043_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_declName_7042_);
                            v___x_7090_ = l_Lean_isMarkedMeta(v_env_7075_, v_declName_7042_);
                            if v___x_7090_ == 0 {
                                v___y_7079_ = v_isMeta_7043_;
                                state = 5;
                                continue;
                            } else {
                                v___x_7091_ = 0;
                                v___y_7079_ = v___x_7091_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_7051_ = lean_box(0);
                v___x_7052_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7052_, 0, v___x_7051_);
                return v___x_7052_;
            }
            2 => {
                v___x_7056_ = lean_box(0);
                v_sz_7057_ = lean_array_size(v___y_7055_);
                v___x_7058_ = 0usize;
                v___x_7059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__4(v_env_7053_, v_declName_7042_, v___y_7055_, v_sz_7057_, v___x_7058_, v___x_7056_, v___y_7044_, v___y_7045_, v___y_7046_, v___y_7047_);
                lean_dec_ref(v___y_7055_);
                lean_dec_ref(v_env_7053_);
                if lean_obj_tag(v___x_7059_) == 0 {
                    v_isSharedCheck_7066_ = (!lean_is_exclusive(v___x_7059_)) as u8;
                    if v_isSharedCheck_7066_ == 0 {
                        v_unused_7067_ = lean_ctor_get(v___x_7059_, 0);
                        lean_dec(v_unused_7067_);
                        v___x_7061_ = v___x_7059_;
                        v_isShared_7062_ = v_isSharedCheck_7066_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_7059_);
                        v___x_7061_ = lean_box(0);
                        v_isShared_7062_ = v_isSharedCheck_7066_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_7059_;
                }
            }
            3 => {
                if v_isShared_7062_ == 0 {
                    lean_ctor_set(v___x_7061_, 0, v___x_7056_);
                    v___x_7064_ = v___x_7061_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7065_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7065_, 0, v___x_7056_);
                    v___x_7064_ = v_reuseFailAlloc_7065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7064_;
            }
            5 => {
                v_toImport_7080_ = lean_ctor_get(v___x_7077_, 0);
                lean_inc_ref(v_toImport_7080_);
                lean_dec(v___x_7077_);
                v_module_7081_ = lean_ctor_get(v_toImport_7080_, 0);
                lean_inc(v_module_7081_);
                lean_dec_ref(v_toImport_7080_);
                lean_inc(v_declName_7042_);
                v___x_7082_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3(v_module_7081_, v___y_7079_, v_declName_7042_, v___y_7044_, v___y_7045_, v___y_7046_, v___y_7047_);
                if lean_obj_tag(v___x_7082_) == 0 {
                    lean_dec_ref_known(v___x_7082_, 1);
                    v___x_7083_ = l_Lean_indirectModUseExt;
                    v___x_7084_ = lean_box(1);
                    v___x_7085_ = lean_box(0);
                    lean_inc_ref(v_env_7053_);
                    v___x_7086_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_7076_,
                        v___x_7083_,
                        v_env_7053_,
                        v___x_7084_,
                        v___x_7085_,
                    );
                    v___x_7087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5___redArg(v___x_7086_, v_declName_7042_);
                    lean_dec(v___x_7086_);
                    if lean_obj_tag(v___x_7087_) == 0 {
                        v___x_7088_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___closed__3;
                        v___y_7055_ = v___x_7088_;
                        state = 2;
                        continue;
                    } else {
                        v_val_7089_ = lean_ctor_get(v___x_7087_, 0);
                        lean_inc(v_val_7089_);
                        lean_dec_ref_known(v___x_7087_, 1);
                        v___y_7055_ = v_val_7089_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_7053_);
                    lean_dec(v_declName_7042_);
                    return v___x_7082_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2___boxed(
    mut v_declName_7092_: *mut LeanObject,
    mut v_isMeta_7093_: *mut LeanObject,
    mut v___y_7094_: *mut LeanObject,
    mut v___y_7095_: *mut LeanObject,
    mut v___y_7096_: *mut LeanObject,
    mut v___y_7097_: *mut LeanObject,
    mut v___y_7098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_7099_: u8 = 0;
    let mut v_res_7100_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_7099_ = (lean_unbox(v_isMeta_7093_) as u8);
    v_res_7100_ =
        l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2(
            v_declName_7092_,
            v_isMeta_boxed_7099_,
            v___y_7094_,
            v___y_7095_,
            v___y_7096_,
            v___y_7097_,
        );
    lean_dec(v___y_7097_);
    lean_dec_ref(v___y_7096_);
    lean_dec(v___y_7095_);
    lean_dec_ref(v___y_7094_);
    return v_res_7100_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__1___redArg(
    mut v_msg_7101_: *mut LeanObject,
    mut v___y_7102_: *mut LeanObject,
    mut v___y_7103_: *mut LeanObject,
    mut v___y_7104_: *mut LeanObject,
    mut v___y_7105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_7107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7112_: u8 = 0;
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7117_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7107_ = lean_ctor_get(v___y_7104_, 5);
                v___x_7108_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__1_spec__2(v_msg_7101_, v___y_7102_, v___y_7103_, v___y_7104_, v___y_7105_);
                v_a_7109_ = lean_ctor_get(v___x_7108_, 0);
                v_isSharedCheck_7117_ = (!lean_is_exclusive(v___x_7108_)) as u8;
                if v_isSharedCheck_7117_ == 0 {
                    v___x_7111_ = v___x_7108_;
                    v_isShared_7112_ = v_isSharedCheck_7117_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_7109_);
                    lean_dec(v___x_7108_);
                    v___x_7111_ = lean_box(0);
                    v_isShared_7112_ = v_isSharedCheck_7117_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_7107_);
                v___x_7113_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7113_, 0, v_ref_7107_);
                lean_ctor_set(v___x_7113_, 1, v_a_7109_);
                if v_isShared_7112_ == 0 {
                    lean_ctor_set_tag(v___x_7111_, 1);
                    lean_ctor_set(v___x_7111_, 0, v___x_7113_);
                    v___x_7115_ = v___x_7111_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7116_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7116_, 0, v___x_7113_);
                    v___x_7115_ = v_reuseFailAlloc_7116_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__1___redArg___boxed(
    mut v_msg_7118_: *mut LeanObject,
    mut v___y_7119_: *mut LeanObject,
    mut v___y_7120_: *mut LeanObject,
    mut v___y_7121_: *mut LeanObject,
    mut v___y_7122_: *mut LeanObject,
    mut v___y_7123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7124_: *mut LeanObject = core::ptr::null_mut();
    v_res_7124_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__1___redArg(
        v_msg_7118_,
        v___y_7119_,
        v___y_7120_,
        v___y_7121_,
        v___y_7122_,
    );
    lean_dec(v___y_7122_);
    lean_dec_ref(v___y_7121_);
    lean_dec(v___y_7120_);
    lean_dec_ref(v___y_7119_);
    return v_res_7124_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut LeanObject = core::ptr::null_mut();
    v___x_7126_ = l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__0;
    v___x_7127_ = l_Lean_stringToMessageData(v___x_7126_);
    return v___x_7127_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut LeanObject = core::ptr::null_mut();
    v___x_7129_ = l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__2;
    v___x_7130_ = l_Lean_stringToMessageData(v___x_7129_);
    return v___x_7130_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__5() -> *mut LeanObject {
    let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut LeanObject = core::ptr::null_mut();
    v___x_7132_ = l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__4;
    v___x_7133_ = l_Lean_stringToMessageData(v___x_7132_);
    return v___x_7133_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_7135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: *mut LeanObject = core::ptr::null_mut();
    v___x_7135_ = l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__6;
    v___x_7136_ = l_Lean_stringToMessageData(v___x_7135_);
    return v___x_7136_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__9() -> *mut LeanObject {
    let mut v___x_7138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut LeanObject = core::ptr::null_mut();
    v___x_7138_ = l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__8;
    v___x_7139_ = l_Lean_stringToMessageData(v___x_7138_);
    return v___x_7139_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__11() -> *mut LeanObject {
    let mut v___x_7141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut LeanObject = core::ptr::null_mut();
    v___x_7141_ = l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__10;
    v___x_7142_ = l_Lean_stringToMessageData(v___x_7141_);
    return v___x_7142_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__13() -> *mut LeanObject {
    let mut v___x_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7145_: *mut LeanObject = core::ptr::null_mut();
    v___x_7144_ = l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__12;
    v___x_7145_ = l_Lean_stringToMessageData(v___x_7144_);
    return v___x_7145_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalMetaEval___redArg(
    mut v_typeName_7146_: *mut LeanObject,
    mut v_moduleName_x3f_7147_: *mut LeanObject,
    mut v_e_7148_: *mut LeanObject,
    mut v_a_7149_: *mut LeanObject,
    mut v_a_7150_: *mut LeanObject,
    mut v_a_7151_: *mut LeanObject,
    mut v_a_7152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7161_: u8 = 0;
    let mut v___x_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7171_: u8 = 0;
    let mut v___y_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: u8 = 0;
    let mut v___x_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: u8 = 0;
    let mut v___x_7186_: u8 = 0;
    let mut v___y_7188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7192_: u8 = 0;
    let mut v___x_7193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: u8 = 0;
    let mut v___x_7201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7214_: u8 = 0;
    let mut v___x_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7218_: u8 = 0;
    let mut v_a_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7222_: u8 = 0;
    let mut v___x_7224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7226_: u8 = 0;
    let mut v_a_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7230_: u8 = 0;
    let mut v___x_7232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7234_: u8 = 0;
    let mut v_a_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7238_: u8 = 0;
    let mut v___x_7240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7242_: u8 = 0;
    let mut v_a_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7246_: u8 = 0;
    let mut v___x_7248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7250_: u8 = 0;
    let mut v___x_7251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7266_: u8 = 0;
    let mut v___x_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7270_: u8 = 0;
    let mut v_env_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7272_: u8 = 0;
    let mut v___x_7273_: u8 = 0;
    let mut v_val_7274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7251_ = lean_st_ref_get(v_a_7152_);
                v_env_7271_ = lean_ctor_get(v___x_7251_, 0);
                lean_inc_ref(v_env_7271_);
                lean_dec(v___x_7251_);
                v___x_7272_ = 1;
                lean_inc(v_typeName_7146_);
                v___x_7273_ =
                    l_Lean_Environment_contains(v_env_7271_, v_typeName_7146_, v___x_7272_);
                if v___x_7273_ == 0 {
                    if lean_obj_tag(v_moduleName_x3f_7147_) == 1 {
                        v_val_7274_ = lean_ctor_get(v_moduleName_x3f_7147_, 0);
                        lean_inc(v_val_7274_);
                        lean_dec_ref_known(v_moduleName_x3f_7147_, 1);
                        v___x_7275_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__11_once
                            ),
                            _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__11,
                        );
                        v___x_7276_ = l_Lean_MessageData_ofName(v_val_7274_);
                        v___x_7277_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7277_, 0, v___x_7275_);
                        lean_ctor_set(v___x_7277_, 1, v___x_7276_);
                        v___x_7278_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__13_once
                            ),
                            _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__13,
                        );
                        v___x_7279_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7279_, 0, v___x_7277_);
                        lean_ctor_set(v___x_7279_, 1, v___x_7278_);
                        v___y_7253_ = v___x_7279_;
                        state = 14;
                        continue;
                    } else {
                        lean_dec(v_moduleName_x3f_7147_);
                        v___x_7280_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3___closed__9);
                        v___y_7253_ = v___x_7280_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_dec(v_moduleName_x3f_7147_);
                    v___y_7188_ = v_a_7149_;
                    v___y_7189_ = v_a_7150_;
                    v___y_7190_ = v_a_7151_;
                    v___y_7191_ = v_a_7152_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_7161_ == 0 {
                    lean_dec_ref(v___y_7155_);
                    v___x_7162_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__1_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__1,
                    );
                    v___x_7163_ = l_Lean_indentExpr(v_e_7148_);
                    v___x_7164_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7164_, 0, v___x_7162_);
                    lean_ctor_set(v___x_7164_, 1, v___x_7163_);
                    v___x_7165_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__3_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__3,
                    );
                    v___x_7166_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7166_, 0, v___x_7164_);
                    lean_ctor_set(v___x_7166_, 1, v___x_7165_);
                    v___x_7167_ = l_Lean_Exception_toMessageData(v___y_7158_);
                    v___x_7168_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7168_, 0, v___x_7166_);
                    lean_ctor_set(v___x_7168_, 1, v___x_7167_);
                    v___x_7169_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__1___redArg(v___x_7168_, v___y_7157_, v___y_7159_, v___y_7156_, v___y_7160_);
                    return v___x_7169_;
                } else {
                    lean_dec_ref(v___y_7158_);
                    lean_dec_ref(v_e_7148_);
                    return v___y_7155_;
                }
            }
            2 => {
                v___x_7176_ = lean_st_ref_get(v___y_7175_);
                v_env_7177_ = lean_ctor_get(v___x_7176_, 0);
                lean_inc_ref(v_env_7177_);
                lean_dec(v___x_7176_);
                v___x_7178_ = 2;
                v___x_7179_ = lean_box((v___x_7178_) as usize);
                v___x_7180_ = lean_box((v___y_7171_) as usize);
                lean_inc_ref(v_e_7148_);
                v___x_7181_ = lean_alloc_closure(
                    l_Lean_Meta_evalExpr_x27___boxed as *mut core::ffi::c_void,
                    10,
                    5,
                );
                lean_closure_set(v___x_7181_, 0, lean_box(0));
                lean_closure_set(v___x_7181_, 1, v_typeName_7146_);
                lean_closure_set(v___x_7181_, 2, v_e_7148_);
                lean_closure_set(v___x_7181_, 3, v___x_7179_);
                lean_closure_set(v___x_7181_, 4, v___x_7180_);
                v___x_7182_ = l_Lean_Environment_unlockAsync(v_env_7177_);
                v___x_7183_ =
                    l_Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0___redArg(
                        v___x_7182_,
                        v___x_7181_,
                        v___y_7172_,
                        v___y_7173_,
                        v___y_7174_,
                        v___y_7175_,
                    );
                if lean_obj_tag(v___x_7183_) == 0 {
                    lean_dec_ref(v_e_7148_);
                    return v___x_7183_;
                } else {
                    v_a_7184_ = lean_ctor_get(v___x_7183_, 0);
                    lean_inc(v_a_7184_);
                    v___x_7185_ = l_Lean_Exception_isInterrupt(v_a_7184_);
                    if v___x_7185_ == 0 {
                        lean_inc(v_a_7184_);
                        v___x_7186_ = l_Lean_Exception_isRuntime(v_a_7184_);
                        v___y_7155_ = v___x_7183_;
                        v___y_7156_ = v___y_7174_;
                        v___y_7157_ = v___y_7172_;
                        v___y_7158_ = v_a_7184_;
                        v___y_7159_ = v___y_7173_;
                        v___y_7160_ = v___y_7175_;
                        v___y_7161_ = v___x_7186_;
                        state = 1;
                        continue;
                    } else {
                        v___y_7155_ = v___x_7183_;
                        v___y_7156_ = v___y_7174_;
                        v___y_7157_ = v___y_7172_;
                        v___y_7158_ = v_a_7184_;
                        v___y_7159_ = v___y_7173_;
                        v___y_7160_ = v___y_7175_;
                        v___y_7161_ = v___x_7185_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7192_ = 1;
                lean_inc(v_typeName_7146_);
                v___x_7193_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2(v_typeName_7146_, v___x_7192_, v___y_7188_, v___y_7189_, v___y_7190_, v___y_7191_);
                if lean_obj_tag(v___x_7193_) == 0 {
                    lean_dec_ref_known(v___x_7193_, 1);
                    lean_inc(v___y_7191_);
                    lean_inc_ref(v___y_7190_);
                    lean_inc(v___y_7189_);
                    lean_inc_ref(v___y_7188_);
                    lean_inc_ref(v_e_7148_);
                    v___x_7194_ = lean_infer_type(
                        v_e_7148_,
                        v___y_7188_,
                        v___y_7189_,
                        v___y_7190_,
                        v___y_7191_,
                    );
                    if lean_obj_tag(v___x_7194_) == 0 {
                        v_a_7195_ = lean_ctor_get(v___x_7194_, 0);
                        lean_inc_n(v_a_7195_, 2);
                        lean_dec_ref_known(v___x_7194_, 1);
                        v___x_7196_ = lean_box(0);
                        lean_inc(v_typeName_7146_);
                        v___x_7197_ = l_Lean_mkConst(v_typeName_7146_, v___x_7196_);
                        lean_inc_ref(v___x_7197_);
                        v___x_7198_ = l_Lean_Meta_isExprDefEqGuarded(
                            v___x_7197_,
                            v_a_7195_,
                            v___y_7188_,
                            v___y_7189_,
                            v___y_7190_,
                            v___y_7191_,
                        );
                        if lean_obj_tag(v___x_7198_) == 0 {
                            v_a_7199_ = lean_ctor_get(v___x_7198_, 0);
                            lean_inc(v_a_7199_);
                            lean_dec_ref_known(v___x_7198_, 1);
                            v___x_7200_ = (lean_unbox(v_a_7199_) as u8);
                            lean_dec(v_a_7199_);
                            if v___x_7200_ == 0 {
                                v___x_7201_ = lean_box(0);
                                v___x_7202_ = l___private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_extraDeps___closed__0;
                                v___x_7203_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(
                                    v_a_7195_,
                                    v___x_7197_,
                                    v___x_7201_,
                                    v___x_7202_,
                                );
                                if lean_obj_tag(v___x_7203_) == 0 {
                                    v_a_7204_ = lean_ctor_get(v___x_7203_, 0);
                                    lean_inc(v_a_7204_);
                                    lean_dec_ref_known(v___x_7203_, 1);
                                    v___x_7205_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__5_once), _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__5);
                                    v___x_7206_ = lean_unsigned_to_nat(30);
                                    lean_inc_ref(v_e_7148_);
                                    v___x_7207_ = l_Lean_inlineExpr(v_e_7148_, v___x_7206_);
                                    v___x_7208_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_7208_, 0, v___x_7205_);
                                    lean_ctor_set(v___x_7208_, 1, v___x_7207_);
                                    v___x_7209_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_7209_, 0, v___x_7208_);
                                    lean_ctor_set(v___x_7209_, 1, v_a_7204_);
                                    v___x_7210_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__1___redArg(v___x_7209_, v___y_7188_, v___y_7189_, v___y_7190_, v___y_7191_);
                                    if lean_obj_tag(v___x_7210_) == 0 {
                                        lean_dec_ref_known(v___x_7210_, 1);
                                        v___y_7171_ = v___x_7192_;
                                        v___y_7172_ = v___y_7188_;
                                        v___y_7173_ = v___y_7189_;
                                        v___y_7174_ = v___y_7190_;
                                        v___y_7175_ = v___y_7191_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_e_7148_);
                                        lean_dec(v_typeName_7146_);
                                        v_a_7211_ = lean_ctor_get(v___x_7210_, 0);
                                        v_isSharedCheck_7218_ =
                                            (!lean_is_exclusive(v___x_7210_)) as u8;
                                        if v_isSharedCheck_7218_ == 0 {
                                            v___x_7213_ = v___x_7210_;
                                            v_isShared_7214_ = v_isSharedCheck_7218_;
                                            state = 4;
                                            continue;
                                        } else {
                                            lean_inc(v_a_7211_);
                                            lean_dec(v___x_7210_);
                                            v___x_7213_ = lean_box(0);
                                            v_isShared_7214_ = v_isSharedCheck_7218_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_e_7148_);
                                    lean_dec(v_typeName_7146_);
                                    v_a_7219_ = lean_ctor_get(v___x_7203_, 0);
                                    v_isSharedCheck_7226_ = (!lean_is_exclusive(v___x_7203_)) as u8;
                                    if v_isSharedCheck_7226_ == 0 {
                                        v___x_7221_ = v___x_7203_;
                                        v_isShared_7222_ = v_isSharedCheck_7226_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7219_);
                                        lean_dec(v___x_7203_);
                                        v___x_7221_ = lean_box(0);
                                        v_isShared_7222_ = v_isSharedCheck_7226_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_7197_);
                                lean_dec(v_a_7195_);
                                v___y_7171_ = v___x_7192_;
                                v___y_7172_ = v___y_7188_;
                                v___y_7173_ = v___y_7189_;
                                v___y_7174_ = v___y_7190_;
                                v___y_7175_ = v___y_7191_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_7197_);
                            lean_dec(v_a_7195_);
                            lean_dec_ref(v_e_7148_);
                            lean_dec(v_typeName_7146_);
                            v_a_7227_ = lean_ctor_get(v___x_7198_, 0);
                            v_isSharedCheck_7234_ = (!lean_is_exclusive(v___x_7198_)) as u8;
                            if v_isSharedCheck_7234_ == 0 {
                                v___x_7229_ = v___x_7198_;
                                v_isShared_7230_ = v_isSharedCheck_7234_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_7227_);
                                lean_dec(v___x_7198_);
                                v___x_7229_ = lean_box(0);
                                v_isShared_7230_ = v_isSharedCheck_7234_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_7148_);
                        lean_dec(v_typeName_7146_);
                        v_a_7235_ = lean_ctor_get(v___x_7194_, 0);
                        v_isSharedCheck_7242_ = (!lean_is_exclusive(v___x_7194_)) as u8;
                        if v_isSharedCheck_7242_ == 0 {
                            v___x_7237_ = v___x_7194_;
                            v_isShared_7238_ = v_isSharedCheck_7242_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_7235_);
                            lean_dec(v___x_7194_);
                            v___x_7237_ = lean_box(0);
                            v_isShared_7238_ = v_isSharedCheck_7242_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_7148_);
                    lean_dec(v_typeName_7146_);
                    v_a_7243_ = lean_ctor_get(v___x_7193_, 0);
                    v_isSharedCheck_7250_ = (!lean_is_exclusive(v___x_7193_)) as u8;
                    if v_isSharedCheck_7250_ == 0 {
                        v___x_7245_ = v___x_7193_;
                        v_isShared_7246_ = v_isSharedCheck_7250_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_7243_);
                        lean_dec(v___x_7193_);
                        v___x_7245_ = lean_box(0);
                        v_isShared_7246_ = v_isSharedCheck_7250_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_7214_ == 0 {
                    v___x_7216_ = v___x_7213_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7217_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7217_, 0, v_a_7211_);
                    v___x_7216_ = v_reuseFailAlloc_7217_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7216_;
            }
            6 => {
                if v_isShared_7222_ == 0 {
                    v___x_7224_ = v___x_7221_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7225_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7225_, 0, v_a_7219_);
                    v___x_7224_ = v_reuseFailAlloc_7225_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7224_;
            }
            8 => {
                if v_isShared_7230_ == 0 {
                    v___x_7232_ = v___x_7229_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7233_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7233_, 0, v_a_7227_);
                    v___x_7232_ = v_reuseFailAlloc_7233_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7232_;
            }
            10 => {
                if v_isShared_7238_ == 0 {
                    v___x_7240_ = v___x_7237_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7241_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7241_, 0, v_a_7235_);
                    v___x_7240_ = v_reuseFailAlloc_7241_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7240_;
            }
            12 => {
                if v_isShared_7246_ == 0 {
                    v___x_7248_ = v___x_7245_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7249_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7249_, 0, v_a_7243_);
                    v___x_7248_ = v_reuseFailAlloc_7249_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_7248_;
            }
            14 => {
                v___x_7254_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__7_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__7,
                );
                lean_inc(v_typeName_7146_);
                v___x_7255_ = l_Lean_MessageData_ofName(v_typeName_7146_);
                v___x_7256_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7256_, 0, v___x_7254_);
                lean_ctor_set(v___x_7256_, 1, v___x_7255_);
                v___x_7257_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3);
                v___x_7258_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7258_, 0, v___x_7256_);
                lean_ctor_set(v___x_7258_, 1, v___x_7257_);
                v___x_7259_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7259_, 0, v___x_7258_);
                lean_ctor_set(v___x_7259_, 1, v___y_7253_);
                v___x_7260_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__9_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalMetaEval___redArg___closed__9,
                );
                v___x_7261_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7261_, 0, v___x_7259_);
                lean_ctor_set(v___x_7261_, 1, v___x_7260_);
                v___x_7262_ =
                    l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__1___redArg(
                        v___x_7261_,
                        v_a_7149_,
                        v_a_7150_,
                        v_a_7151_,
                        v_a_7152_,
                    );
                if lean_obj_tag(v___x_7262_) == 0 {
                    lean_dec_ref_known(v___x_7262_, 1);
                    v___y_7188_ = v_a_7149_;
                    v___y_7189_ = v_a_7150_;
                    v___y_7190_ = v_a_7151_;
                    v___y_7191_ = v_a_7152_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v_e_7148_);
                    lean_dec(v_typeName_7146_);
                    v_a_7263_ = lean_ctor_get(v___x_7262_, 0);
                    v_isSharedCheck_7270_ = (!lean_is_exclusive(v___x_7262_)) as u8;
                    if v_isSharedCheck_7270_ == 0 {
                        v___x_7265_ = v___x_7262_;
                        v_isShared_7266_ = v_isSharedCheck_7270_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_7263_);
                        lean_dec(v___x_7262_);
                        v___x_7265_ = lean_box(0);
                        v_isShared_7266_ = v_isSharedCheck_7270_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_7266_ == 0 {
                    v___x_7268_ = v___x_7265_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7269_, 0, v_a_7263_);
                    v___x_7268_ = v_reuseFailAlloc_7269_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalMetaEval___redArg___boxed(
    mut v_typeName_7281_: *mut LeanObject,
    mut v_moduleName_x3f_7282_: *mut LeanObject,
    mut v_e_7283_: *mut LeanObject,
    mut v_a_7284_: *mut LeanObject,
    mut v_a_7285_: *mut LeanObject,
    mut v_a_7286_: *mut LeanObject,
    mut v_a_7287_: *mut LeanObject,
    mut v_a_7288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7289_: *mut LeanObject = core::ptr::null_mut();
    v_res_7289_ = l_Lean_Elab_ConfigEval_evalMetaEval___redArg(
        v_typeName_7281_,
        v_moduleName_x3f_7282_,
        v_e_7283_,
        v_a_7284_,
        v_a_7285_,
        v_a_7286_,
        v_a_7287_,
    );
    lean_dec(v_a_7287_);
    lean_dec_ref(v_a_7286_);
    lean_dec(v_a_7285_);
    lean_dec_ref(v_a_7284_);
    return v_res_7289_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalMetaEval(
    mut v_00_u03b1_7290_: *mut LeanObject,
    mut v_typeName_7291_: *mut LeanObject,
    mut v_moduleName_x3f_7292_: *mut LeanObject,
    mut v_e_7293_: *mut LeanObject,
    mut v_a_7294_: *mut LeanObject,
    mut v_a_7295_: *mut LeanObject,
    mut v_a_7296_: *mut LeanObject,
    mut v_a_7297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7299_: *mut LeanObject = core::ptr::null_mut();
    v___x_7299_ = l_Lean_Elab_ConfigEval_evalMetaEval___redArg(
        v_typeName_7291_,
        v_moduleName_x3f_7292_,
        v_e_7293_,
        v_a_7294_,
        v_a_7295_,
        v_a_7296_,
        v_a_7297_,
    );
    return v___x_7299_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalMetaEval___boxed(
    mut v_00_u03b1_7300_: *mut LeanObject,
    mut v_typeName_7301_: *mut LeanObject,
    mut v_moduleName_x3f_7302_: *mut LeanObject,
    mut v_e_7303_: *mut LeanObject,
    mut v_a_7304_: *mut LeanObject,
    mut v_a_7305_: *mut LeanObject,
    mut v_a_7306_: *mut LeanObject,
    mut v_a_7307_: *mut LeanObject,
    mut v_a_7308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7309_: *mut LeanObject = core::ptr::null_mut();
    v_res_7309_ = l_Lean_Elab_ConfigEval_evalMetaEval(
        v_00_u03b1_7300_,
        v_typeName_7301_,
        v_moduleName_x3f_7302_,
        v_e_7303_,
        v_a_7304_,
        v_a_7305_,
        v_a_7306_,
        v_a_7307_,
    );
    lean_dec(v_a_7307_);
    lean_dec_ref(v_a_7306_);
    lean_dec(v_a_7305_);
    lean_dec_ref(v_a_7304_);
    return v_res_7309_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0(
    mut v_env_7310_: *mut LeanObject,
    mut v___y_7311_: *mut LeanObject,
    mut v___y_7312_: *mut LeanObject,
    mut v___y_7313_: *mut LeanObject,
    mut v___y_7314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7316_: *mut LeanObject = core::ptr::null_mut();
    v___x_7316_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___redArg(v_env_7310_, v___y_7312_, v___y_7314_);
    return v___x_7316_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0___boxed(
    mut v_env_7317_: *mut LeanObject,
    mut v___y_7318_: *mut LeanObject,
    mut v___y_7319_: *mut LeanObject,
    mut v___y_7320_: *mut LeanObject,
    mut v___y_7321_: *mut LeanObject,
    mut v___y_7322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7323_: *mut LeanObject = core::ptr::null_mut();
    v_res_7323_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0_spec__0(v_env_7317_, v___y_7318_, v___y_7319_, v___y_7320_, v___y_7321_);
    lean_dec(v___y_7321_);
    lean_dec_ref(v___y_7320_);
    lean_dec(v___y_7319_);
    lean_dec_ref(v___y_7318_);
    return v_res_7323_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0(
    mut v_00_u03b1_7324_: *mut LeanObject,
    mut v_env_7325_: *mut LeanObject,
    mut v_x_7326_: *mut LeanObject,
    mut v___y_7327_: *mut LeanObject,
    mut v___y_7328_: *mut LeanObject,
    mut v___y_7329_: *mut LeanObject,
    mut v___y_7330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7332_: *mut LeanObject = core::ptr::null_mut();
    v___x_7332_ = l_Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0___redArg(
        v_env_7325_,
        v_x_7326_,
        v___y_7327_,
        v___y_7328_,
        v___y_7329_,
        v___y_7330_,
    );
    return v___x_7332_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0___boxed(
    mut v_00_u03b1_7333_: *mut LeanObject,
    mut v_env_7334_: *mut LeanObject,
    mut v_x_7335_: *mut LeanObject,
    mut v___y_7336_: *mut LeanObject,
    mut v___y_7337_: *mut LeanObject,
    mut v___y_7338_: *mut LeanObject,
    mut v___y_7339_: *mut LeanObject,
    mut v___y_7340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7341_: *mut LeanObject = core::ptr::null_mut();
    v_res_7341_ = l_Lean_withEnv___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__0(
        v_00_u03b1_7333_,
        v_env_7334_,
        v_x_7335_,
        v___y_7336_,
        v___y_7337_,
        v___y_7338_,
        v___y_7339_,
    );
    lean_dec(v___y_7339_);
    lean_dec_ref(v___y_7338_);
    lean_dec(v___y_7337_);
    lean_dec_ref(v___y_7336_);
    return v_res_7341_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__1(
    mut v_00_u03b1_7342_: *mut LeanObject,
    mut v_msg_7343_: *mut LeanObject,
    mut v___y_7344_: *mut LeanObject,
    mut v___y_7345_: *mut LeanObject,
    mut v___y_7346_: *mut LeanObject,
    mut v___y_7347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7349_: *mut LeanObject = core::ptr::null_mut();
    v___x_7349_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__1___redArg(
        v_msg_7343_,
        v___y_7344_,
        v___y_7345_,
        v___y_7346_,
        v___y_7347_,
    );
    return v___x_7349_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__1___boxed(
    mut v_00_u03b1_7350_: *mut LeanObject,
    mut v_msg_7351_: *mut LeanObject,
    mut v___y_7352_: *mut LeanObject,
    mut v___y_7353_: *mut LeanObject,
    mut v___y_7354_: *mut LeanObject,
    mut v___y_7355_: *mut LeanObject,
    mut v___y_7356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7357_: *mut LeanObject = core::ptr::null_mut();
    v_res_7357_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__1(
        v_00_u03b1_7350_,
        v_msg_7351_,
        v___y_7352_,
        v___y_7353_,
        v___y_7354_,
        v___y_7355_,
    );
    lean_dec(v___y_7355_);
    lean_dec_ref(v___y_7354_);
    lean_dec(v___y_7353_);
    lean_dec_ref(v___y_7352_);
    return v_res_7357_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5(
    mut v_00_u03b2_7358_: *mut LeanObject,
    mut v_m_7359_: *mut LeanObject,
    mut v_a_7360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
    v___x_7361_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5___redArg(v_m_7359_, v_a_7360_);
    return v___x_7361_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5___boxed(
    mut v_00_u03b2_7362_: *mut LeanObject,
    mut v_m_7363_: *mut LeanObject,
    mut v_a_7364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7365_: *mut LeanObject = core::ptr::null_mut();
    v_res_7365_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5(v_00_u03b2_7362_, v_m_7363_, v_a_7364_);
    lean_dec(v_a_7364_);
    lean_dec_ref(v_m_7363_);
    return v_res_7365_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4(
    mut v_00_u03b2_7366_: *mut LeanObject,
    mut v_x_7367_: *mut LeanObject,
    mut v_x_7368_: *mut LeanObject,
) -> u8 {
    let mut v___x_7369_: u8 = 0;
    v___x_7369_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4___redArg(v_x_7367_, v_x_7368_);
    return v___x_7369_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b2_7370_: *mut LeanObject,
    mut v_x_7371_: *mut LeanObject,
    mut v_x_7372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7373_: u8 = 0;
    let mut v_r_7374_: *mut LeanObject = core::ptr::null_mut();
    v_res_7373_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4(v_00_u03b2_7370_, v_x_7371_, v_x_7372_);
    lean_dec_ref(v_x_7372_);
    lean_dec_ref(v_x_7371_);
    v_r_7374_ = lean_box((v_res_7373_) as usize);
    return v_r_7374_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5_spec__8(
    mut v_00_u03b2_7375_: *mut LeanObject,
    mut v_a_7376_: *mut LeanObject,
    mut v_x_7377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7378_: *mut LeanObject = core::ptr::null_mut();
    v___x_7378_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5_spec__8___redArg(v_a_7376_, v_x_7377_);
    return v___x_7378_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5_spec__8___boxed(
    mut v_00_u03b2_7379_: *mut LeanObject,
    mut v_a_7380_: *mut LeanObject,
    mut v_x_7381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7382_: *mut LeanObject = core::ptr::null_mut();
    v_res_7382_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__5_spec__8(v_00_u03b2_7379_, v_a_7380_, v_x_7381_);
    lean_dec(v_x_7381_);
    lean_dec(v_a_7380_);
    return v_res_7382_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5(
    mut v_00_u03b2_7383_: *mut LeanObject,
    mut v_x_7384_: *mut LeanObject,
    mut v_x_7385_: usize,
    mut v_x_7386_: *mut LeanObject,
) -> u8 {
    let mut v___x_7387_: u8 = 0;
    v___x_7387_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___redArg(v_x_7384_, v_x_7385_, v_x_7386_);
    return v___x_7387_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5___boxed(
    mut v_00_u03b2_7388_: *mut LeanObject,
    mut v_x_7389_: *mut LeanObject,
    mut v_x_7390_: *mut LeanObject,
    mut v_x_7391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_8842__boxed_7392_: usize = 0;
    let mut v_res_7393_: u8 = 0;
    let mut v_r_7394_: *mut LeanObject = core::ptr::null_mut();
    v_x_8842__boxed_7392_ = lean_unbox_usize(v_x_7390_);
    lean_dec(v_x_7390_);
    v_res_7393_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5(v_00_u03b2_7388_, v_x_7389_, v_x_8842__boxed_7392_, v_x_7391_);
    lean_dec_ref(v_x_7391_);
    lean_dec_ref(v_x_7389_);
    v_r_7394_ = lean_box((v_res_7393_) as usize);
    return v_r_7394_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5_spec__8(
    mut v_00_u03b2_7395_: *mut LeanObject,
    mut v_keys_7396_: *mut LeanObject,
    mut v_vals_7397_: *mut LeanObject,
    mut v_heq_7398_: *mut LeanObject,
    mut v_i_7399_: *mut LeanObject,
    mut v_k_7400_: *mut LeanObject,
) -> u8 {
    let mut v___x_7401_: u8 = 0;
    v___x_7401_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5_spec__8___redArg(v_keys_7396_, v_i_7399_, v_k_7400_);
    return v___x_7401_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5_spec__8___boxed(
    mut v_00_u03b2_7402_: *mut LeanObject,
    mut v_keys_7403_: *mut LeanObject,
    mut v_vals_7404_: *mut LeanObject,
    mut v_heq_7405_: *mut LeanObject,
    mut v_i_7406_: *mut LeanObject,
    mut v_k_7407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7408_: u8 = 0;
    let mut v_r_7409_: *mut LeanObject = core::ptr::null_mut();
    v_res_7408_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_evalMetaEval_spec__2_spec__3_spec__4_spec__5_spec__8(v_00_u03b2_7402_, v_keys_7403_, v_vals_7404_, v_heq_7405_, v_i_7406_, v_k_7407_);
    lean_dec_ref(v_k_7407_);
    lean_dec_ref(v_vals_7404_);
    lean_dec_ref(v_keys_7403_);
    v_r_7409_ = lean_box((v_res_7408_) as usize);
    return v_r_7409_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_7411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: *mut LeanObject = core::ptr::null_mut();
    v___x_7411_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0___closed__0;
    v___x_7412_ = l_Lean_stringToMessageData(v___x_7411_);
    return v___x_7412_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0(
    mut v_type_7413_: *mut LeanObject,
    mut v_typeRef_7414_: *mut LeanObject,
    mut v_x_7415_: *mut LeanObject,
    mut v___y_7416_: *mut LeanObject,
    mut v___y_7417_: *mut LeanObject,
    mut v___y_7418_: *mut LeanObject,
    mut v___y_7419_: *mut LeanObject,
    mut v___y_7420_: *mut LeanObject,
    mut v___y_7421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
    v___x_7423_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0___closed__1,
    );
    v___x_7424_ = l_Lean_MessageData_ofExpr(v_type_7413_);
    v___x_7425_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7425_, 0, v___x_7423_);
    lean_ctor_set(v___x_7425_, 1, v___x_7424_);
    v___x_7426_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_7427_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7427_, 0, v___x_7425_);
    lean_ctor_set(v___x_7427_, 1, v___x_7426_);
    v___x_7428_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1_spec__4_spec__8___redArg(v_typeRef_7414_, v___x_7427_, v___y_7416_, v___y_7417_, v___y_7418_, v___y_7419_, v___y_7420_, v___y_7421_);
    return v___x_7428_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0___boxed(
    mut v_type_7429_: *mut LeanObject,
    mut v_typeRef_7430_: *mut LeanObject,
    mut v_x_7431_: *mut LeanObject,
    mut v___y_7432_: *mut LeanObject,
    mut v___y_7433_: *mut LeanObject,
    mut v___y_7434_: *mut LeanObject,
    mut v___y_7435_: *mut LeanObject,
    mut v___y_7436_: *mut LeanObject,
    mut v___y_7437_: *mut LeanObject,
    mut v___y_7438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7439_: *mut LeanObject = core::ptr::null_mut();
    v_res_7439_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0(
        v_type_7429_,
        v_typeRef_7430_,
        v_x_7431_,
        v___y_7432_,
        v___y_7433_,
        v___y_7434_,
        v___y_7435_,
        v___y_7436_,
        v___y_7437_,
    );
    lean_dec(v___y_7437_);
    lean_dec_ref(v___y_7436_);
    lean_dec(v___y_7435_);
    lean_dec_ref(v___y_7434_);
    lean_dec(v___y_7433_);
    lean_dec_ref(v___y_7432_);
    lean_dec_ref(v_x_7431_);
    lean_dec(v_typeRef_7430_);
    return v_res_7439_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7442_: *mut LeanObject = core::ptr::null_mut();
    v___x_7441_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__0;
    v___x_7442_ = l_String_toRawSubstring_x27(v___x_7441_);
    return v___x_7442_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__5()
-> *mut LeanObject {
    let mut v___x_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7450_: *mut LeanObject = core::ptr::null_mut();
    v___x_7449_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__4;
    v___x_7450_ = lean_mk_syntax_ident(v___x_7449_);
    return v___x_7450_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__6()
-> *mut LeanObject {
    let mut v___x_7451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7452_: *mut LeanObject = core::ptr::null_mut();
    v___x_7451_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__1;
    v___x_7452_ = l_String_toRawSubstring_x27(v___x_7451_);
    return v___x_7452_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__12()
-> *mut LeanObject {
    let mut v___x_7459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: *mut LeanObject = core::ptr::null_mut();
    v___x_7459_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__11;
    v___x_7460_ = l_String_toRawSubstring_x27(v___x_7459_);
    return v___x_7460_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1(
    mut v_type_7473_: *mut LeanObject,
    mut v_kind_7474_: *mut LeanObject,
    mut v_cmdRef_7475_: *mut LeanObject,
    mut v_typeRef_7476_: *mut LeanObject,
    mut v_vis_x3f_7477_: *mut LeanObject,
    mut v___x_7478_: *mut LeanObject,
    mut v___f_7479_: *mut LeanObject,
    mut v___y_7480_: *mut LeanObject,
    mut v___y_7481_: *mut LeanObject,
    mut v___y_7482_: *mut LeanObject,
    mut v___y_7483_: *mut LeanObject,
    mut v___y_7484_: *mut LeanObject,
    mut v___y_7485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_us_7487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_7488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7724_: u8 = 0;
    let mut v___x_7725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7814_: u8 = 0;
    let mut v___x_7815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7834_: u8 = 0;
    let mut v___x_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7841_: u8 = 0;
    let mut v___x_7842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_type_7473_) == 4 {
                    v_us_7487_ = lean_ctor_get(v_type_7473_, 1);
                    if lean_obj_tag(v_us_7487_) == 0 {
                        lean_dec_ref(v___y_7480_);
                        lean_dec_ref(v___f_7479_);
                        v_declName_7488_ = lean_ctor_get(v_type_7473_, 0);
                        lean_inc(v_declName_7488_);
                        lean_dec_ref_known(v_type_7473_, 2);
                        v___x_7489_ = lean_st_ref_get(v___y_7485_);
                        lean_dec(v___y_7485_);
                        v_env_7828_ = lean_ctor_get(v___x_7489_, 0);
                        lean_inc_ref(v_env_7828_);
                        lean_dec(v___x_7489_);
                        v___x_7829_ =
                            l_Lean_Environment_getModuleIdxFor_x3f(v_env_7828_, v_declName_7488_);
                        if lean_obj_tag(v___x_7829_) == 0 {
                            lean_dec_ref(v_env_7828_);
                            v___x_7830_ = lean_box(0);
                            v___y_7810_ = v___x_7830_;
                            state = 5;
                            continue;
                        } else {
                            v_val_7831_ = lean_ctor_get(v___x_7829_, 0);
                            v_isSharedCheck_7841_ = (!lean_is_exclusive(v___x_7829_)) as u8;
                            if v_isSharedCheck_7841_ == 0 {
                                v___x_7833_ = v___x_7829_;
                                v_isShared_7834_ = v_isSharedCheck_7841_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_val_7831_);
                                lean_dec(v___x_7829_);
                                v___x_7833_ = lean_box(0);
                                v_isShared_7834_ = v_isSharedCheck_7841_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_vis_x3f_7477_);
                        lean_dec(v_kind_7474_);
                        lean_inc(v___y_7483_);
                        lean_inc_ref(v___y_7482_);
                        lean_inc(v___y_7481_);
                        v___x_7842_ = lean_apply_8(
                            v___f_7479_,
                            v_type_7473_,
                            v___y_7480_,
                            v___y_7481_,
                            v___y_7482_,
                            v___y_7483_,
                            v___y_7484_,
                            v___y_7485_,
                            lean_box(0),
                        );
                        return v___x_7842_;
                    }
                } else {
                    lean_dec(v_vis_x3f_7477_);
                    lean_dec(v_kind_7474_);
                    lean_inc(v___y_7483_);
                    lean_inc_ref(v___y_7482_);
                    lean_inc(v___y_7481_);
                    v___x_7843_ = lean_apply_8(
                        v___f_7479_,
                        v_type_7473_,
                        v___y_7480_,
                        v___y_7481_,
                        v___y_7482_,
                        v___y_7483_,
                        v___y_7484_,
                        v___y_7485_,
                        lean_box(0),
                    );
                    return v___x_7843_;
                }
            }
            1 => {
                lean_inc(v___y_7506_);
                lean_inc_n(v___y_7495_, 6);
                lean_inc_n(v___y_7491_, 28);
                v___x_7528_ = l_Lean_Syntax_node3(
                    v___y_7491_,
                    v___y_7495_,
                    v___y_7521_,
                    v___y_7506_,
                    v___y_7527_,
                );
                lean_inc_n(v___y_7526_, 2);
                v___x_7529_ =
                    l_Lean_Syntax_node2(v___y_7491_, v___y_7526_, v___y_7507_, v___x_7528_);
                v___x_7530_ =
                    l_Lean_Syntax_node2(v___y_7491_, v___y_7514_, v___y_7511_, v___x_7529_);
                lean_inc_n(v___y_7518_, 10);
                lean_inc(v___y_7497_);
                lean_inc(v___y_7513_);
                v___x_7531_ = l_Lean_Syntax_node3(
                    v___y_7491_,
                    v___y_7513_,
                    v___y_7497_,
                    v___y_7518_,
                    v___x_7530_,
                );
                v___x_7532_ = l_Lean_Syntax_node3(
                    v___y_7491_,
                    v___y_7495_,
                    v___y_7518_,
                    v___y_7518_,
                    v___x_7531_,
                );
                lean_inc(v___y_7525_);
                v___x_7533_ =
                    l_Lean_Syntax_node2(v___y_7491_, v___y_7525_, v___y_7508_, v___x_7532_);
                v___x_7534_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__23;
                v___x_7535_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__24
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__24_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__24,
                );
                v___x_7536_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__25;
                lean_inc_n(v___y_7510_, 3);
                lean_inc_n(v___y_7519_, 3);
                v___x_7537_ = l_Lean_addMacroScope(v___y_7519_, v___x_7536_, v___y_7510_);
                lean_inc_ref(v___y_7498_);
                lean_inc_ref_n(v___y_7509_, 3);
                lean_inc_ref_n(v___y_7515_, 9);
                v___x_7538_ = l_Lean_Name_mkStr5(
                    v___y_7515_,
                    v___y_7509_,
                    v___y_7498_,
                    v___y_7492_,
                    v___x_7534_,
                );
                lean_inc_n(v___y_7512_, 2);
                v___x_7539_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7539_, 0, v___x_7538_);
                lean_ctor_set(v___x_7539_, 1, v___y_7512_);
                lean_inc_n(v___y_7499_, 3);
                v___x_7540_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7540_, 0, v___x_7539_);
                lean_ctor_set(v___x_7540_, 1, v___y_7499_);
                v___x_7541_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_7541_, 0, v___y_7491_);
                lean_ctor_set(v___x_7541_, 1, v___x_7535_);
                lean_ctor_set(v___x_7541_, 2, v___x_7537_);
                lean_ctor_set(v___x_7541_, 3, v___x_7540_);
                v___x_7542_ =
                    l_Lean_Syntax_node2(v___y_7491_, v___y_7505_, v___x_7541_, v___y_7518_);
                v___x_7543_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__27_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__27,
                );
                v___x_7544_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__28;
                v___x_7545_ = l_Lean_addMacroScope(v___y_7519_, v___x_7544_, v___y_7510_);
                v___x_7546_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__30;
                v___x_7547_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7547_, 0, v___x_7546_);
                lean_ctor_set(v___x_7547_, 1, v___y_7512_);
                v___x_7548_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7548_, 0, v___x_7547_);
                lean_ctor_set(v___x_7548_, 1, v___y_7499_);
                v___x_7549_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_7549_, 0, v___y_7491_);
                lean_ctor_set(v___x_7549_, 1, v___x_7543_);
                lean_ctor_set(v___x_7549_, 2, v___x_7545_);
                lean_ctor_set(v___x_7549_, 3, v___x_7548_);
                v___x_7550_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__8;
                lean_inc_ref_n(v___y_7493_, 2);
                lean_inc_ref_n(v___y_7500_, 2);
                v___x_7551_ =
                    l_Lean_Name_mkStr4(v___y_7515_, v___y_7500_, v___y_7493_, v___x_7550_);
                v___x_7552_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__10;
                v___x_7553_ =
                    l_Lean_Name_mkStr4(v___y_7515_, v___y_7500_, v___y_7493_, v___x_7552_);
                v___x_7554_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__12;
                v___x_7555_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7555_, 0, v___y_7491_);
                lean_ctor_set(v___x_7555_, 1, v___x_7554_);
                v___x_7556_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__14;
                v___x_7557_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__16), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__16_once), _init_l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__16);
                v___x_7558_ = lean_box(0);
                v___x_7559_ = l_Lean_addMacroScope(v___y_7519_, v___x_7558_, v___y_7510_);
                v___x_7560_ = l_Lean_Name_mkStr3(v___y_7515_, v___y_7509_, v___y_7498_);
                v___x_7561_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7561_, 0, v___x_7560_);
                v___x_7562_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__20;
                lean_inc_ref_n(v___y_7520_, 2);
                v___x_7563_ = l_Lean_Name_mkStr3(v___y_7515_, v___x_7562_, v___y_7520_);
                v___x_7564_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7564_, 0, v___x_7563_);
                v___x_7565_ = l_Lean_Name_mkStr3(v___y_7515_, v___y_7509_, v___y_7520_);
                v___x_7566_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7566_, 0, v___x_7565_);
                v___x_7567_ = l_Lean_Name_mkStr3(v___y_7515_, v___y_7509_, v___y_7493_);
                v___x_7568_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7568_, 0, v___x_7567_);
                v___x_7569_ = l_Lean_Name_mkStr2(v___y_7515_, v___x_7562_);
                v___x_7570_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7570_, 0, v___x_7569_);
                v___x_7571_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7571_, 0, v___x_7570_);
                lean_ctor_set(v___x_7571_, 1, v___y_7499_);
                v___x_7572_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7572_, 0, v___x_7568_);
                lean_ctor_set(v___x_7572_, 1, v___x_7571_);
                v___x_7573_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7573_, 0, v___x_7566_);
                lean_ctor_set(v___x_7573_, 1, v___x_7572_);
                v___x_7574_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7574_, 0, v___x_7564_);
                lean_ctor_set(v___x_7574_, 1, v___x_7573_);
                v___x_7575_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7575_, 0, v___y_7524_);
                lean_ctor_set(v___x_7575_, 1, v___x_7574_);
                v___x_7576_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7576_, 0, v___x_7561_);
                lean_ctor_set(v___x_7576_, 1, v___x_7575_);
                v___x_7577_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_7577_, 0, v___y_7491_);
                lean_ctor_set(v___x_7577_, 1, v___x_7557_);
                lean_ctor_set(v___x_7577_, 2, v___x_7559_);
                lean_ctor_set(v___x_7577_, 3, v___x_7576_);
                v___x_7578_ = l_Lean_Syntax_node1(v___y_7491_, v___x_7556_, v___x_7577_);
                v___x_7579_ =
                    l_Lean_Syntax_node2(v___y_7491_, v___x_7553_, v___x_7555_, v___x_7578_);
                v___x_7580_ =
                    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__0;
                v___x_7581_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__1_once), _init_l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__1);
                v___x_7582_ =
                    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__2;
                v___x_7583_ = l_Lean_addMacroScope(v___y_7519_, v___x_7582_, v___y_7510_);
                v___x_7584_ = l_Lean_Name_mkStr2(v___y_7515_, v___x_7580_);
                v___x_7585_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7585_, 0, v___x_7584_);
                lean_ctor_set(v___x_7585_, 1, v___y_7512_);
                v___x_7586_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7586_, 0, v___x_7585_);
                lean_ctor_set(v___x_7586_, 1, v___y_7499_);
                v___x_7587_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_7587_, 0, v___y_7491_);
                lean_ctor_set(v___x_7587_, 1, v___x_7581_);
                lean_ctor_set(v___x_7587_, 2, v___x_7583_);
                lean_ctor_set(v___x_7587_, 3, v___x_7586_);
                v___x_7588_ =
                    l_Lean_Syntax_node2(v___y_7491_, v___y_7494_, v___y_7501_, v___y_7506_);
                v___x_7589_ = l_Lean_Syntax_node1(v___y_7491_, v___y_7495_, v___x_7588_);
                v___x_7590_ =
                    l_Lean_Syntax_node2(v___y_7491_, v___y_7526_, v___x_7587_, v___x_7589_);
                v___x_7591_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__36;
                v___x_7592_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7592_, 0, v___y_7491_);
                lean_ctor_set(v___x_7592_, 1, v___x_7591_);
                v___x_7593_ = l_Lean_Syntax_node3(
                    v___y_7491_,
                    v___x_7551_,
                    v___x_7579_,
                    v___x_7590_,
                    v___x_7592_,
                );
                v___x_7594_ = l_Lean_Syntax_node1(v___y_7491_, v___y_7495_, v___x_7593_);
                v___x_7595_ =
                    l_Lean_Syntax_node2(v___y_7491_, v___y_7526_, v___x_7549_, v___x_7594_);
                v___x_7596_ = l_Lean_Syntax_node3(
                    v___y_7491_,
                    v___y_7513_,
                    v___y_7497_,
                    v___y_7518_,
                    v___x_7595_,
                );
                v___x_7597_ = l_Lean_Syntax_node3(
                    v___y_7491_,
                    v___y_7495_,
                    v___y_7518_,
                    v___y_7518_,
                    v___x_7596_,
                );
                v___x_7598_ =
                    l_Lean_Syntax_node2(v___y_7491_, v___y_7525_, v___x_7542_, v___x_7597_);
                v___x_7599_ = l_Lean_Syntax_node3(
                    v___y_7491_,
                    v___y_7495_,
                    v___x_7533_,
                    v___y_7518_,
                    v___x_7598_,
                );
                v___x_7600_ = l_Lean_Syntax_node1(v___y_7491_, v___y_7504_, v___x_7599_);
                v___x_7601_ = l_Lean_Syntax_node3(
                    v___y_7491_,
                    v___y_7496_,
                    v___y_7503_,
                    v___x_7600_,
                    v___y_7518_,
                );
                v___x_7602_ = l_Lean_Syntax_node6(
                    v___y_7491_,
                    v___y_7522_,
                    v_kind_7474_,
                    v___y_7517_,
                    v___y_7518_,
                    v___y_7518_,
                    v___y_7516_,
                    v___x_7601_,
                );
                lean_inc(v___y_7523_);
                v___x_7603_ =
                    l_Lean_Syntax_node2(v___y_7491_, v___y_7523_, v___y_7502_, v___x_7602_);
                v___x_7604_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7604_, 0, v___x_7603_);
                return v___x_7604_;
            }
            2 => {
                v___x_7644_ = lean_unsigned_to_nat(1);
                v___x_7645_ = lean_mk_empty_array_with_capacity(v___x_7644_);
                v___x_7646_ = lean_array_push(v___x_7645_, v___y_7643_);
                lean_inc(v___y_7625_);
                v___x_7647_ = l_Lean_Syntax_mkCApp(v___y_7625_, v___x_7646_);
                v___y_7491_ = v___y_7607_;
                v___y_7492_ = v___y_7606_;
                v___y_7493_ = v___y_7608_;
                v___y_7494_ = v___y_7609_;
                v___y_7495_ = v___y_7610_;
                v___y_7496_ = v___y_7611_;
                v___y_7497_ = v___y_7615_;
                v___y_7498_ = v___y_7614_;
                v___y_7499_ = v___y_7613_;
                v___y_7500_ = v___y_7612_;
                v___y_7501_ = v___y_7616_;
                v___y_7502_ = v___y_7617_;
                v___y_7503_ = v___y_7618_;
                v___y_7504_ = v___y_7619_;
                v___y_7505_ = v___y_7620_;
                v___y_7506_ = v___y_7621_;
                v___y_7507_ = v___y_7622_;
                v___y_7508_ = v___y_7623_;
                v___y_7509_ = v___y_7624_;
                v___y_7510_ = v___y_7626_;
                v___y_7511_ = v___y_7627_;
                v___y_7512_ = v___y_7628_;
                v___y_7513_ = v___y_7630_;
                v___y_7514_ = v___y_7631_;
                v___y_7515_ = v___y_7629_;
                v___y_7516_ = v___y_7633_;
                v___y_7517_ = v___y_7632_;
                v___y_7518_ = v___y_7635_;
                v___y_7519_ = v___y_7634_;
                v___y_7520_ = v___y_7636_;
                v___y_7521_ = v___y_7637_;
                v___y_7522_ = v___y_7638_;
                v___y_7523_ = v___y_7639_;
                v___y_7524_ = v___y_7641_;
                v___y_7525_ = v___y_7640_;
                v___y_7526_ = v___y_7642_;
                v___y_7527_ = v___x_7647_;
                state = 1;
                continue;
            }
            3 => {
                if lean_obj_tag(v___y_7654_) == 0 {
                    v___x_7686_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__5_once), _init_l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__5);
                    v___y_7491_ = v___y_7650_;
                    v___y_7492_ = v___y_7649_;
                    v___y_7493_ = v___y_7651_;
                    v___y_7494_ = v___y_7652_;
                    v___y_7495_ = v___y_7653_;
                    v___y_7496_ = v___y_7655_;
                    v___y_7497_ = v___y_7659_;
                    v___y_7498_ = v___y_7658_;
                    v___y_7499_ = v___y_7657_;
                    v___y_7500_ = v___y_7656_;
                    v___y_7501_ = v___y_7660_;
                    v___y_7502_ = v___y_7661_;
                    v___y_7503_ = v___y_7662_;
                    v___y_7504_ = v___y_7663_;
                    v___y_7505_ = v___y_7664_;
                    v___y_7506_ = v___y_7685_;
                    v___y_7507_ = v___y_7665_;
                    v___y_7508_ = v___y_7666_;
                    v___y_7509_ = v___y_7667_;
                    v___y_7510_ = v___y_7668_;
                    v___y_7511_ = v___y_7669_;
                    v___y_7512_ = v___y_7670_;
                    v___y_7513_ = v___y_7671_;
                    v___y_7514_ = v___y_7672_;
                    v___y_7515_ = v___y_7673_;
                    v___y_7516_ = v___y_7675_;
                    v___y_7517_ = v___y_7674_;
                    v___y_7518_ = v___y_7677_;
                    v___y_7519_ = v___y_7676_;
                    v___y_7520_ = v___y_7678_;
                    v___y_7521_ = v___y_7679_;
                    v___y_7522_ = v___y_7680_;
                    v___y_7523_ = v___y_7681_;
                    v___y_7524_ = v___y_7683_;
                    v___y_7525_ = v___y_7682_;
                    v___y_7526_ = v___y_7684_;
                    v___y_7527_ = v___x_7686_;
                    state = 1;
                    continue;
                } else {
                    v_val_7687_ = lean_ctor_get(v___y_7654_, 0);
                    lean_inc_n(v_val_7687_, 2);
                    lean_dec_ref_known(v___y_7654_, 1);
                    v___x_7688_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__30;
                    lean_inc(v___y_7670_);
                    v___x_7689_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                        v___y_7670_,
                        v_val_7687_,
                    );
                    if lean_obj_tag(v___x_7689_) == 0 {
                        v___x_7690_ = l_Lean_quoteNameMk(v_val_7687_);
                        v___y_7606_ = v___y_7649_;
                        v___y_7607_ = v___y_7650_;
                        v___y_7608_ = v___y_7651_;
                        v___y_7609_ = v___y_7652_;
                        v___y_7610_ = v___y_7653_;
                        v___y_7611_ = v___y_7655_;
                        v___y_7612_ = v___y_7656_;
                        v___y_7613_ = v___y_7657_;
                        v___y_7614_ = v___y_7658_;
                        v___y_7615_ = v___y_7659_;
                        v___y_7616_ = v___y_7660_;
                        v___y_7617_ = v___y_7661_;
                        v___y_7618_ = v___y_7662_;
                        v___y_7619_ = v___y_7663_;
                        v___y_7620_ = v___y_7664_;
                        v___y_7621_ = v___y_7685_;
                        v___y_7622_ = v___y_7665_;
                        v___y_7623_ = v___y_7666_;
                        v___y_7624_ = v___y_7667_;
                        v___y_7625_ = v___x_7688_;
                        v___y_7626_ = v___y_7668_;
                        v___y_7627_ = v___y_7669_;
                        v___y_7628_ = v___y_7670_;
                        v___y_7629_ = v___y_7673_;
                        v___y_7630_ = v___y_7671_;
                        v___y_7631_ = v___y_7672_;
                        v___y_7632_ = v___y_7674_;
                        v___y_7633_ = v___y_7675_;
                        v___y_7634_ = v___y_7676_;
                        v___y_7635_ = v___y_7677_;
                        v___y_7636_ = v___y_7678_;
                        v___y_7637_ = v___y_7679_;
                        v___y_7638_ = v___y_7680_;
                        v___y_7639_ = v___y_7681_;
                        v___y_7640_ = v___y_7682_;
                        v___y_7641_ = v___y_7683_;
                        v___y_7642_ = v___y_7684_;
                        v___y_7643_ = v___x_7690_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_val_7687_);
                        v_val_7691_ = lean_ctor_get(v___x_7689_, 0);
                        lean_inc(v_val_7691_);
                        lean_dec_ref_known(v___x_7689_, 1);
                        v___x_7692_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__59;
                        lean_inc_ref(v___y_7651_);
                        lean_inc_ref(v___y_7656_);
                        lean_inc_ref(v___y_7673_);
                        v___x_7693_ =
                            l_Lean_Name_mkStr4(v___y_7673_, v___y_7656_, v___y_7651_, v___x_7692_);
                        v___x_7694_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__2;
                        v___x_7695_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__60;
                        v___x_7696_ = lean_string_intercalate(v___x_7695_, v_val_7691_);
                        v___x_7697_ = lean_string_append(v___x_7694_, v___x_7696_);
                        lean_dec_ref(v___x_7696_);
                        v___x_7698_ = lean_box(2);
                        v___x_7699_ = l_Lean_Syntax_mkNameLit(v___x_7697_, v___x_7698_);
                        v___x_7700_ = lean_unsigned_to_nat(1);
                        v___x_7701_ = lean_mk_empty_array_with_capacity(v___x_7700_);
                        v___x_7702_ = lean_array_push(v___x_7701_, v___x_7699_);
                        v___x_7703_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_7703_, 0, v___x_7698_);
                        lean_ctor_set(v___x_7703_, 1, v___x_7693_);
                        lean_ctor_set(v___x_7703_, 2, v___x_7702_);
                        v___y_7606_ = v___y_7649_;
                        v___y_7607_ = v___y_7650_;
                        v___y_7608_ = v___y_7651_;
                        v___y_7609_ = v___y_7652_;
                        v___y_7610_ = v___y_7653_;
                        v___y_7611_ = v___y_7655_;
                        v___y_7612_ = v___y_7656_;
                        v___y_7613_ = v___y_7657_;
                        v___y_7614_ = v___y_7658_;
                        v___y_7615_ = v___y_7659_;
                        v___y_7616_ = v___y_7660_;
                        v___y_7617_ = v___y_7661_;
                        v___y_7618_ = v___y_7662_;
                        v___y_7619_ = v___y_7663_;
                        v___y_7620_ = v___y_7664_;
                        v___y_7621_ = v___y_7685_;
                        v___y_7622_ = v___y_7665_;
                        v___y_7623_ = v___y_7666_;
                        v___y_7624_ = v___y_7667_;
                        v___y_7625_ = v___x_7688_;
                        v___y_7626_ = v___y_7668_;
                        v___y_7627_ = v___y_7669_;
                        v___y_7628_ = v___y_7670_;
                        v___y_7629_ = v___y_7673_;
                        v___y_7630_ = v___y_7671_;
                        v___y_7631_ = v___y_7672_;
                        v___y_7632_ = v___y_7674_;
                        v___y_7633_ = v___y_7675_;
                        v___y_7634_ = v___y_7676_;
                        v___y_7635_ = v___y_7677_;
                        v___y_7636_ = v___y_7678_;
                        v___y_7637_ = v___y_7679_;
                        v___y_7638_ = v___y_7680_;
                        v___y_7639_ = v___y_7681_;
                        v___y_7640_ = v___y_7682_;
                        v___y_7641_ = v___y_7683_;
                        v___y_7642_ = v___y_7684_;
                        v___y_7643_ = v___x_7703_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                lean_inc_ref(v___y_7717_);
                v___x_7719_ = l_Array_append___redArg(v___y_7717_, v___y_7718_);
                lean_dec_ref(v___y_7718_);
                lean_inc_n(v___y_7707_, 2);
                lean_inc_n(v___y_7705_, 16);
                v___x_7720_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7720_, 0, v___y_7705_);
                lean_ctor_set(v___x_7720_, 1, v___y_7707_);
                lean_ctor_set(v___x_7720_, 2, v___x_7719_);
                lean_inc_n(v___y_7712_, 8);
                lean_inc(v___y_7709_);
                v___x_7721_ = l_Lean_Syntax_node7(
                    v___y_7705_,
                    v___y_7709_,
                    v___y_7712_,
                    v___y_7712_,
                    v___x_7720_,
                    v___y_7712_,
                    v___y_7712_,
                    v___y_7712_,
                    v___y_7712_,
                );
                v___x_7722_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__13;
                lean_inc_ref_n(v___y_7714_, 3);
                lean_inc_ref_n(v___y_7711_, 11);
                lean_inc_ref_n(v___y_7710_, 14);
                v___x_7723_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___y_7711_, v___y_7714_, v___x_7722_);
                v___x_7724_ = 1;
                v___x_7725_ = l_Lean_SourceInfo_fromRef(v_cmdRef_7475_, v___x_7724_);
                v___x_7726_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7726_, 0, v___x_7725_);
                lean_ctor_set(v___x_7726_, 1, v___x_7722_);
                v___x_7727_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__14;
                v___x_7728_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___y_7711_, v___y_7714_, v___x_7727_);
                v___x_7729_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__8;
                v___x_7730_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__44;
                v___x_7731_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___y_7711_, v___x_7729_, v___x_7730_);
                v___x_7732_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__45;
                v___x_7733_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7733_, 0, v___y_7705_);
                lean_ctor_set(v___x_7733_, 1, v___x_7732_);
                v___x_7734_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__9;
                v___x_7735_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___y_7711_, v___x_7729_, v___x_7734_);
                v___x_7736_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__1;
                v___x_7737_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__6_once), _init_l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__6);
                v___x_7738_ =
                    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__7;
                lean_inc_n(v___y_7706_, 3);
                lean_inc_n(v___y_7713_, 3);
                v___x_7739_ = l_Lean_addMacroScope(v___y_7713_, v___x_7738_, v___y_7706_);
                v___x_7740_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__3;
                v___x_7741_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__4;
                v___x_7742_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___x_7740_, v___x_7741_, v___x_7736_);
                v___x_7743_ = lean_box(0);
                lean_inc(v___x_7742_);
                v___x_7744_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7744_, 0, v___x_7742_);
                lean_ctor_set(v___x_7744_, 1, v___x_7743_);
                v___x_7745_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7745_, 0, v___x_7742_);
                lean_inc_ref(v___x_7745_);
                v___x_7746_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7746_, 0, v___x_7745_);
                lean_ctor_set(v___x_7746_, 1, v___x_7743_);
                v___x_7747_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7747_, 0, v___x_7744_);
                lean_ctor_set(v___x_7747_, 1, v___x_7746_);
                v___x_7748_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_7748_, 0, v___y_7705_);
                lean_ctor_set(v___x_7748_, 1, v___x_7737_);
                lean_ctor_set(v___x_7748_, 2, v___x_7739_);
                lean_ctor_set(v___x_7748_, 3, v___x_7747_);
                v___x_7749_ =
                    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__8;
                v___x_7750_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___y_7711_, v___x_7729_, v___x_7749_);
                v___x_7751_ =
                    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__9;
                v___x_7752_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7752_, 0, v___y_7705_);
                lean_ctor_set(v___x_7752_, 1, v___x_7751_);
                lean_inc_ref(v___x_7752_);
                lean_inc(v___x_7750_);
                v___x_7753_ =
                    l_Lean_Syntax_node2(v___y_7705_, v___x_7750_, v___x_7752_, v___y_7715_);
                lean_inc(v___x_7753_);
                v___x_7754_ = l_Lean_Syntax_node1(v___y_7705_, v___y_7707_, v___x_7753_);
                lean_inc(v___x_7735_);
                v___x_7755_ =
                    l_Lean_Syntax_node2(v___y_7705_, v___x_7735_, v___x_7748_, v___x_7754_);
                v___x_7756_ =
                    l_Lean_Syntax_node2(v___y_7705_, v___x_7731_, v___x_7733_, v___x_7755_);
                v___x_7757_ =
                    l_Lean_Syntax_node2(v___y_7705_, v___x_7728_, v___y_7712_, v___x_7756_);
                v___x_7758_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__15;
                v___x_7759_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___y_7711_, v___y_7714_, v___x_7758_);
                v___x_7760_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__16;
                v___x_7761_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7761_, 0, v___y_7705_);
                lean_ctor_set(v___x_7761_, 1, v___x_7760_);
                v___x_7762_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__17;
                v___x_7763_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___y_7711_, v___x_7729_, v___x_7762_);
                v___x_7764_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__18;
                v___x_7765_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___y_7711_, v___x_7729_, v___x_7764_);
                v___x_7766_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__19;
                v___x_7767_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___y_7711_, v___x_7729_, v___x_7766_);
                v___x_7768_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__2;
                v___x_7769_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__20_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__20,
                );
                v___x_7770_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__21;
                v___x_7771_ = l_Lean_addMacroScope(v___y_7713_, v___x_7770_, v___y_7706_);
                v___x_7772_ = l_Lean_Name_mkStr5(
                    v___y_7710_,
                    v___x_7740_,
                    v___x_7741_,
                    v___x_7736_,
                    v___x_7768_,
                );
                v___x_7773_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7773_, 0, v___x_7772_);
                lean_ctor_set(v___x_7773_, 1, v___x_7743_);
                v___x_7774_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7774_, 0, v___x_7773_);
                lean_ctor_set(v___x_7774_, 1, v___x_7743_);
                v___x_7775_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_7775_, 0, v___y_7705_);
                lean_ctor_set(v___x_7775_, 1, v___x_7769_);
                lean_ctor_set(v___x_7775_, 2, v___x_7771_);
                lean_ctor_set(v___x_7775_, 3, v___x_7774_);
                lean_inc(v___x_7767_);
                v___x_7776_ =
                    l_Lean_Syntax_node2(v___y_7705_, v___x_7767_, v___x_7775_, v___y_7712_);
                v___x_7777_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__22;
                v___x_7778_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___y_7711_, v___x_7729_, v___x_7777_);
                v___x_7779_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__55;
                v___x_7780_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7780_, 0, v___y_7705_);
                lean_ctor_set(v___x_7780_, 1, v___x_7779_);
                v___x_7781_ =
                    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__10;
                v___x_7782_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___y_7711_, v___x_7729_, v___x_7781_);
                v___x_7783_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_7783_, 0, v___y_7705_);
                lean_ctor_set(v___x_7783_, 1, v___x_7781_);
                v___x_7784_ =
                    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__11;
                v___x_7785_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__12), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__12_once), _init_l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__12);
                v___x_7786_ =
                    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__13;
                v___x_7787_ = l_Lean_addMacroScope(v___y_7713_, v___x_7786_, v___y_7706_);
                v___x_7788_ =
                    l_Lean_Name_mkStr4(v___y_7710_, v___x_7740_, v___x_7741_, v___x_7784_);
                lean_inc(v___x_7788_);
                v___x_7789_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7789_, 0, v___x_7788_);
                lean_ctor_set(v___x_7789_, 1, v___x_7743_);
                v___x_7790_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7790_, 0, v___x_7788_);
                v___x_7791_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7791_, 0, v___x_7790_);
                lean_ctor_set(v___x_7791_, 1, v___x_7743_);
                v___x_7792_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7792_, 0, v___x_7789_);
                lean_ctor_set(v___x_7792_, 1, v___x_7791_);
                v___x_7793_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_7793_, 0, v___y_7705_);
                lean_ctor_set(v___x_7793_, 1, v___x_7785_);
                lean_ctor_set(v___x_7793_, 2, v___x_7787_);
                lean_ctor_set(v___x_7793_, 3, v___x_7792_);
                lean_inc(v_declName_7488_);
                v___x_7794_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_7743_,
                    v_declName_7488_,
                );
                if lean_obj_tag(v___x_7794_) == 0 {
                    v___x_7795_ = l_Lean_quoteNameMk(v_declName_7488_);
                    v___y_7649_ = v___x_7736_;
                    v___y_7650_ = v___y_7705_;
                    v___y_7651_ = v___x_7729_;
                    v___y_7652_ = v___x_7750_;
                    v___y_7653_ = v___y_7707_;
                    v___y_7654_ = v___y_7708_;
                    v___y_7655_ = v___x_7759_;
                    v___y_7656_ = v___y_7711_;
                    v___y_7657_ = v___x_7743_;
                    v___y_7658_ = v___x_7741_;
                    v___y_7659_ = v___x_7780_;
                    v___y_7660_ = v___x_7752_;
                    v___y_7661_ = v___x_7721_;
                    v___y_7662_ = v___x_7761_;
                    v___y_7663_ = v___x_7763_;
                    v___y_7664_ = v___x_7767_;
                    v___y_7665_ = v___x_7793_;
                    v___y_7666_ = v___x_7776_;
                    v___y_7667_ = v___x_7740_;
                    v___y_7668_ = v___y_7706_;
                    v___y_7669_ = v___x_7783_;
                    v___y_7670_ = v___x_7743_;
                    v___y_7671_ = v___x_7778_;
                    v___y_7672_ = v___x_7782_;
                    v___y_7673_ = v___y_7710_;
                    v___y_7674_ = v___x_7726_;
                    v___y_7675_ = v___x_7757_;
                    v___y_7676_ = v___y_7713_;
                    v___y_7677_ = v___y_7712_;
                    v___y_7678_ = v___y_7714_;
                    v___y_7679_ = v___x_7753_;
                    v___y_7680_ = v___x_7723_;
                    v___y_7681_ = v___y_7716_;
                    v___y_7682_ = v___x_7765_;
                    v___y_7683_ = v___x_7745_;
                    v___y_7684_ = v___x_7735_;
                    v___y_7685_ = v___x_7795_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_declName_7488_);
                    v_val_7796_ = lean_ctor_get(v___x_7794_, 0);
                    lean_inc(v_val_7796_);
                    lean_dec_ref_known(v___x_7794_, 1);
                    v___x_7797_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__59;
                    lean_inc_ref(v___y_7711_);
                    lean_inc_ref(v___y_7710_);
                    v___x_7798_ =
                        l_Lean_Name_mkStr4(v___y_7710_, v___y_7711_, v___x_7729_, v___x_7797_);
                    v___x_7799_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_ConfigEval_DeriveEvalExpr_0__Lean_Elab_ConfigEval_ensureEvalExpr_getIndType_spec__0_spec__0_spec__1___redArg___closed__2;
                    v___x_7800_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__60;
                    v___x_7801_ = lean_string_intercalate(v___x_7800_, v_val_7796_);
                    v___x_7802_ = lean_string_append(v___x_7799_, v___x_7801_);
                    lean_dec_ref(v___x_7801_);
                    v___x_7803_ = lean_box(2);
                    v___x_7804_ = l_Lean_Syntax_mkNameLit(v___x_7802_, v___x_7803_);
                    v___x_7805_ = lean_unsigned_to_nat(1);
                    v___x_7806_ = lean_mk_empty_array_with_capacity(v___x_7805_);
                    v___x_7807_ = lean_array_push(v___x_7806_, v___x_7804_);
                    v___x_7808_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_7808_, 0, v___x_7803_);
                    lean_ctor_set(v___x_7808_, 1, v___x_7798_);
                    lean_ctor_set(v___x_7808_, 2, v___x_7807_);
                    v___y_7649_ = v___x_7736_;
                    v___y_7650_ = v___y_7705_;
                    v___y_7651_ = v___x_7729_;
                    v___y_7652_ = v___x_7750_;
                    v___y_7653_ = v___y_7707_;
                    v___y_7654_ = v___y_7708_;
                    v___y_7655_ = v___x_7759_;
                    v___y_7656_ = v___y_7711_;
                    v___y_7657_ = v___x_7743_;
                    v___y_7658_ = v___x_7741_;
                    v___y_7659_ = v___x_7780_;
                    v___y_7660_ = v___x_7752_;
                    v___y_7661_ = v___x_7721_;
                    v___y_7662_ = v___x_7761_;
                    v___y_7663_ = v___x_7763_;
                    v___y_7664_ = v___x_7767_;
                    v___y_7665_ = v___x_7793_;
                    v___y_7666_ = v___x_7776_;
                    v___y_7667_ = v___x_7740_;
                    v___y_7668_ = v___y_7706_;
                    v___y_7669_ = v___x_7783_;
                    v___y_7670_ = v___x_7743_;
                    v___y_7671_ = v___x_7778_;
                    v___y_7672_ = v___x_7782_;
                    v___y_7673_ = v___y_7710_;
                    v___y_7674_ = v___x_7726_;
                    v___y_7675_ = v___x_7757_;
                    v___y_7676_ = v___y_7713_;
                    v___y_7677_ = v___y_7712_;
                    v___y_7678_ = v___y_7714_;
                    v___y_7679_ = v___x_7753_;
                    v___y_7680_ = v___x_7723_;
                    v___y_7681_ = v___y_7716_;
                    v___y_7682_ = v___x_7765_;
                    v___y_7683_ = v___x_7745_;
                    v___y_7684_ = v___x_7735_;
                    v___y_7685_ = v___x_7808_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v_ref_7811_ = lean_ctor_get(v___y_7484_, 5);
                lean_inc(v_ref_7811_);
                v_quotContext_7812_ = lean_ctor_get(v___y_7484_, 10);
                lean_inc(v_quotContext_7812_);
                v_currMacroScope_7813_ = lean_ctor_get(v___y_7484_, 11);
                lean_inc(v_currMacroScope_7813_);
                lean_dec_ref(v___y_7484_);
                v___x_7814_ = 0;
                lean_inc(v_declName_7488_);
                v___x_7815_ = l_Lean_mkCIdentFrom(v_typeRef_7476_, v_declName_7488_, v___x_7814_);
                v___x_7816_ = l_Lean_SourceInfo_fromRef(v_ref_7811_, v___x_7814_);
                lean_dec(v_ref_7811_);
                v___x_7817_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__0;
                v___x_7818_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__7;
                v___x_7819_ = l_List_forIn_x27_loop___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__6___redArg___closed__21;
                v___x_7820_ =
                    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__14;
                v___x_7821_ =
                    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___closed__15;
                v___x_7822_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__18;
                v___x_7823_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_ensureEvalExpr_spec__4___closed__26);
                lean_inc(v___x_7816_);
                v___x_7824_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_7824_, 0, v___x_7816_);
                lean_ctor_set(v___x_7824_, 1, v___x_7822_);
                lean_ctor_set(v___x_7824_, 2, v___x_7823_);
                if lean_obj_tag(v_vis_x3f_7477_) == 1 {
                    v_val_7825_ = lean_ctor_get(v_vis_x3f_7477_, 0);
                    lean_inc(v_val_7825_);
                    lean_dec_ref_known(v_vis_x3f_7477_, 1);
                    v___x_7826_ = l_Array_mkArray1___redArg(v_val_7825_);
                    v___y_7705_ = v___x_7816_;
                    v___y_7706_ = v_currMacroScope_7813_;
                    v___y_7707_ = v___x_7822_;
                    v___y_7708_ = v___y_7810_;
                    v___y_7709_ = v___x_7821_;
                    v___y_7710_ = v___x_7817_;
                    v___y_7711_ = v___x_7818_;
                    v___y_7712_ = v___x_7824_;
                    v___y_7713_ = v_quotContext_7812_;
                    v___y_7714_ = v___x_7819_;
                    v___y_7715_ = v___x_7815_;
                    v___y_7716_ = v___x_7820_;
                    v___y_7717_ = v___x_7823_;
                    v___y_7718_ = v___x_7826_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_vis_x3f_7477_);
                    v___x_7827_ = l_Lean_Elab_ConfigEval_ensureEvalExpr___lam__1___closed__61;
                    v___y_7705_ = v___x_7816_;
                    v___y_7706_ = v_currMacroScope_7813_;
                    v___y_7707_ = v___x_7822_;
                    v___y_7708_ = v___y_7810_;
                    v___y_7709_ = v___x_7821_;
                    v___y_7710_ = v___x_7817_;
                    v___y_7711_ = v___x_7818_;
                    v___y_7712_ = v___x_7824_;
                    v___y_7713_ = v_quotContext_7812_;
                    v___y_7714_ = v___x_7819_;
                    v___y_7715_ = v___x_7815_;
                    v___y_7716_ = v___x_7820_;
                    v___y_7717_ = v___x_7823_;
                    v___y_7718_ = v___x_7827_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_7835_ = l_Lean_Environment_header(v_env_7828_);
                lean_dec_ref(v_env_7828_);
                v___x_7836_ = l_Lean_EnvironmentHeader_moduleNames(v___x_7835_);
                v___x_7837_ = lean_array_get(v___x_7478_, v___x_7836_, v_val_7831_);
                lean_dec(v_val_7831_);
                lean_dec_ref(v___x_7836_);
                if v_isShared_7834_ == 0 {
                    lean_ctor_set(v___x_7833_, 0, v___x_7837_);
                    v___x_7839_ = v___x_7833_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7840_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7840_, 0, v___x_7837_);
                    v___x_7839_ = v_reuseFailAlloc_7840_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_7810_ = v___x_7839_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___boxed(
    mut v_type_7844_: *mut LeanObject,
    mut v_kind_7845_: *mut LeanObject,
    mut v_cmdRef_7846_: *mut LeanObject,
    mut v_typeRef_7847_: *mut LeanObject,
    mut v_vis_x3f_7848_: *mut LeanObject,
    mut v___x_7849_: *mut LeanObject,
    mut v___f_7850_: *mut LeanObject,
    mut v___y_7851_: *mut LeanObject,
    mut v___y_7852_: *mut LeanObject,
    mut v___y_7853_: *mut LeanObject,
    mut v___y_7854_: *mut LeanObject,
    mut v___y_7855_: *mut LeanObject,
    mut v___y_7856_: *mut LeanObject,
    mut v___y_7857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7858_: *mut LeanObject = core::ptr::null_mut();
    v_res_7858_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1(
        v_type_7844_,
        v_kind_7845_,
        v_cmdRef_7846_,
        v_typeRef_7847_,
        v_vis_x3f_7848_,
        v___x_7849_,
        v___f_7850_,
        v___y_7851_,
        v___y_7852_,
        v___y_7853_,
        v___y_7854_,
        v___y_7855_,
        v___y_7856_,
    );
    lean_dec(v___y_7854_);
    lean_dec_ref(v___y_7853_);
    lean_dec(v___y_7852_);
    lean_dec(v___x_7849_);
    lean_dec(v_typeRef_7847_);
    lean_dec(v_cmdRef_7846_);
    return v_res_7858_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__2(
    mut v_type_7859_: *mut LeanObject,
    mut v_kind_7860_: *mut LeanObject,
    mut v_cmdRef_7861_: *mut LeanObject,
    mut v_typeRef_7862_: *mut LeanObject,
    mut v_vis_x3f_7863_: *mut LeanObject,
    mut v___x_7864_: *mut LeanObject,
    mut v___f_7865_: *mut LeanObject,
    mut v___y_7866_: *mut LeanObject,
    mut v___y_7867_: *mut LeanObject,
    mut v___y_7868_: *mut LeanObject,
    mut v___y_7869_: *mut LeanObject,
    mut v___y_7870_: *mut LeanObject,
    mut v___y_7871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7874_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_7869_);
    lean_inc_ref(v___y_7868_);
    lean_inc(v___y_7867_);
    v___f_7873_ = lean_alloc_closure(
        l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__1___boxed
            as *mut core::ffi::c_void,
        14,
        11,
    );
    lean_closure_set(v___f_7873_, 0, v_type_7859_);
    lean_closure_set(v___f_7873_, 1, v_kind_7860_);
    lean_closure_set(v___f_7873_, 2, v_cmdRef_7861_);
    lean_closure_set(v___f_7873_, 3, v_typeRef_7862_);
    lean_closure_set(v___f_7873_, 4, v_vis_x3f_7863_);
    lean_closure_set(v___f_7873_, 5, v___x_7864_);
    lean_closure_set(v___f_7873_, 6, v___f_7865_);
    lean_closure_set(v___f_7873_, 7, v___y_7866_);
    lean_closure_set(v___f_7873_, 8, v___y_7867_);
    lean_closure_set(v___f_7873_, 9, v___y_7868_);
    lean_closure_set(v___f_7873_, 10, v___y_7869_);
    v___x_7874_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_7873_, v___y_7870_, v___y_7871_);
    return v___x_7874_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__2___boxed(
    mut v_type_7875_: *mut LeanObject,
    mut v_kind_7876_: *mut LeanObject,
    mut v_cmdRef_7877_: *mut LeanObject,
    mut v_typeRef_7878_: *mut LeanObject,
    mut v_vis_x3f_7879_: *mut LeanObject,
    mut v___x_7880_: *mut LeanObject,
    mut v___f_7881_: *mut LeanObject,
    mut v___y_7882_: *mut LeanObject,
    mut v___y_7883_: *mut LeanObject,
    mut v___y_7884_: *mut LeanObject,
    mut v___y_7885_: *mut LeanObject,
    mut v___y_7886_: *mut LeanObject,
    mut v___y_7887_: *mut LeanObject,
    mut v___y_7888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7889_: *mut LeanObject = core::ptr::null_mut();
    v_res_7889_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__2(
        v_type_7875_,
        v_kind_7876_,
        v_cmdRef_7877_,
        v_typeRef_7878_,
        v_vis_x3f_7879_,
        v___x_7880_,
        v___f_7881_,
        v___y_7882_,
        v___y_7883_,
        v___y_7884_,
        v___y_7885_,
        v___y_7886_,
        v___y_7887_,
    );
    lean_dec(v___y_7887_);
    lean_dec_ref(v___y_7886_);
    lean_dec(v___y_7885_);
    lean_dec_ref(v___y_7884_);
    lean_dec(v___y_7883_);
    return v_res_7889_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval(
    mut v_vis_x3f_7890_: *mut LeanObject,
    mut v_kind_7891_: *mut LeanObject,
    mut v_cmdRef_7892_: *mut LeanObject,
    mut v_typeRef_7893_: *mut LeanObject,
    mut v_type_7894_: *mut LeanObject,
    mut v_a_7895_: *mut LeanObject,
    mut v_a_7896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7907_: u8 = 0;
    let mut v___x_7909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_typeRef_7893_);
                lean_inc_ref(v_type_7894_);
                v___f_7898_ = lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__0___boxed
                        as *mut core::ffi::c_void,
                    10,
                    2,
                );
                lean_closure_set(v___f_7898_, 0, v_type_7894_);
                lean_closure_set(v___f_7898_, 1, v_typeRef_7893_);
                v___x_7899_ = lean_box(0);
                v___f_7900_ = lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___lam__2___boxed
                        as *mut core::ffi::c_void,
                    14,
                    7,
                );
                lean_closure_set(v___f_7900_, 0, v_type_7894_);
                lean_closure_set(v___f_7900_, 1, v_kind_7891_);
                lean_closure_set(v___f_7900_, 2, v_cmdRef_7892_);
                lean_closure_set(v___f_7900_, 3, v_typeRef_7893_);
                lean_closure_set(v___f_7900_, 4, v_vis_x3f_7890_);
                lean_closure_set(v___f_7900_, 5, v___x_7899_);
                lean_closure_set(v___f_7900_, 6, v___f_7898_);
                v___x_7901_ =
                    l_Lean_Elab_Command_liftTermElabM___redArg(v___f_7900_, v_a_7895_, v_a_7896_);
                if lean_obj_tag(v___x_7901_) == 0 {
                    v_a_7902_ = lean_ctor_get(v___x_7901_, 0);
                    lean_inc(v_a_7902_);
                    lean_dec_ref_known(v___x_7901_, 1);
                    v___x_7903_ = l_Lean_Elab_Command_elabCommand(v_a_7902_, v_a_7895_, v_a_7896_);
                    return v___x_7903_;
                } else {
                    v_a_7904_ = lean_ctor_get(v___x_7901_, 0);
                    v_isSharedCheck_7911_ = (!lean_is_exclusive(v___x_7901_)) as u8;
                    if v_isSharedCheck_7911_ == 0 {
                        v___x_7906_ = v___x_7901_;
                        v_isShared_7907_ = v_isSharedCheck_7911_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7904_);
                        lean_dec(v___x_7901_);
                        v___x_7906_ = lean_box(0);
                        v_isShared_7907_ = v_isSharedCheck_7911_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7907_ == 0 {
                    v___x_7909_ = v___x_7906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7910_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7910_, 0, v_a_7904_);
                    v___x_7909_ = v_reuseFailAlloc_7910_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval___boxed(
    mut v_vis_x3f_7912_: *mut LeanObject,
    mut v_kind_7913_: *mut LeanObject,
    mut v_cmdRef_7914_: *mut LeanObject,
    mut v_typeRef_7915_: *mut LeanObject,
    mut v_type_7916_: *mut LeanObject,
    mut v_a_7917_: *mut LeanObject,
    mut v_a_7918_: *mut LeanObject,
    mut v_a_7919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7920_: *mut LeanObject = core::ptr::null_mut();
    v_res_7920_ = l_Lean_Elab_ConfigEval_deriveEvalExprUsingMetaEval(
        v_vis_x3f_7912_,
        v_kind_7913_,
        v_cmdRef_7914_,
        v_typeRef_7915_,
        v_type_7916_,
        v_a_7917_,
        v_a_7918_,
    );
    lean_dec(v_a_7918_);
    lean_dec_ref(v_a_7917_);
    return v_res_7920_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclNameGen(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ErrorUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_DeclNameGen(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ErrorUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
}
