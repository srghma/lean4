// Lean compiler output
// Module: Lean.Elab.ConfigEval.Basic
// Imports: Lean.Elab.ConfigEval.Types Lean.Elab.SyntheticMVars Lean.Elab.ConfigEval.Util
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::String::Pattern::Basic::l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2;
use crate::r#gen::Init::Data::String::Pattern::Char::l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed;
use crate::r#gen::Init::Data::String::Pattern::Pred::l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_contains___redArg;
use crate::r#gen::Init::GetElem::l_List_get_x3fInternal___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isAtom, l_Lean_TSyntax_getId, l_Lean_mkCIdentFrom, l_String_toName,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_appendCore, l_Lean_Name_str___override, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getId, l_Lean_Syntax_getNumArgs, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isMissing, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesIdent, l_Lean_Syntax_matchesNull, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed,
    l_ReaderT_instMonadExceptOf___redArg___lam__2, l_ReaderT_instMonadLift___lam__0___boxed,
    l_instMonadExceptOfMonadExceptOf___redArg, lean_erase_macro_scopes,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Exception_isRuntime, l_Lean_instMonadExceptOfExceptionCoreM,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::{
    l_Lean_FileMap_toPosition, l_Lean_instInhabitedFileMap_default,
};
use crate::r#gen::Lean::Elab::ConfigEval::Types::{
    initialize_Lean_Elab_ConfigEval_Types, l_Lean_Elab_ConfigEval_unsupportedExprExceptionId,
    runtime_initialize_Lean_Elab_ConfigEval_Types,
};
use crate::r#gen::Lean::Elab::ConfigEval::Util::{
    initialize_Lean_Elab_ConfigEval_Util, runtime_initialize_Lean_Elab_ConfigEval_Util,
};
use crate::r#gen::Lean::Elab::Exception::{
    l_Lean_Elab_abortTermExceptionId, l_Lean_Elab_isAbortExceptionId,
    l_Lean_Elab_throwAbortTerm___redArg, l_Lean_Elab_unsupportedSyntaxExceptionId,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_InfoTree_substitute;
use crate::r#gen::Lean::Elab::SyntheticMVars::{
    initialize_Lean_Elab_SyntheticMVars,
    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp,
    runtime_initialize_Lean_Elab_SyntheticMVars,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_TermElabM_run___redArg, l_Lean_Elab_Term_addTermInfo_x27,
    l_Lean_Elab_Term_elabTermEnsuringType___boxed,
    l_Lean_Elab_Term_instAddErrorMessageContextTermElabM,
    l_Lean_Elab_Term_instMonadMacroAdapterTermElabM,
    l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed,
    l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed,
    l_Lean_Elab_Term_logUnassignedUsingErrorInfos,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_throwError___redArg, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_const___override, l_Lean_mkAppB, l_Lean_mkConst};
use crate::r#gen::Lean::InternalExceptionId::{
    l_Lean_InternalExceptionId_getName, l_Lean_instBEqInternalExceptionId_beq,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_ofNat, l_Lean_mkLevelParam};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_empty;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_indentExpr, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey, l_Lean_Meta_instMonadMCtxMetaM,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0, l_Lean_instantiateMVars___redArg,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Syntax::{l_Lean_Syntax_hasMissing, l_Lean_Syntax_identComponents};
use crate::r#gen::Lean::Util::Sorry::{l_Lean_Expr_hasSorry, l_Lean_Expr_hasSyntheticSorry};
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_uint32_dec_eq, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_whnf;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6_value:
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
    m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7_value:
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
    m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 11,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8_value:
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
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32,
        116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25_value:
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
    m_data: [10, 111, 102, 32, 116, 121, 112, 101, 32, 96, 0],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27_value:
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
    m_data: [96, 0],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 99, 111, 110, 116, 97, 105, 110, 115,
        32, 96, 115, 111, 114, 114, 121, 96, 58, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32,
        116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 58, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        79, 112, 116, 105, 111, 110, 32, 105, 115, 32, 110, 111, 116, 32, 98, 111, 111, 108, 101,
        97, 110, 45, 118, 97, 108, 117, 101, 100, 44, 32, 115, 111, 32, 96, 40, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        32, 58, 61, 32, 46, 46, 46, 41, 96, 32, 115, 121, 110, 116, 97, 120, 32, 109, 117, 115,
        116, 32, 98, 101, 32, 117, 115, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105,
        111, 110, 32, 111, 112, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2_value:
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
    m_data: [32, 102, 111, 114, 32, 96, 0],
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4_value:
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
    m_data: [32, 96, 0],
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        67, 97, 110, 110, 111, 116, 32, 115, 101, 116, 32, 111, 112, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        32, 117, 115, 105, 110, 103, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111,
        110, 32, 115, 121, 110, 116, 97, 120, 46, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2_value:
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
    m_fun: l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2 as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value:
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
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
        12882480457794858234 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
        9255189395584251158 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9_value:
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
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
        12882480457794858234 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        15761733860085307253 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11_value:
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
    m_data: [43, 0],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12_value:
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
    m_data: [45, 0],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13_value:
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
    m_data: [40, 0],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 58, 32, 0]};
static mut l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0_value:
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
    m_data: [105, 100, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        6041859491766292191 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5_value:
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
    m_data: [95, 99, 102, 103, 95, 100, 117, 109, 109, 121, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        16753651297112092462 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8_value:
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
    m_data: [67, 111, 110, 102, 105, 103, 69, 118, 97, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        17728754291599005030 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value:
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
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<10> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
            + 16) as u16,
        other: 8,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16843009 as *mut crate::leanh::LeanObject,
        65537 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3_value:
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
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4: u64 = 0;
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_value:
    crate::leanh::LeanCtorObject<7> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7
            + 0) as u16,
        other: 7,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(
    mut v_inst_4264_: *mut crate::leanh::LeanObject,
    mut v_stx_4265_: *mut crate::leanh::LeanObject,
    mut v_a_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
    mut v_a_4268_: *mut crate::leanh::LeanObject,
    mut v_a_4269_: *mut crate::leanh::LeanObject,
    mut v_a_4270_: *mut crate::leanh::LeanObject,
    mut v_a_4271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_evalTerm_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4286_: u8 = 0;
    let mut v_cancelTk_x3f_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4288_: u8 = 0;
    let mut v_inheritedTraceOptions_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4296_: u8 = 0;
    let mut v_fst_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v_a_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalTerm_4273_ = crate::leanh::lean_ctor_get(v_inst_4264_, 0);
                crate::leanh::lean_inc_ref(v_evalTerm_4273_);
                crate::leanh::lean_dec_ref(v_inst_4264_);
                v_fileName_4274_ = crate::leanh::lean_ctor_get(v_a_4270_, 0);
                v_fileMap_4275_ = crate::leanh::lean_ctor_get(v_a_4270_, 1);
                v_options_4276_ = crate::leanh::lean_ctor_get(v_a_4270_, 2);
                v_currRecDepth_4277_ = crate::leanh::lean_ctor_get(v_a_4270_, 3);
                v_maxRecDepth_4278_ = crate::leanh::lean_ctor_get(v_a_4270_, 4);
                v_ref_4279_ = crate::leanh::lean_ctor_get(v_a_4270_, 5);
                v_currNamespace_4280_ = crate::leanh::lean_ctor_get(v_a_4270_, 6);
                v_openDecls_4281_ = crate::leanh::lean_ctor_get(v_a_4270_, 7);
                v_initHeartbeats_4282_ = crate::leanh::lean_ctor_get(v_a_4270_, 8);
                v_maxHeartbeats_4283_ = crate::leanh::lean_ctor_get(v_a_4270_, 9);
                v_quotContext_4284_ = crate::leanh::lean_ctor_get(v_a_4270_, 10);
                v_currMacroScope_4285_ = crate::leanh::lean_ctor_get(v_a_4270_, 11);
                v_diag_4286_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4270_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4287_ = crate::leanh::lean_ctor_get(v_a_4270_, 12);
                v_suppressElabErrors_4288_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4270_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4289_ = crate::leanh::lean_ctor_get(v_a_4270_, 13);
                v_ref_4290_ = l_Lean_replaceRef(v_stx_4265_, v_ref_4279_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4289_);
                crate::leanh::lean_inc(v_cancelTk_x3f_4287_);
                crate::leanh::lean_inc(v_currMacroScope_4285_);
                crate::leanh::lean_inc(v_quotContext_4284_);
                crate::leanh::lean_inc(v_maxHeartbeats_4283_);
                crate::leanh::lean_inc(v_initHeartbeats_4282_);
                crate::leanh::lean_inc(v_openDecls_4281_);
                crate::leanh::lean_inc(v_currNamespace_4280_);
                crate::leanh::lean_inc(v_maxRecDepth_4278_);
                crate::leanh::lean_inc(v_currRecDepth_4277_);
                crate::leanh::lean_inc_ref(v_options_4276_);
                crate::leanh::lean_inc_ref(v_fileMap_4275_);
                crate::leanh::lean_inc_ref(v_fileName_4274_);
                v___x_4291_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4291_, 0, v_fileName_4274_);
                crate::leanh::lean_ctor_set(v___x_4291_, 1, v_fileMap_4275_);
                crate::leanh::lean_ctor_set(v___x_4291_, 2, v_options_4276_);
                crate::leanh::lean_ctor_set(v___x_4291_, 3, v_currRecDepth_4277_);
                crate::leanh::lean_ctor_set(v___x_4291_, 4, v_maxRecDepth_4278_);
                crate::leanh::lean_ctor_set(v___x_4291_, 5, v_ref_4290_);
                crate::leanh::lean_ctor_set(v___x_4291_, 6, v_currNamespace_4280_);
                crate::leanh::lean_ctor_set(v___x_4291_, 7, v_openDecls_4281_);
                crate::leanh::lean_ctor_set(v___x_4291_, 8, v_initHeartbeats_4282_);
                crate::leanh::lean_ctor_set(v___x_4291_, 9, v_maxHeartbeats_4283_);
                crate::leanh::lean_ctor_set(v___x_4291_, 10, v_quotContext_4284_);
                crate::leanh::lean_ctor_set(v___x_4291_, 11, v_currMacroScope_4285_);
                crate::leanh::lean_ctor_set(v___x_4291_, 12, v_cancelTk_x3f_4287_);
                crate::leanh::lean_ctor_set(v___x_4291_, 13, v_inheritedTraceOptions_4289_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4291_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_4286_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4291_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4288_,
                );
                crate::leanh::lean_inc(v_a_4271_);
                crate::leanh::lean_inc(v_a_4269_);
                crate::leanh::lean_inc_ref(v_a_4268_);
                crate::leanh::lean_inc(v_a_4267_);
                crate::leanh::lean_inc_ref(v_a_4266_);
                v___x_4292_ = crate::leanh::lean_apply_8(
                    v_evalTerm_4273_,
                    v_stx_4265_,
                    v_a_4266_,
                    v_a_4267_,
                    v_a_4268_,
                    v_a_4269_,
                    v___x_4291_,
                    v_a_4271_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4292_) == 0 {
                    v_a_4293_ = crate::leanh::lean_ctor_get(v___x_4292_, 0);
                    v_isSharedCheck_4301_ = (!crate::leanh::lean_is_exclusive(v___x_4292_)) as u8;
                    if v_isSharedCheck_4301_ == 0 {
                        v___x_4295_ = v___x_4292_;
                        v_isShared_4296_ = v_isSharedCheck_4301_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4293_);
                        crate::leanh::lean_dec(v___x_4292_);
                        v___x_4295_ = crate::leanh::lean_box(0);
                        v_isShared_4296_ = v_isSharedCheck_4301_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4302_ = crate::leanh::lean_ctor_get(v___x_4292_, 0);
                    v_isSharedCheck_4309_ = (!crate::leanh::lean_is_exclusive(v___x_4292_)) as u8;
                    if v_isSharedCheck_4309_ == 0 {
                        v___x_4304_ = v___x_4292_;
                        v_isShared_4305_ = v_isSharedCheck_4309_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4302_);
                        crate::leanh::lean_dec(v___x_4292_);
                        v___x_4304_ = crate::leanh::lean_box(0);
                        v_isShared_4305_ = v_isSharedCheck_4309_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4297_ = crate::leanh::lean_ctor_get(v_a_4293_, 0);
                crate::leanh::lean_inc(v_fst_4297_);
                crate::leanh::lean_dec(v_a_4293_);
                if v_isShared_4296_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4295_, 0, v_fst_4297_);
                    v___x_4299_ = v___x_4295_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_fst_4297_);
                    v___x_4299_ = v_reuseFailAlloc_4300_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4299_;
            }
            3 => {
                if v_isShared_4305_ == 0 {
                    v___x_4307_ = v___x_4304_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
                    v___x_4307_ = v_reuseFailAlloc_4308_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermWithRef___redArg___boxed(
    mut v_inst_4310_: *mut crate::leanh::LeanObject,
    mut v_stx_4311_: *mut crate::leanh::LeanObject,
    mut v_a_4312_: *mut crate::leanh::LeanObject,
    mut v_a_4313_: *mut crate::leanh::LeanObject,
    mut v_a_4314_: *mut crate::leanh::LeanObject,
    mut v_a_4315_: *mut crate::leanh::LeanObject,
    mut v_a_4316_: *mut crate::leanh::LeanObject,
    mut v_a_4317_: *mut crate::leanh::LeanObject,
    mut v_a_4318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4319_ = l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(
        v_inst_4310_,
        v_stx_4311_,
        v_a_4312_,
        v_a_4313_,
        v_a_4314_,
        v_a_4315_,
        v_a_4316_,
        v_a_4317_,
    );
    crate::leanh::lean_dec(v_a_4317_);
    crate::leanh::lean_dec_ref(v_a_4316_);
    crate::leanh::lean_dec(v_a_4315_);
    crate::leanh::lean_dec_ref(v_a_4314_);
    crate::leanh::lean_dec(v_a_4313_);
    crate::leanh::lean_dec_ref(v_a_4312_);
    return v_res_4319_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermWithRef(
    mut v_00_u03b1_4320_: *mut crate::leanh::LeanObject,
    mut v_inst_4321_: *mut crate::leanh::LeanObject,
    mut v_stx_4322_: *mut crate::leanh::LeanObject,
    mut v_a_4323_: *mut crate::leanh::LeanObject,
    mut v_a_4324_: *mut crate::leanh::LeanObject,
    mut v_a_4325_: *mut crate::leanh::LeanObject,
    mut v_a_4326_: *mut crate::leanh::LeanObject,
    mut v_a_4327_: *mut crate::leanh::LeanObject,
    mut v_a_4328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4330_ = l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(
        v_inst_4321_,
        v_stx_4322_,
        v_a_4323_,
        v_a_4324_,
        v_a_4325_,
        v_a_4326_,
        v_a_4327_,
        v_a_4328_,
    );
    return v___x_4330_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermWithRef___boxed(
    mut v_00_u03b1_4331_: *mut crate::leanh::LeanObject,
    mut v_inst_4332_: *mut crate::leanh::LeanObject,
    mut v_stx_4333_: *mut crate::leanh::LeanObject,
    mut v_a_4334_: *mut crate::leanh::LeanObject,
    mut v_a_4335_: *mut crate::leanh::LeanObject,
    mut v_a_4336_: *mut crate::leanh::LeanObject,
    mut v_a_4337_: *mut crate::leanh::LeanObject,
    mut v_a_4338_: *mut crate::leanh::LeanObject,
    mut v_a_4339_: *mut crate::leanh::LeanObject,
    mut v_a_4340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4341_ = l_Lean_Elab_ConfigEval_evalTermWithRef(
        v_00_u03b1_4331_,
        v_inst_4332_,
        v_stx_4333_,
        v_a_4334_,
        v_a_4335_,
        v_a_4336_,
        v_a_4337_,
        v_a_4338_,
        v_a_4339_,
    );
    crate::leanh::lean_dec(v_a_4339_);
    crate::leanh::lean_dec_ref(v_a_4338_);
    crate::leanh::lean_dec(v_a_4337_);
    crate::leanh::lean_dec_ref(v_a_4336_);
    crate::leanh::lean_dec(v_a_4335_);
    crate::leanh::lean_dec_ref(v_a_4334_);
    return v_res_4341_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4342_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_4342_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4343_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0,
    );
    v___x_4344_ = l_StateRefT_x27_instMonad___redArg(v___x_4343_);
    return v___x_4344_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4353_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_4354_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4354_, 0, v___x_4353_);
    return v___f_4354_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4355_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_4356_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4356_, 0, v___x_4355_);
    return v___f_4356_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4357_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11,
    );
    v___f_4358_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10,
    );
    v___x_4359_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4359_, 0, v___f_4358_);
    crate::leanh::lean_ctor_set(v___x_4359_, 1, v___f_4357_);
    return v___x_4359_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4360_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12,
    );
    v___f_4361_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4361_, 0, v___x_4360_);
    return v___f_4361_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4362_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12,
    );
    v___f_4363_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4363_, 0, v___x_4362_);
    return v___f_4363_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4364_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14,
    );
    v___f_4365_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13,
    );
    v___x_4366_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4366_, 0, v___f_4365_);
    crate::leanh::lean_ctor_set(v___x_4366_, 1, v___f_4364_);
    return v___x_4366_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4367_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15,
    );
    v___f_4368_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4368_, 0, v___x_4367_);
    return v___f_4368_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4369_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15,
    );
    v___f_4370_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4370_, 0, v___x_4369_);
    return v___f_4370_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4371_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17,
    );
    v___f_4372_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16,
    );
    v___x_4373_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4373_, 0, v___f_4372_);
    crate::leanh::lean_ctor_set(v___x_4373_, 1, v___f_4371_);
    return v___x_4373_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4374_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18,
    );
    v___f_4375_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4375_, 0, v___x_4374_);
    return v___f_4375_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4376_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18,
    );
    v___f_4377_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4377_, 0, v___x_4376_);
    return v___f_4377_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4378_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20,
    );
    v___f_4379_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19,
    );
    v___x_4380_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4380_, 0, v___f_4379_);
    crate::leanh::lean_ctor_set(v___x_4380_, 1, v___f_4378_);
    return v___x_4380_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4381_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21,
    );
    v___x_4382_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_4381_);
    return v___x_4382_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4384_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23;
    v___x_4385_ = l_Lean_stringToMessageData(v___x_4384_);
    return v___x_4385_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4387_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25;
    v___x_4388_ = l_Lean_stringToMessageData(v___x_4387_);
    return v___x_4388_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4390_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27;
    v___x_4391_ = l_Lean_stringToMessageData(v___x_4390_);
    return v___x_4391_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4393_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29;
    v___x_4394_ = l_Lean_stringToMessageData(v___x_4393_);
    return v___x_4394_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4396_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31;
    v___x_4397_ = l_Lean_stringToMessageData(v___x_4396_);
    return v___x_4397_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(
    mut v_inst_4398_: *mut crate::leanh::LeanObject,
    mut v_stx_4399_: *mut crate::leanh::LeanObject,
    mut v_a_4400_: *mut crate::leanh::LeanObject,
    mut v_a_4401_: *mut crate::leanh::LeanObject,
    mut v_a_4402_: *mut crate::leanh::LeanObject,
    mut v_a_4403_: *mut crate::leanh::LeanObject,
    mut v_a_4404_: *mut crate::leanh::LeanObject,
    mut v_a_4405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4427_: u8 = 0;
    let mut v_toFunctor_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4434_: u8 = 0;
    let mut v___f_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4451_: u8 = 0;
    let mut v_toFunctor_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4458_: u8 = 0;
    let mut v___f_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadQuotation_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getMCtx_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyMCtx_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalExpr_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4492_: u8 = 0;
    let mut v___x_4493_: u8 = 0;
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4510_: u8 = 0;
    let mut v_cancelTk_x3f_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4512_: u8 = 0;
    let mut v_inheritedTraceOptions_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: u8 = 0;
    let mut v_ref_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751__overap_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802__overap_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4548_: u8 = 0;
    let mut v_id_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4552_: u8 = 0;
    let mut v___x_4553_: u8 = 0;
    let mut v_val_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4563_: u8 = 0;
    let mut v_unused_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: u8 = 0;
    let mut v___x_4576_: u8 = 0;
    let mut v___y_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: u8 = 0;
    let mut v___x_4071__overap_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4594_: u8 = 0;
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4598_: u8 = 0;
    let mut v_a_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4602_: u8 = 0;
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4606_: u8 = 0;
    let mut v_a_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4610_: u8 = 0;
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4614_: u8 = 0;
    let mut v___y_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938__overap_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4630_: u8 = 0;
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4634_: u8 = 0;
    let mut v___x_4635_: u8 = 0;
    let mut v___x_4636_: u8 = 0;
    let mut v___x_3959__overap_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4642_: u8 = 0;
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4646_: u8 = 0;
    let mut v_a_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4650_: u8 = 0;
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4654_: u8 = 0;
    let mut v_a_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4658_: u8 = 0;
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_isSharedCheck_4663_: u8 = 0;
    let mut v_reuseFailAlloc_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4666_: u8 = 0;
    let mut v_unused_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4668_: u8 = 0;
    let mut v_unused_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4672_: u8 = 0;
    let mut v_unused_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4674_: u8 = 0;
    let mut v_unused_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4407_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1,
                );
                v_toApplicative_4408_ = crate::leanh::lean_ctor_get(v___x_4407_, 0);
                v_toFunctor_4409_ = crate::leanh::lean_ctor_get(v_toApplicative_4408_, 0);
                v_toSeq_4410_ = crate::leanh::lean_ctor_get(v_toApplicative_4408_, 2);
                v_toSeqLeft_4411_ = crate::leanh::lean_ctor_get(v_toApplicative_4408_, 3);
                v_toSeqRight_4412_ = crate::leanh::lean_ctor_get(v_toApplicative_4408_, 4);
                v___f_4413_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2;
                v___f_4414_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_4409_, 2);
                v___f_4415_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4415_, 0, v_toFunctor_4409_);
                v___f_4416_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4416_, 0, v_toFunctor_4409_);
                v___x_4417_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4417_, 0, v___f_4415_);
                crate::leanh::lean_ctor_set(v___x_4417_, 1, v___f_4416_);
                crate::leanh::lean_inc(v_toSeqRight_4412_);
                v___f_4418_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4418_, 0, v_toSeqRight_4412_);
                crate::leanh::lean_inc(v_toSeqLeft_4411_);
                v___f_4419_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4419_, 0, v_toSeqLeft_4411_);
                crate::leanh::lean_inc(v_toSeq_4410_);
                v___f_4420_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4420_, 0, v_toSeq_4410_);
                v___x_4421_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4421_, 0, v___x_4417_);
                crate::leanh::lean_ctor_set(v___x_4421_, 1, v___f_4413_);
                crate::leanh::lean_ctor_set(v___x_4421_, 2, v___f_4420_);
                crate::leanh::lean_ctor_set(v___x_4421_, 3, v___f_4419_);
                crate::leanh::lean_ctor_set(v___x_4421_, 4, v___f_4418_);
                v___x_4422_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4422_, 0, v___x_4421_);
                crate::leanh::lean_ctor_set(v___x_4422_, 1, v___f_4414_);
                v___x_4423_ = l_StateRefT_x27_instMonad___redArg(v___x_4422_);
                v_toApplicative_4424_ = crate::leanh::lean_ctor_get(v___x_4423_, 0);
                v_isSharedCheck_4674_ = (!crate::leanh::lean_is_exclusive(v___x_4423_)) as u8;
                if v_isSharedCheck_4674_ == 0 {
                    v_unused_4675_ = crate::leanh::lean_ctor_get(v___x_4423_, 1);
                    crate::leanh::lean_dec(v_unused_4675_);
                    v___x_4426_ = v___x_4423_;
                    v_isShared_4427_ = v_isSharedCheck_4674_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4424_);
                    crate::leanh::lean_dec(v___x_4423_);
                    v___x_4426_ = crate::leanh::lean_box(0);
                    v_isShared_4427_ = v_isSharedCheck_4674_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4428_ = crate::leanh::lean_ctor_get(v_toApplicative_4424_, 0);
                v_toSeq_4429_ = crate::leanh::lean_ctor_get(v_toApplicative_4424_, 2);
                v_toSeqLeft_4430_ = crate::leanh::lean_ctor_get(v_toApplicative_4424_, 3);
                v_toSeqRight_4431_ = crate::leanh::lean_ctor_get(v_toApplicative_4424_, 4);
                v_isSharedCheck_4672_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4424_)) as u8;
                if v_isSharedCheck_4672_ == 0 {
                    v_unused_4673_ = crate::leanh::lean_ctor_get(v_toApplicative_4424_, 1);
                    crate::leanh::lean_dec(v_unused_4673_);
                    v___x_4433_ = v_toApplicative_4424_;
                    v_isShared_4434_ = v_isSharedCheck_4672_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4431_);
                    crate::leanh::lean_inc(v_toSeqLeft_4430_);
                    crate::leanh::lean_inc(v_toSeq_4429_);
                    crate::leanh::lean_inc(v_toFunctor_4428_);
                    crate::leanh::lean_dec(v_toApplicative_4424_);
                    v___x_4433_ = crate::leanh::lean_box(0);
                    v_isShared_4434_ = v_isSharedCheck_4672_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4435_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4;
                v___f_4436_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_4428_);
                v___f_4437_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4437_, 0, v_toFunctor_4428_);
                v___f_4438_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4438_, 0, v_toFunctor_4428_);
                v___x_4439_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4439_, 0, v___f_4437_);
                crate::leanh::lean_ctor_set(v___x_4439_, 1, v___f_4438_);
                v___f_4440_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4440_, 0, v_toSeqRight_4431_);
                v___f_4441_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4441_, 0, v_toSeqLeft_4430_);
                v___f_4442_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4442_, 0, v_toSeq_4429_);
                if v_isShared_4434_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4433_, 4, v___f_4440_);
                    crate::leanh::lean_ctor_set(v___x_4433_, 3, v___f_4441_);
                    crate::leanh::lean_ctor_set(v___x_4433_, 2, v___f_4442_);
                    crate::leanh::lean_ctor_set(v___x_4433_, 1, v___f_4435_);
                    crate::leanh::lean_ctor_set(v___x_4433_, 0, v___x_4439_);
                    v___x_4444_ = v___x_4433_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4671_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 0, v___x_4439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 1, v___f_4435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 2, v___f_4442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 3, v___f_4441_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 4, v___f_4440_);
                    v___x_4444_ = v_reuseFailAlloc_4671_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4427_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4426_, 1, v___f_4436_);
                    crate::leanh::lean_ctor_set(v___x_4426_, 0, v___x_4444_);
                    v___x_4446_ = v___x_4426_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4670_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4444_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4670_, 1, v___f_4436_);
                    v___x_4446_ = v_reuseFailAlloc_4670_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4447_ = l_StateRefT_x27_instMonad___redArg(v___x_4446_);
                v_toApplicative_4448_ = crate::leanh::lean_ctor_get(v___x_4447_, 0);
                v_isSharedCheck_4668_ = (!crate::leanh::lean_is_exclusive(v___x_4447_)) as u8;
                if v_isSharedCheck_4668_ == 0 {
                    v_unused_4669_ = crate::leanh::lean_ctor_get(v___x_4447_, 1);
                    crate::leanh::lean_dec(v_unused_4669_);
                    v___x_4450_ = v___x_4447_;
                    v_isShared_4451_ = v_isSharedCheck_4668_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4448_);
                    crate::leanh::lean_dec(v___x_4447_);
                    v___x_4450_ = crate::leanh::lean_box(0);
                    v_isShared_4451_ = v_isSharedCheck_4668_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4452_ = crate::leanh::lean_ctor_get(v_toApplicative_4448_, 0);
                v_toSeq_4453_ = crate::leanh::lean_ctor_get(v_toApplicative_4448_, 2);
                v_toSeqLeft_4454_ = crate::leanh::lean_ctor_get(v_toApplicative_4448_, 3);
                v_toSeqRight_4455_ = crate::leanh::lean_ctor_get(v_toApplicative_4448_, 4);
                v_isSharedCheck_4666_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4448_)) as u8;
                if v_isSharedCheck_4666_ == 0 {
                    v_unused_4667_ = crate::leanh::lean_ctor_get(v_toApplicative_4448_, 1);
                    crate::leanh::lean_dec(v_unused_4667_);
                    v___x_4457_ = v_toApplicative_4448_;
                    v_isShared_4458_ = v_isSharedCheck_4666_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4455_);
                    crate::leanh::lean_inc(v_toSeqLeft_4454_);
                    crate::leanh::lean_inc(v_toSeq_4453_);
                    crate::leanh::lean_inc(v_toFunctor_4452_);
                    crate::leanh::lean_dec(v_toApplicative_4448_);
                    v___x_4457_ = crate::leanh::lean_box(0);
                    v_isShared_4458_ = v_isSharedCheck_4666_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4459_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6;
                v___f_4460_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7;
                crate::leanh::lean_inc_ref(v_toFunctor_4452_);
                v___f_4461_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4461_, 0, v_toFunctor_4452_);
                v___f_4462_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4462_, 0, v_toFunctor_4452_);
                v___x_4463_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4463_, 0, v___f_4461_);
                crate::leanh::lean_ctor_set(v___x_4463_, 1, v___f_4462_);
                v___f_4464_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4464_, 0, v_toSeqRight_4455_);
                v___f_4465_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4465_, 0, v_toSeqLeft_4454_);
                v___f_4466_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4466_, 0, v_toSeq_4453_);
                if v_isShared_4458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4457_, 4, v___f_4464_);
                    crate::leanh::lean_ctor_set(v___x_4457_, 3, v___f_4465_);
                    crate::leanh::lean_ctor_set(v___x_4457_, 2, v___f_4466_);
                    crate::leanh::lean_ctor_set(v___x_4457_, 1, v___f_4459_);
                    crate::leanh::lean_ctor_set(v___x_4457_, 0, v___x_4463_);
                    v___x_4468_ = v___x_4457_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4665_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 1, v___f_4459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 2, v___f_4466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 3, v___f_4465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 4, v___f_4464_);
                    v___x_4468_ = v_reuseFailAlloc_4665_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4450_, 1, v___f_4460_);
                    crate::leanh::lean_ctor_set(v___x_4450_, 0, v___x_4468_);
                    v___x_4470_ = v___x_4450_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4664_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4664_, 1, v___f_4460_);
                    v___x_4470_ = v_reuseFailAlloc_4664_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4471_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
                v_toMonadQuotation_4472_ = crate::leanh::lean_ctor_get(v___x_4471_, 0);
                v_toMonadRef_4473_ = crate::leanh::lean_ctor_get(v_toMonadQuotation_4472_, 0);
                v___x_4474_ = l_Lean_Meta_instMonadMCtxMetaM;
                v_getMCtx_4475_ = crate::leanh::lean_ctor_get(v___x_4474_, 0);
                v_modifyMCtx_4476_ = crate::leanh::lean_ctor_get(v___x_4474_, 1);
                v___f_4477_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8;
                v___x_4478_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9;
                crate::leanh::lean_inc(v_modifyMCtx_4476_);
                v___f_4479_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4479_, 0, v_modifyMCtx_4476_);
                crate::leanh::lean_closure_set(v___f_4479_, 1, v___x_4478_);
                crate::leanh::lean_inc(v_getMCtx_4475_);
                v___x_4480_ = crate::leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___x_4480_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4480_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4480_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4480_, 3, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4480_, 4, v_getMCtx_4475_);
                v___f_4481_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4481_, 0, v___f_4479_);
                crate::leanh::lean_closure_set(v___f_4481_, 1, v___f_4477_);
                v___x_4482_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instMonadLift___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_4482_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4482_, 1, v___x_4480_);
                v___x_4483_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4483_, 0, v___x_4482_);
                crate::leanh::lean_ctor_set(v___x_4483_, 1, v___f_4481_);
                v___x_4484_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21,
                );
                v___x_4485_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
                crate::leanh::lean_inc_ref(v_toMonadRef_4473_);
                v___x_4486_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4486_, 0, v___x_4484_);
                crate::leanh::lean_ctor_set(v___x_4486_, 1, v_toMonadRef_4473_);
                crate::leanh::lean_ctor_set(v___x_4486_, 2, v___x_4485_);
                v___x_4487_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22,
                );
                v_evalExpr_4488_ = crate::leanh::lean_ctor_get(v_inst_4398_, 0);
                v_expectedType_x3f_4489_ = crate::leanh::lean_ctor_get(v_inst_4398_, 1);
                v_isSharedCheck_4663_ = (!crate::leanh::lean_is_exclusive(v_inst_4398_)) as u8;
                if v_isSharedCheck_4663_ == 0 {
                    v___x_4491_ = v_inst_4398_;
                    v_isShared_4492_ = v_isSharedCheck_4663_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_expectedType_x3f_4489_);
                    crate::leanh::lean_inc(v_evalExpr_4488_);
                    crate::leanh::lean_dec(v_inst_4398_);
                    v___x_4491_ = crate::leanh::lean_box(0);
                    v_isShared_4492_ = v_isSharedCheck_4663_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4493_ = 1;
                v___x_4494_ = crate::leanh::lean_box(0);
                v___x_4495_ = crate::leanh::lean_box((v___x_4493_) as usize);
                v___x_4496_ = crate::leanh::lean_box((v___x_4493_) as usize);
                crate::leanh::lean_inc(v_expectedType_x3f_4489_);
                crate::leanh::lean_inc(v_stx_4399_);
                v___x_4497_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                crate::leanh::lean_closure_set(v___x_4497_, 0, v_stx_4399_);
                crate::leanh::lean_closure_set(v___x_4497_, 1, v_expectedType_x3f_4489_);
                crate::leanh::lean_closure_set(v___x_4497_, 2, v___x_4495_);
                crate::leanh::lean_closure_set(v___x_4497_, 3, v___x_4496_);
                crate::leanh::lean_closure_set(v___x_4497_, 4, v___x_4494_);
                v_fileName_4498_ = crate::leanh::lean_ctor_get(v_a_4404_, 0);
                v_fileMap_4499_ = crate::leanh::lean_ctor_get(v_a_4404_, 1);
                v_options_4500_ = crate::leanh::lean_ctor_get(v_a_4404_, 2);
                v_currRecDepth_4501_ = crate::leanh::lean_ctor_get(v_a_4404_, 3);
                v_maxRecDepth_4502_ = crate::leanh::lean_ctor_get(v_a_4404_, 4);
                v_ref_4503_ = crate::leanh::lean_ctor_get(v_a_4404_, 5);
                v_currNamespace_4504_ = crate::leanh::lean_ctor_get(v_a_4404_, 6);
                v_openDecls_4505_ = crate::leanh::lean_ctor_get(v_a_4404_, 7);
                v_initHeartbeats_4506_ = crate::leanh::lean_ctor_get(v_a_4404_, 8);
                v_maxHeartbeats_4507_ = crate::leanh::lean_ctor_get(v_a_4404_, 9);
                v_quotContext_4508_ = crate::leanh::lean_ctor_get(v_a_4404_, 10);
                v_currMacroScope_4509_ = crate::leanh::lean_ctor_get(v_a_4404_, 11);
                v_diag_4510_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4404_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4511_ = crate::leanh::lean_ctor_get(v_a_4404_, 12);
                v_suppressElabErrors_4512_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4404_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4513_ = crate::leanh::lean_ctor_get(v_a_4404_, 13);
                v___x_4514_ = 1;
                v_ref_4515_ = l_Lean_replaceRef(v_stx_4399_, v_ref_4503_);
                crate::leanh::lean_dec(v_stx_4399_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4513_);
                crate::leanh::lean_inc(v_cancelTk_x3f_4511_);
                crate::leanh::lean_inc(v_currMacroScope_4509_);
                crate::leanh::lean_inc(v_quotContext_4508_);
                crate::leanh::lean_inc(v_maxHeartbeats_4507_);
                crate::leanh::lean_inc(v_initHeartbeats_4506_);
                crate::leanh::lean_inc(v_openDecls_4505_);
                crate::leanh::lean_inc(v_currNamespace_4504_);
                crate::leanh::lean_inc(v_maxRecDepth_4502_);
                crate::leanh::lean_inc(v_currRecDepth_4501_);
                crate::leanh::lean_inc_ref(v_options_4500_);
                crate::leanh::lean_inc_ref(v_fileMap_4499_);
                crate::leanh::lean_inc_ref(v_fileName_4498_);
                v___x_4516_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4516_, 0, v_fileName_4498_);
                crate::leanh::lean_ctor_set(v___x_4516_, 1, v_fileMap_4499_);
                crate::leanh::lean_ctor_set(v___x_4516_, 2, v_options_4500_);
                crate::leanh::lean_ctor_set(v___x_4516_, 3, v_currRecDepth_4501_);
                crate::leanh::lean_ctor_set(v___x_4516_, 4, v_maxRecDepth_4502_);
                crate::leanh::lean_ctor_set(v___x_4516_, 5, v_ref_4515_);
                crate::leanh::lean_ctor_set(v___x_4516_, 6, v_currNamespace_4504_);
                crate::leanh::lean_ctor_set(v___x_4516_, 7, v_openDecls_4505_);
                crate::leanh::lean_ctor_set(v___x_4516_, 8, v_initHeartbeats_4506_);
                crate::leanh::lean_ctor_set(v___x_4516_, 9, v_maxHeartbeats_4507_);
                crate::leanh::lean_ctor_set(v___x_4516_, 10, v_quotContext_4508_);
                crate::leanh::lean_ctor_set(v___x_4516_, 11, v_currMacroScope_4509_);
                crate::leanh::lean_ctor_set(v___x_4516_, 12, v_cancelTk_x3f_4511_);
                crate::leanh::lean_ctor_set(v___x_4516_, 13, v_inheritedTraceOptions_4513_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4516_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_4510_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4516_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4512_,
                );
                v___x_4517_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        crate::leanh::lean_box(0),
                        v___x_4497_,
                        v___x_4514_,
                        v_a_4400_,
                        v_a_4401_,
                        v_a_4402_,
                        v_a_4403_,
                        v___x_4516_,
                        v_a_4405_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4517_) == 0 {
                    v_a_4518_ = crate::leanh::lean_ctor_get(v___x_4517_, 0);
                    crate::leanh::lean_inc(v_a_4518_);
                    crate::leanh::lean_dec_ref_known(v___x_4517_, 1);
                    crate::leanh::lean_inc_ref(v___x_4470_);
                    v___x_3751__overap_4519_ =
                        l_Lean_instantiateMVars___redArg(v___x_4470_, v___x_4483_, v_a_4518_);
                    crate::leanh::lean_inc(v_a_4405_);
                    crate::leanh::lean_inc_ref(v___x_4516_);
                    crate::leanh::lean_inc(v_a_4403_);
                    crate::leanh::lean_inc_ref(v_a_4402_);
                    crate::leanh::lean_inc(v_a_4401_);
                    crate::leanh::lean_inc_ref(v_a_4400_);
                    v___x_4520_ = crate::leanh::lean_apply_7(
                        v___x_3751__overap_4519_,
                        v_a_4400_,
                        v_a_4401_,
                        v_a_4402_,
                        v_a_4403_,
                        v___x_4516_,
                        v_a_4405_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4520_) == 0 {
                        v_a_4521_ = crate::leanh::lean_ctor_get(v___x_4520_, 0);
                        crate::leanh::lean_inc(v_a_4521_);
                        crate::leanh::lean_dec_ref_known(v___x_4520_, 1);
                        v___x_4635_ = l_Lean_Expr_hasSorry(v_a_4521_);
                        if v___x_4635_ == 0 {
                            v___y_4578_ = v_a_4400_;
                            v___y_4579_ = v_a_4401_;
                            v___y_4580_ = v_a_4402_;
                            v___y_4581_ = v_a_4403_;
                            v___y_4582_ = v___x_4516_;
                            v___y_4583_ = v_a_4405_;
                            state = 16;
                            continue;
                        } else {
                            v___x_4636_ = l_Lean_Expr_hasSyntheticSorry(v_a_4521_);
                            if v___x_4636_ == 0 {
                                v___y_4616_ = v_a_4400_;
                                v___y_4617_ = v_a_4401_;
                                v___y_4618_ = v_a_4402_;
                                v___y_4619_ = v_a_4403_;
                                v___y_4620_ = v___x_4516_;
                                v___y_4621_ = v_a_4405_;
                                state = 23;
                                continue;
                            } else {
                                v___x_3959__overap_4637_ =
                                    l_Lean_Elab_throwAbortTerm___redArg(v___x_4487_);
                                crate::leanh::lean_inc(v_a_4405_);
                                crate::leanh::lean_inc_ref(v___x_4516_);
                                crate::leanh::lean_inc(v_a_4403_);
                                crate::leanh::lean_inc_ref(v_a_4402_);
                                crate::leanh::lean_inc(v_a_4401_);
                                crate::leanh::lean_inc_ref(v_a_4400_);
                                v___x_4638_ = crate::leanh::lean_apply_7(
                                    v___x_3959__overap_4637_,
                                    v_a_4400_,
                                    v_a_4401_,
                                    v_a_4402_,
                                    v_a_4403_,
                                    v___x_4516_,
                                    v_a_4405_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_4638_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4638_, 1);
                                    v___y_4616_ = v_a_4400_;
                                    v___y_4617_ = v_a_4401_;
                                    v___y_4618_ = v_a_4402_;
                                    v___y_4619_ = v_a_4403_;
                                    v___y_4620_ = v___x_4516_;
                                    v___y_4621_ = v_a_4405_;
                                    state = 23;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_4521_);
                                    crate::leanh::lean_dec_ref_known(v___x_4516_, 14);
                                    crate::leanh::lean_del_object(v___x_4491_);
                                    crate::leanh::lean_dec(v_expectedType_x3f_4489_);
                                    crate::leanh::lean_dec_ref(v_evalExpr_4488_);
                                    crate::leanh::lean_dec_ref_known(v___x_4486_, 3);
                                    crate::leanh::lean_dec_ref(v___x_4470_);
                                    v_a_4639_ = crate::leanh::lean_ctor_get(v___x_4638_, 0);
                                    v_isSharedCheck_4646_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4638_)) as u8;
                                    if v_isSharedCheck_4646_ == 0 {
                                        v___x_4641_ = v___x_4638_;
                                        v_isShared_4642_ = v_isSharedCheck_4646_;
                                        state = 26;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4639_);
                                        crate::leanh::lean_dec(v___x_4638_);
                                        v___x_4641_ = crate::leanh::lean_box(0);
                                        v_isShared_4642_ = v_isSharedCheck_4646_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_4516_, 14);
                        crate::leanh::lean_del_object(v___x_4491_);
                        crate::leanh::lean_dec(v_expectedType_x3f_4489_);
                        crate::leanh::lean_dec_ref(v_evalExpr_4488_);
                        crate::leanh::lean_dec_ref_known(v___x_4486_, 3);
                        crate::leanh::lean_dec_ref(v___x_4470_);
                        v_a_4647_ = crate::leanh::lean_ctor_get(v___x_4520_, 0);
                        v_isSharedCheck_4654_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4520_)) as u8;
                        if v_isSharedCheck_4654_ == 0 {
                            v___x_4649_ = v___x_4520_;
                            v_isShared_4650_ = v_isSharedCheck_4654_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4647_);
                            crate::leanh::lean_dec(v___x_4520_);
                            v___x_4649_ = crate::leanh::lean_box(0);
                            v_isShared_4650_ = v_isSharedCheck_4654_;
                            state = 28;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_4516_, 14);
                    crate::leanh::lean_del_object(v___x_4491_);
                    crate::leanh::lean_dec(v_expectedType_x3f_4489_);
                    crate::leanh::lean_dec_ref(v_evalExpr_4488_);
                    crate::leanh::lean_dec_ref_known(v___x_4486_, 3);
                    crate::leanh::lean_dec_ref_known(v___x_4483_, 2);
                    crate::leanh::lean_dec_ref(v___x_4470_);
                    v_a_4655_ = crate::leanh::lean_ctor_get(v___x_4517_, 0);
                    v_isSharedCheck_4662_ = (!crate::leanh::lean_is_exclusive(v___x_4517_)) as u8;
                    if v_isSharedCheck_4662_ == 0 {
                        v___x_4657_ = v___x_4517_;
                        v_isShared_4658_ = v_isSharedCheck_4662_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4655_);
                        crate::leanh::lean_dec(v___x_4517_);
                        v___x_4657_ = crate::leanh::lean_box(0);
                        v_isShared_4658_ = v_isSharedCheck_4662_;
                        state = 30;
                        continue;
                    }
                }
            }
            10 => {
                v___x_4530_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24,
                );
                v___x_4531_ = l_Lean_indentExpr(v_a_4521_);
                if v_isShared_4492_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4491_, 7);
                    crate::leanh::lean_ctor_set(v___x_4491_, 1, v___x_4531_);
                    crate::leanh::lean_ctor_set(v___x_4491_, 0, v___x_4530_);
                    v___x_4533_ = v___x_4491_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 1, v___x_4531_);
                    v___x_4533_ = v_reuseFailAlloc_4537_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4534_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4534_, 0, v___x_4533_);
                crate::leanh::lean_ctor_set(v___x_4534_, 1, v___y_4529_);
                v___x_3802__overap_4535_ =
                    l_Lean_throwError___redArg(v___x_4470_, v___x_4486_, v___x_4534_);
                crate::leanh::lean_inc(v___y_4525_);
                crate::leanh::lean_inc(v___y_4526_);
                crate::leanh::lean_inc_ref(v___y_4524_);
                crate::leanh::lean_inc(v___y_4528_);
                crate::leanh::lean_inc_ref(v___y_4527_);
                v___x_4536_ = crate::leanh::lean_apply_7(
                    v___x_3802__overap_4535_,
                    v___y_4527_,
                    v___y_4528_,
                    v___y_4524_,
                    v___y_4526_,
                    v___y_4523_,
                    v___y_4525_,
                    crate::leanh::lean_box(0),
                );
                return v___x_4536_;
            }
            12 => {
                if v___y_4548_ == 0 {
                    if crate::leanh::lean_obj_tag(v___y_4539_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___y_4539_, 2);
                        crate::leanh::lean_dec_ref(v___y_4541_);
                        crate::leanh::lean_dec(v_a_4521_);
                        crate::leanh::lean_del_object(v___x_4491_);
                        crate::leanh::lean_dec(v_expectedType_x3f_4489_);
                        crate::leanh::lean_dec_ref_known(v___x_4486_, 3);
                        crate::leanh::lean_dec_ref(v___x_4470_);
                        return v___y_4542_;
                    } else {
                        v_id_4549_ = crate::leanh::lean_ctor_get(v___y_4539_, 0);
                        v_isSharedCheck_4563_ =
                            (!crate::leanh::lean_is_exclusive(v___y_4539_)) as u8;
                        if v_isSharedCheck_4563_ == 0 {
                            v_unused_4564_ = crate::leanh::lean_ctor_get(v___y_4539_, 1);
                            crate::leanh::lean_dec(v_unused_4564_);
                            v___x_4551_ = v___y_4539_;
                            v_isShared_4552_ = v_isSharedCheck_4563_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_id_4549_);
                            crate::leanh::lean_dec(v___y_4539_);
                            v___x_4551_ = crate::leanh::lean_box(0);
                            v_isShared_4552_ = v_isSharedCheck_4563_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4541_);
                    crate::leanh::lean_dec_ref(v___y_4539_);
                    crate::leanh::lean_dec(v_a_4521_);
                    crate::leanh::lean_del_object(v___x_4491_);
                    crate::leanh::lean_dec(v_expectedType_x3f_4489_);
                    crate::leanh::lean_dec_ref_known(v___x_4486_, 3);
                    crate::leanh::lean_dec_ref(v___x_4470_);
                    return v___y_4542_;
                }
            }
            13 => {
                v___x_4553_ = l_Lean_instBEqInternalExceptionId_beq(v___y_4543_, v_id_4549_);
                crate::leanh::lean_dec(v_id_4549_);
                if v___x_4553_ == 0 {
                    crate::leanh::lean_del_object(v___x_4551_);
                    crate::leanh::lean_dec_ref(v___y_4541_);
                    crate::leanh::lean_dec(v_a_4521_);
                    crate::leanh::lean_del_object(v___x_4491_);
                    crate::leanh::lean_dec(v_expectedType_x3f_4489_);
                    crate::leanh::lean_dec_ref_known(v___x_4486_, 3);
                    crate::leanh::lean_dec_ref(v___x_4470_);
                    return v___y_4542_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_4542_);
                    if crate::leanh::lean_obj_tag(v_expectedType_x3f_4489_) == 1 {
                        v_val_4554_ = crate::leanh::lean_ctor_get(v_expectedType_x3f_4489_, 0);
                        crate::leanh::lean_inc(v_val_4554_);
                        crate::leanh::lean_dec_ref_known(v_expectedType_x3f_4489_, 1);
                        v___x_4555_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26_once
                            ),
                            _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26,
                        );
                        v___x_4556_ = l_Lean_MessageData_ofExpr(v_val_4554_);
                        if v_isShared_4552_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4551_, 7);
                            crate::leanh::lean_ctor_set(v___x_4551_, 1, v___x_4556_);
                            crate::leanh::lean_ctor_set(v___x_4551_, 0, v___x_4555_);
                            v___x_4558_ = v___x_4551_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_4561_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 0, v___x_4555_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 1, v___x_4556_);
                            v___x_4558_ = v_reuseFailAlloc_4561_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4551_);
                        crate::leanh::lean_dec(v_expectedType_x3f_4489_);
                        v___x_4562_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once
                            ),
                            _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30,
                        );
                        v___y_4523_ = v___y_4541_;
                        v___y_4524_ = v___y_4540_;
                        v___y_4525_ = v___y_4544_;
                        v___y_4526_ = v___y_4546_;
                        v___y_4527_ = v___y_4545_;
                        v___y_4528_ = v___y_4547_;
                        v___y_4529_ = v___x_4562_;
                        state = 10;
                        continue;
                    }
                }
            }
            14 => {
                v___x_4559_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                );
                v___x_4560_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4560_, 0, v___x_4558_);
                crate::leanh::lean_ctor_set(v___x_4560_, 1, v___x_4559_);
                v___y_4523_ = v___y_4541_;
                v___y_4524_ = v___y_4540_;
                v___y_4525_ = v___y_4544_;
                v___y_4526_ = v___y_4546_;
                v___y_4527_ = v___y_4545_;
                v___y_4528_ = v___y_4547_;
                v___y_4529_ = v___x_4560_;
                state = 10;
                continue;
            }
            15 => {
                crate::leanh::lean_inc(v___y_4571_);
                crate::leanh::lean_inc_ref(v___y_4570_);
                crate::leanh::lean_inc(v___y_4569_);
                crate::leanh::lean_inc_ref(v___y_4568_);
                crate::leanh::lean_inc(v_a_4521_);
                v___x_4572_ = crate::leanh::lean_apply_6(
                    v_evalExpr_4488_,
                    v_a_4521_,
                    v___y_4568_,
                    v___y_4569_,
                    v___y_4570_,
                    v___y_4571_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4572_) == 0 {
                    crate::leanh::lean_dec_ref(v___y_4570_);
                    crate::leanh::lean_dec(v_a_4521_);
                    crate::leanh::lean_del_object(v___x_4491_);
                    crate::leanh::lean_dec(v_expectedType_x3f_4489_);
                    crate::leanh::lean_dec_ref_known(v___x_4486_, 3);
                    crate::leanh::lean_dec_ref(v___x_4470_);
                    return v___x_4572_;
                } else {
                    v_a_4573_ = crate::leanh::lean_ctor_get(v___x_4572_, 0);
                    crate::leanh::lean_inc(v_a_4573_);
                    v___x_4574_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_4575_ = l_Lean_Exception_isInterrupt(v_a_4573_);
                    if v___x_4575_ == 0 {
                        crate::leanh::lean_inc(v_a_4573_);
                        v___x_4576_ = l_Lean_Exception_isRuntime(v_a_4573_);
                        v___y_4539_ = v_a_4573_;
                        v___y_4540_ = v___y_4568_;
                        v___y_4541_ = v___y_4570_;
                        v___y_4542_ = v___x_4572_;
                        v___y_4543_ = v___x_4574_;
                        v___y_4544_ = v___y_4571_;
                        v___y_4545_ = v___y_4566_;
                        v___y_4546_ = v___y_4569_;
                        v___y_4547_ = v___y_4567_;
                        v___y_4548_ = v___x_4576_;
                        state = 12;
                        continue;
                    } else {
                        v___y_4539_ = v_a_4573_;
                        v___y_4540_ = v___y_4568_;
                        v___y_4541_ = v___y_4570_;
                        v___y_4542_ = v___x_4572_;
                        v___y_4543_ = v___x_4574_;
                        v___y_4544_ = v___y_4571_;
                        v___y_4545_ = v___y_4566_;
                        v___y_4546_ = v___y_4569_;
                        v___y_4547_ = v___y_4567_;
                        v___y_4548_ = v___x_4575_;
                        state = 12;
                        continue;
                    }
                }
            }
            16 => {
                crate::leanh::lean_inc(v_a_4521_);
                v___x_4584_ = l_Lean_Meta_getMVars(
                    v_a_4521_,
                    v___y_4580_,
                    v___y_4581_,
                    v___y_4582_,
                    v___y_4583_,
                );
                if crate::leanh::lean_obj_tag(v___x_4584_) == 0 {
                    v_a_4585_ = crate::leanh::lean_ctor_get(v___x_4584_, 0);
                    crate::leanh::lean_inc(v_a_4585_);
                    crate::leanh::lean_dec_ref_known(v___x_4584_, 1);
                    v___x_4586_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                        v_a_4585_,
                        v___x_4494_,
                        v___y_4578_,
                        v___y_4579_,
                        v___y_4580_,
                        v___y_4581_,
                        v___y_4582_,
                        v___y_4583_,
                    );
                    crate::leanh::lean_dec(v_a_4585_);
                    if crate::leanh::lean_obj_tag(v___x_4586_) == 0 {
                        v_a_4587_ = crate::leanh::lean_ctor_get(v___x_4586_, 0);
                        crate::leanh::lean_inc(v_a_4587_);
                        crate::leanh::lean_dec_ref_known(v___x_4586_, 1);
                        v___x_4588_ = (crate::leanh::lean_unbox(v_a_4587_) as u8);
                        crate::leanh::lean_dec(v_a_4587_);
                        if v___x_4588_ == 0 {
                            v___y_4566_ = v___y_4578_;
                            v___y_4567_ = v___y_4579_;
                            v___y_4568_ = v___y_4580_;
                            v___y_4569_ = v___y_4581_;
                            v___y_4570_ = v___y_4582_;
                            v___y_4571_ = v___y_4583_;
                            state = 15;
                            continue;
                        } else {
                            v___x_4071__overap_4589_ =
                                l_Lean_Elab_throwAbortTerm___redArg(v___x_4487_);
                            crate::leanh::lean_inc(v___y_4583_);
                            crate::leanh::lean_inc_ref(v___y_4582_);
                            crate::leanh::lean_inc(v___y_4581_);
                            crate::leanh::lean_inc_ref(v___y_4580_);
                            crate::leanh::lean_inc(v___y_4579_);
                            crate::leanh::lean_inc_ref(v___y_4578_);
                            v___x_4590_ = crate::leanh::lean_apply_7(
                                v___x_4071__overap_4589_,
                                v___y_4578_,
                                v___y_4579_,
                                v___y_4580_,
                                v___y_4581_,
                                v___y_4582_,
                                v___y_4583_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_4590_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4590_, 1);
                                v___y_4566_ = v___y_4578_;
                                v___y_4567_ = v___y_4579_;
                                v___y_4568_ = v___y_4580_;
                                v___y_4569_ = v___y_4581_;
                                v___y_4570_ = v___y_4582_;
                                v___y_4571_ = v___y_4583_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___y_4582_);
                                crate::leanh::lean_dec(v_a_4521_);
                                crate::leanh::lean_del_object(v___x_4491_);
                                crate::leanh::lean_dec(v_expectedType_x3f_4489_);
                                crate::leanh::lean_dec_ref(v_evalExpr_4488_);
                                crate::leanh::lean_dec_ref_known(v___x_4486_, 3);
                                crate::leanh::lean_dec_ref(v___x_4470_);
                                v_a_4591_ = crate::leanh::lean_ctor_get(v___x_4590_, 0);
                                v_isSharedCheck_4598_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4590_)) as u8;
                                if v_isSharedCheck_4598_ == 0 {
                                    v___x_4593_ = v___x_4590_;
                                    v_isShared_4594_ = v_isSharedCheck_4598_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4591_);
                                    crate::leanh::lean_dec(v___x_4590_);
                                    v___x_4593_ = crate::leanh::lean_box(0);
                                    v_isShared_4594_ = v_isSharedCheck_4598_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_4582_);
                        crate::leanh::lean_dec(v_a_4521_);
                        crate::leanh::lean_del_object(v___x_4491_);
                        crate::leanh::lean_dec(v_expectedType_x3f_4489_);
                        crate::leanh::lean_dec_ref(v_evalExpr_4488_);
                        crate::leanh::lean_dec_ref_known(v___x_4486_, 3);
                        crate::leanh::lean_dec_ref(v___x_4470_);
                        v_a_4599_ = crate::leanh::lean_ctor_get(v___x_4586_, 0);
                        v_isSharedCheck_4606_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4586_)) as u8;
                        if v_isSharedCheck_4606_ == 0 {
                            v___x_4601_ = v___x_4586_;
                            v_isShared_4602_ = v_isSharedCheck_4606_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4599_);
                            crate::leanh::lean_dec(v___x_4586_);
                            v___x_4601_ = crate::leanh::lean_box(0);
                            v_isShared_4602_ = v_isSharedCheck_4606_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4582_);
                    crate::leanh::lean_dec(v_a_4521_);
                    crate::leanh::lean_del_object(v___x_4491_);
                    crate::leanh::lean_dec(v_expectedType_x3f_4489_);
                    crate::leanh::lean_dec_ref(v_evalExpr_4488_);
                    crate::leanh::lean_dec_ref_known(v___x_4486_, 3);
                    crate::leanh::lean_dec_ref(v___x_4470_);
                    v_a_4607_ = crate::leanh::lean_ctor_get(v___x_4584_, 0);
                    v_isSharedCheck_4614_ = (!crate::leanh::lean_is_exclusive(v___x_4584_)) as u8;
                    if v_isSharedCheck_4614_ == 0 {
                        v___x_4609_ = v___x_4584_;
                        v_isShared_4610_ = v_isSharedCheck_4614_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4607_);
                        crate::leanh::lean_dec(v___x_4584_);
                        v___x_4609_ = crate::leanh::lean_box(0);
                        v_isShared_4610_ = v_isSharedCheck_4614_;
                        state = 21;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_4594_ == 0 {
                    v___x_4596_ = v___x_4593_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4591_);
                    v___x_4596_ = v_reuseFailAlloc_4597_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4596_;
            }
            19 => {
                if v_isShared_4602_ == 0 {
                    v___x_4604_ = v___x_4601_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4605_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
                    v___x_4604_ = v_reuseFailAlloc_4605_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4604_;
            }
            21 => {
                if v_isShared_4610_ == 0 {
                    v___x_4612_ = v___x_4609_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
                    v___x_4612_ = v_reuseFailAlloc_4613_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4612_;
            }
            23 => {
                v___x_4622_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32,
                );
                crate::leanh::lean_inc(v_a_4521_);
                v___x_4623_ = l_Lean_indentExpr(v_a_4521_);
                v___x_4624_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4624_, 0, v___x_4622_);
                crate::leanh::lean_ctor_set(v___x_4624_, 1, v___x_4623_);
                crate::leanh::lean_inc_ref(v___x_4486_);
                crate::leanh::lean_inc_ref(v___x_4470_);
                v___x_3938__overap_4625_ =
                    l_Lean_throwError___redArg(v___x_4470_, v___x_4486_, v___x_4624_);
                crate::leanh::lean_inc(v___y_4621_);
                crate::leanh::lean_inc_ref(v___y_4620_);
                crate::leanh::lean_inc(v___y_4619_);
                crate::leanh::lean_inc_ref(v___y_4618_);
                crate::leanh::lean_inc(v___y_4617_);
                crate::leanh::lean_inc_ref(v___y_4616_);
                v___x_4626_ = crate::leanh::lean_apply_7(
                    v___x_3938__overap_4625_,
                    v___y_4616_,
                    v___y_4617_,
                    v___y_4618_,
                    v___y_4619_,
                    v___y_4620_,
                    v___y_4621_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4626_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4626_, 1);
                    v___y_4578_ = v___y_4616_;
                    v___y_4579_ = v___y_4617_;
                    v___y_4580_ = v___y_4618_;
                    v___y_4581_ = v___y_4619_;
                    v___y_4582_ = v___y_4620_;
                    v___y_4583_ = v___y_4621_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_4620_);
                    crate::leanh::lean_dec(v_a_4521_);
                    crate::leanh::lean_del_object(v___x_4491_);
                    crate::leanh::lean_dec(v_expectedType_x3f_4489_);
                    crate::leanh::lean_dec_ref(v_evalExpr_4488_);
                    crate::leanh::lean_dec_ref_known(v___x_4486_, 3);
                    crate::leanh::lean_dec_ref(v___x_4470_);
                    v_a_4627_ = crate::leanh::lean_ctor_get(v___x_4626_, 0);
                    v_isSharedCheck_4634_ = (!crate::leanh::lean_is_exclusive(v___x_4626_)) as u8;
                    if v_isSharedCheck_4634_ == 0 {
                        v___x_4629_ = v___x_4626_;
                        v_isShared_4630_ = v_isSharedCheck_4634_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4627_);
                        crate::leanh::lean_dec(v___x_4626_);
                        v___x_4629_ = crate::leanh::lean_box(0);
                        v_isShared_4630_ = v_isSharedCheck_4634_;
                        state = 24;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_4630_ == 0 {
                    v___x_4632_ = v___x_4629_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4627_);
                    v___x_4632_ = v_reuseFailAlloc_4633_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4632_;
            }
            26 => {
                if v_isShared_4642_ == 0 {
                    v___x_4644_ = v___x_4641_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
                    v___x_4644_ = v_reuseFailAlloc_4645_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4644_;
            }
            28 => {
                if v_isShared_4650_ == 0 {
                    v___x_4652_ = v___x_4649_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4653_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
                    v___x_4652_ = v_reuseFailAlloc_4653_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4652_;
            }
            30 => {
                if v_isShared_4658_ == 0 {
                    v___x_4660_ = v___x_4657_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4661_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
                    v___x_4660_ = v_reuseFailAlloc_4661_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___boxed(
    mut v_inst_4676_: *mut crate::leanh::LeanObject,
    mut v_stx_4677_: *mut crate::leanh::LeanObject,
    mut v_a_4678_: *mut crate::leanh::LeanObject,
    mut v_a_4679_: *mut crate::leanh::LeanObject,
    mut v_a_4680_: *mut crate::leanh::LeanObject,
    mut v_a_4681_: *mut crate::leanh::LeanObject,
    mut v_a_4682_: *mut crate::leanh::LeanObject,
    mut v_a_4683_: *mut crate::leanh::LeanObject,
    mut v_a_4684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4685_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(
        v_inst_4676_,
        v_stx_4677_,
        v_a_4678_,
        v_a_4679_,
        v_a_4680_,
        v_a_4681_,
        v_a_4682_,
        v_a_4683_,
    );
    crate::leanh::lean_dec(v_a_4683_);
    crate::leanh::lean_dec_ref(v_a_4682_);
    crate::leanh::lean_dec(v_a_4681_);
    crate::leanh::lean_dec_ref(v_a_4680_);
    crate::leanh::lean_dec(v_a_4679_);
    crate::leanh::lean_dec_ref(v_a_4678_);
    return v_res_4685_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab(
    mut v_00_u03b1_4686_: *mut crate::leanh::LeanObject,
    mut v_inst_4687_: *mut crate::leanh::LeanObject,
    mut v_stx_4688_: *mut crate::leanh::LeanObject,
    mut v_a_4689_: *mut crate::leanh::LeanObject,
    mut v_a_4690_: *mut crate::leanh::LeanObject,
    mut v_a_4691_: *mut crate::leanh::LeanObject,
    mut v_a_4692_: *mut crate::leanh::LeanObject,
    mut v_a_4693_: *mut crate::leanh::LeanObject,
    mut v_a_4694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4696_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(
        v_inst_4687_,
        v_stx_4688_,
        v_a_4689_,
        v_a_4690_,
        v_a_4691_,
        v_a_4692_,
        v_a_4693_,
        v_a_4694_,
    );
    return v___x_4696_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___boxed(
    mut v_00_u03b1_4697_: *mut crate::leanh::LeanObject,
    mut v_inst_4698_: *mut crate::leanh::LeanObject,
    mut v_stx_4699_: *mut crate::leanh::LeanObject,
    mut v_a_4700_: *mut crate::leanh::LeanObject,
    mut v_a_4701_: *mut crate::leanh::LeanObject,
    mut v_a_4702_: *mut crate::leanh::LeanObject,
    mut v_a_4703_: *mut crate::leanh::LeanObject,
    mut v_a_4704_: *mut crate::leanh::LeanObject,
    mut v_a_4705_: *mut crate::leanh::LeanObject,
    mut v_a_4706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4707_ = l_Lean_Elab_ConfigEval_evalExprWithElab(
        v_00_u03b1_4697_,
        v_inst_4698_,
        v_stx_4699_,
        v_a_4700_,
        v_a_4701_,
        v_a_4702_,
        v_a_4703_,
        v_a_4704_,
        v_a_4705_,
    );
    crate::leanh::lean_dec(v_a_4705_);
    crate::leanh::lean_dec_ref(v_a_4704_);
    crate::leanh::lean_dec(v_a_4703_);
    crate::leanh::lean_dec_ref(v_a_4702_);
    crate::leanh::lean_dec(v_a_4701_);
    crate::leanh::lean_dec_ref(v_a_4700_);
    return v_res_4707_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(
    mut v_inst_4708_: *mut crate::leanh::LeanObject,
    mut v_inst_4709_: *mut crate::leanh::LeanObject,
    mut v_stx_4710_: *mut crate::leanh::LeanObject,
    mut v_a_4711_: *mut crate::leanh::LeanObject,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
    mut v_a_4713_: *mut crate::leanh::LeanObject,
    mut v_a_4714_: *mut crate::leanh::LeanObject,
    mut v_a_4715_: *mut crate::leanh::LeanObject,
    mut v_a_4716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_evalTerm_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4731_: u8 = 0;
    let mut v_cancelTk_x3f_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4733_: u8 = 0;
    let mut v_inheritedTraceOptions_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4741_: u8 = 0;
    let mut v_fst_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4746_: u8 = 0;
    let mut v_a_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4750_: u8 = 0;
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4755_: u8 = 0;
    let mut v_id_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: u8 = 0;
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: u8 = 0;
    let mut v___x_4760_: u8 = 0;
    let mut v_reuseFailAlloc_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalTerm_4718_ = crate::leanh::lean_ctor_get(v_inst_4708_, 0);
                crate::leanh::lean_inc_ref(v_evalTerm_4718_);
                crate::leanh::lean_dec_ref(v_inst_4708_);
                v_fileName_4719_ = crate::leanh::lean_ctor_get(v_a_4715_, 0);
                v_fileMap_4720_ = crate::leanh::lean_ctor_get(v_a_4715_, 1);
                v_options_4721_ = crate::leanh::lean_ctor_get(v_a_4715_, 2);
                v_currRecDepth_4722_ = crate::leanh::lean_ctor_get(v_a_4715_, 3);
                v_maxRecDepth_4723_ = crate::leanh::lean_ctor_get(v_a_4715_, 4);
                v_ref_4724_ = crate::leanh::lean_ctor_get(v_a_4715_, 5);
                v_currNamespace_4725_ = crate::leanh::lean_ctor_get(v_a_4715_, 6);
                v_openDecls_4726_ = crate::leanh::lean_ctor_get(v_a_4715_, 7);
                v_initHeartbeats_4727_ = crate::leanh::lean_ctor_get(v_a_4715_, 8);
                v_maxHeartbeats_4728_ = crate::leanh::lean_ctor_get(v_a_4715_, 9);
                v_quotContext_4729_ = crate::leanh::lean_ctor_get(v_a_4715_, 10);
                v_currMacroScope_4730_ = crate::leanh::lean_ctor_get(v_a_4715_, 11);
                v_diag_4731_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4715_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4732_ = crate::leanh::lean_ctor_get(v_a_4715_, 12);
                v_suppressElabErrors_4733_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4715_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4734_ = crate::leanh::lean_ctor_get(v_a_4715_, 13);
                v_ref_4735_ = l_Lean_replaceRef(v_stx_4710_, v_ref_4724_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4734_);
                crate::leanh::lean_inc(v_cancelTk_x3f_4732_);
                crate::leanh::lean_inc(v_currMacroScope_4730_);
                crate::leanh::lean_inc(v_quotContext_4729_);
                crate::leanh::lean_inc(v_maxHeartbeats_4728_);
                crate::leanh::lean_inc(v_initHeartbeats_4727_);
                crate::leanh::lean_inc(v_openDecls_4726_);
                crate::leanh::lean_inc(v_currNamespace_4725_);
                crate::leanh::lean_inc(v_maxRecDepth_4723_);
                crate::leanh::lean_inc(v_currRecDepth_4722_);
                crate::leanh::lean_inc_ref(v_options_4721_);
                crate::leanh::lean_inc_ref(v_fileMap_4720_);
                crate::leanh::lean_inc_ref(v_fileName_4719_);
                v___x_4736_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4736_, 0, v_fileName_4719_);
                crate::leanh::lean_ctor_set(v___x_4736_, 1, v_fileMap_4720_);
                crate::leanh::lean_ctor_set(v___x_4736_, 2, v_options_4721_);
                crate::leanh::lean_ctor_set(v___x_4736_, 3, v_currRecDepth_4722_);
                crate::leanh::lean_ctor_set(v___x_4736_, 4, v_maxRecDepth_4723_);
                crate::leanh::lean_ctor_set(v___x_4736_, 5, v_ref_4735_);
                crate::leanh::lean_ctor_set(v___x_4736_, 6, v_currNamespace_4725_);
                crate::leanh::lean_ctor_set(v___x_4736_, 7, v_openDecls_4726_);
                crate::leanh::lean_ctor_set(v___x_4736_, 8, v_initHeartbeats_4727_);
                crate::leanh::lean_ctor_set(v___x_4736_, 9, v_maxHeartbeats_4728_);
                crate::leanh::lean_ctor_set(v___x_4736_, 10, v_quotContext_4729_);
                crate::leanh::lean_ctor_set(v___x_4736_, 11, v_currMacroScope_4730_);
                crate::leanh::lean_ctor_set(v___x_4736_, 12, v_cancelTk_x3f_4732_);
                crate::leanh::lean_ctor_set(v___x_4736_, 13, v_inheritedTraceOptions_4734_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4736_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_4731_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4736_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4733_,
                );
                crate::leanh::lean_inc(v_a_4716_);
                crate::leanh::lean_inc_ref(v___x_4736_);
                crate::leanh::lean_inc(v_a_4714_);
                crate::leanh::lean_inc_ref(v_a_4713_);
                crate::leanh::lean_inc(v_a_4712_);
                crate::leanh::lean_inc_ref(v_a_4711_);
                crate::leanh::lean_inc(v_stx_4710_);
                v___x_4737_ = crate::leanh::lean_apply_8(
                    v_evalTerm_4718_,
                    v_stx_4710_,
                    v_a_4711_,
                    v_a_4712_,
                    v_a_4713_,
                    v_a_4714_,
                    v___x_4736_,
                    v_a_4716_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4737_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4736_, 14);
                    crate::leanh::lean_dec(v_stx_4710_);
                    crate::leanh::lean_dec_ref(v_inst_4709_);
                    v_a_4738_ = crate::leanh::lean_ctor_get(v___x_4737_, 0);
                    v_isSharedCheck_4746_ = (!crate::leanh::lean_is_exclusive(v___x_4737_)) as u8;
                    if v_isSharedCheck_4746_ == 0 {
                        v___x_4740_ = v___x_4737_;
                        v_isShared_4741_ = v_isSharedCheck_4746_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4738_);
                        crate::leanh::lean_dec(v___x_4737_);
                        v___x_4740_ = crate::leanh::lean_box(0);
                        v_isShared_4741_ = v_isSharedCheck_4746_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4747_ = crate::leanh::lean_ctor_get(v___x_4737_, 0);
                    v_isSharedCheck_4762_ = (!crate::leanh::lean_is_exclusive(v___x_4737_)) as u8;
                    if v_isSharedCheck_4762_ == 0 {
                        v___x_4749_ = v___x_4737_;
                        v_isShared_4750_ = v_isSharedCheck_4762_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4747_);
                        crate::leanh::lean_dec(v___x_4737_);
                        v___x_4749_ = crate::leanh::lean_box(0);
                        v_isShared_4750_ = v_isSharedCheck_4762_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4742_ = crate::leanh::lean_ctor_get(v_a_4738_, 0);
                crate::leanh::lean_inc(v_fst_4742_);
                crate::leanh::lean_dec(v_a_4738_);
                if v_isShared_4741_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4740_, 0, v_fst_4742_);
                    v___x_4744_ = v___x_4740_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_fst_4742_);
                    v___x_4744_ = v_reuseFailAlloc_4745_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4744_;
            }
            3 => {
                v___x_4751_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                crate::leanh::lean_inc(v_a_4747_);
                if v_isShared_4750_ == 0 {
                    v___x_4753_ = v___x_4749_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4761_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4747_);
                    v___x_4753_ = v_reuseFailAlloc_4761_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4759_ = l_Lean_Exception_isInterrupt(v_a_4747_);
                if v___x_4759_ == 0 {
                    crate::leanh::lean_inc(v_a_4747_);
                    v___x_4760_ = l_Lean_Exception_isRuntime(v_a_4747_);
                    v___y_4755_ = v___x_4760_;
                    state = 5;
                    continue;
                } else {
                    v___y_4755_ = v___x_4759_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_4755_ == 0 {
                    if crate::leanh::lean_obj_tag(v_a_4747_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_a_4747_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4736_, 14);
                        crate::leanh::lean_dec(v_stx_4710_);
                        crate::leanh::lean_dec_ref(v_inst_4709_);
                        return v___x_4753_;
                    } else {
                        v_id_4756_ = crate::leanh::lean_ctor_get(v_a_4747_, 0);
                        crate::leanh::lean_inc(v_id_4756_);
                        crate::leanh::lean_dec_ref_known(v_a_4747_, 2);
                        v___x_4757_ =
                            l_Lean_instBEqInternalExceptionId_beq(v___x_4751_, v_id_4756_);
                        crate::leanh::lean_dec(v_id_4756_);
                        if v___x_4757_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4736_, 14);
                            crate::leanh::lean_dec(v_stx_4710_);
                            crate::leanh::lean_dec_ref(v_inst_4709_);
                            return v___x_4753_;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4753_);
                            v___x_4758_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(
                                v_inst_4709_,
                                v_stx_4710_,
                                v_a_4711_,
                                v_a_4712_,
                                v_a_4713_,
                                v_a_4714_,
                                v___x_4736_,
                                v_a_4716_,
                            );
                            crate::leanh::lean_dec_ref_known(v___x_4736_, 14);
                            return v___x_4758_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4747_);
                    crate::leanh::lean_dec_ref_known(v___x_4736_, 14);
                    crate::leanh::lean_dec(v_stx_4710_);
                    crate::leanh::lean_dec_ref(v_inst_4709_);
                    return v___x_4753_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg___boxed(
    mut v_inst_4763_: *mut crate::leanh::LeanObject,
    mut v_inst_4764_: *mut crate::leanh::LeanObject,
    mut v_stx_4765_: *mut crate::leanh::LeanObject,
    mut v_a_4766_: *mut crate::leanh::LeanObject,
    mut v_a_4767_: *mut crate::leanh::LeanObject,
    mut v_a_4768_: *mut crate::leanh::LeanObject,
    mut v_a_4769_: *mut crate::leanh::LeanObject,
    mut v_a_4770_: *mut crate::leanh::LeanObject,
    mut v_a_4771_: *mut crate::leanh::LeanObject,
    mut v_a_4772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4773_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(
        v_inst_4763_,
        v_inst_4764_,
        v_stx_4765_,
        v_a_4766_,
        v_a_4767_,
        v_a_4768_,
        v_a_4769_,
        v_a_4770_,
        v_a_4771_,
    );
    crate::leanh::lean_dec(v_a_4771_);
    crate::leanh::lean_dec_ref(v_a_4770_);
    crate::leanh::lean_dec(v_a_4769_);
    crate::leanh::lean_dec_ref(v_a_4768_);
    crate::leanh::lean_dec(v_a_4767_);
    crate::leanh::lean_dec_ref(v_a_4766_);
    return v_res_4773_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(
    mut v_00_u03b1_4774_: *mut crate::leanh::LeanObject,
    mut v_inst_4775_: *mut crate::leanh::LeanObject,
    mut v_inst_4776_: *mut crate::leanh::LeanObject,
    mut v_stx_4777_: *mut crate::leanh::LeanObject,
    mut v_a_4778_: *mut crate::leanh::LeanObject,
    mut v_a_4779_: *mut crate::leanh::LeanObject,
    mut v_a_4780_: *mut crate::leanh::LeanObject,
    mut v_a_4781_: *mut crate::leanh::LeanObject,
    mut v_a_4782_: *mut crate::leanh::LeanObject,
    mut v_a_4783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4785_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(
        v_inst_4775_,
        v_inst_4776_,
        v_stx_4777_,
        v_a_4778_,
        v_a_4779_,
        v_a_4780_,
        v_a_4781_,
        v_a_4782_,
        v_a_4783_,
    );
    return v___x_4785_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___boxed(
    mut v_00_u03b1_4786_: *mut crate::leanh::LeanObject,
    mut v_inst_4787_: *mut crate::leanh::LeanObject,
    mut v_inst_4788_: *mut crate::leanh::LeanObject,
    mut v_stx_4789_: *mut crate::leanh::LeanObject,
    mut v_a_4790_: *mut crate::leanh::LeanObject,
    mut v_a_4791_: *mut crate::leanh::LeanObject,
    mut v_a_4792_: *mut crate::leanh::LeanObject,
    mut v_a_4793_: *mut crate::leanh::LeanObject,
    mut v_a_4794_: *mut crate::leanh::LeanObject,
    mut v_a_4795_: *mut crate::leanh::LeanObject,
    mut v_a_4796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4797_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(
        v_00_u03b1_4786_,
        v_inst_4787_,
        v_inst_4788_,
        v_stx_4789_,
        v_a_4790_,
        v_a_4791_,
        v_a_4792_,
        v_a_4793_,
        v_a_4794_,
        v_a_4795_,
    );
    crate::leanh::lean_dec(v_a_4795_);
    crate::leanh::lean_dec_ref(v_a_4794_);
    crate::leanh::lean_dec(v_a_4793_);
    crate::leanh::lean_dec_ref(v_a_4792_);
    crate::leanh::lean_dec(v_a_4791_);
    crate::leanh::lean_dec_ref(v_a_4790_);
    return v_res_4797_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
    mut v_x_4816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: u8 = 0;
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: u8 = 0;
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: u8 = 0;
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: u8 = 0;
    let mut v_t_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4817_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4;
                crate::leanh::lean_inc(v_x_4816_);
                v___x_4818_ = l_Lean_Syntax_isOfKind(v_x_4816_, v___x_4817_);
                if v___x_4818_ == 0 {
                    return v_x_4816_;
                } else {
                    v___x_4819_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4820_ = l_Lean_Syntax_getArg(v_x_4816_, v___x_4819_);
                    v___x_4821_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6;
                    crate::leanh::lean_inc(v___x_4820_);
                    v___x_4822_ = l_Lean_Syntax_isOfKind(v___x_4820_, v___x_4821_);
                    if v___x_4822_ == 0 {
                        crate::leanh::lean_dec(v___x_4820_);
                        return v_x_4816_;
                    } else {
                        v___x_4823_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4824_ = l_Lean_Syntax_getArg(v___x_4820_, v___x_4823_);
                        crate::leanh::lean_dec(v___x_4820_);
                        v___x_4825_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8;
                        crate::leanh::lean_inc(v___x_4824_);
                        v___x_4826_ = l_Lean_Syntax_isOfKind(v___x_4824_, v___x_4825_);
                        if v___x_4826_ == 0 {
                            crate::leanh::lean_dec(v___x_4824_);
                            return v_x_4816_;
                        } else {
                            v___x_4827_ = l_Lean_Syntax_getArg(v___x_4824_, v___x_4819_);
                            crate::leanh::lean_dec(v___x_4824_);
                            v___x_4828_ = crate::leanh::lean_box(0);
                            v___x_4829_ = l_Lean_Syntax_matchesIdent(v___x_4827_, v___x_4828_);
                            crate::leanh::lean_dec(v___x_4827_);
                            if v___x_4829_ == 0 {
                                return v_x_4816_;
                            } else {
                                v_t_4830_ = l_Lean_Syntax_getArg(v_x_4816_, v___x_4823_);
                                crate::leanh::lean_dec(v_x_4816_);
                                v_x_4816_ = v_t_4830_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg(
    mut v_expectedType_x3f_4832_: *mut crate::leanh::LeanObject,
    mut v_f_4833_: *mut crate::leanh::LeanObject,
    mut v_stx_4834_: *mut crate::leanh::LeanObject,
    mut v_a_4835_: *mut crate::leanh::LeanObject,
    mut v_a_4836_: *mut crate::leanh::LeanObject,
    mut v_a_4837_: *mut crate::leanh::LeanObject,
    mut v_a_4838_: *mut crate::leanh::LeanObject,
    mut v_a_4839_: *mut crate::leanh::LeanObject,
    mut v_a_4840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4854_: u8 = 0;
    let mut v_cancelTk_x3f_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4856_: u8 = 0;
    let mut v_inheritedTraceOptions_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4865_: u8 = 0;
    let mut v_snd_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_4869_: u8 = 0;
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: u8 = 0;
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4879_: u8 = 0;
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4883_: u8 = 0;
    let mut v_unused_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4888_: u8 = 0;
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4892_: u8 = 0;
    let mut v_isSharedCheck_4893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4842_ = crate::leanh::lean_ctor_get(v_a_4839_, 0);
                v_fileMap_4843_ = crate::leanh::lean_ctor_get(v_a_4839_, 1);
                v_options_4844_ = crate::leanh::lean_ctor_get(v_a_4839_, 2);
                v_currRecDepth_4845_ = crate::leanh::lean_ctor_get(v_a_4839_, 3);
                v_maxRecDepth_4846_ = crate::leanh::lean_ctor_get(v_a_4839_, 4);
                v_ref_4847_ = crate::leanh::lean_ctor_get(v_a_4839_, 5);
                v_currNamespace_4848_ = crate::leanh::lean_ctor_get(v_a_4839_, 6);
                v_openDecls_4849_ = crate::leanh::lean_ctor_get(v_a_4839_, 7);
                v_initHeartbeats_4850_ = crate::leanh::lean_ctor_get(v_a_4839_, 8);
                v_maxHeartbeats_4851_ = crate::leanh::lean_ctor_get(v_a_4839_, 9);
                v_quotContext_4852_ = crate::leanh::lean_ctor_get(v_a_4839_, 10);
                v_currMacroScope_4853_ = crate::leanh::lean_ctor_get(v_a_4839_, 11);
                v_diag_4854_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4839_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4855_ = crate::leanh::lean_ctor_get(v_a_4839_, 12);
                v_suppressElabErrors_4856_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4839_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4857_ = crate::leanh::lean_ctor_get(v_a_4839_, 13);
                crate::leanh::lean_inc(v_stx_4834_);
                v___x_4858_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_4834_,
                    );
                v_ref_4859_ = l_Lean_replaceRef(v_stx_4834_, v_ref_4847_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4857_);
                crate::leanh::lean_inc(v_cancelTk_x3f_4855_);
                crate::leanh::lean_inc(v_currMacroScope_4853_);
                crate::leanh::lean_inc(v_quotContext_4852_);
                crate::leanh::lean_inc(v_maxHeartbeats_4851_);
                crate::leanh::lean_inc(v_initHeartbeats_4850_);
                crate::leanh::lean_inc(v_openDecls_4849_);
                crate::leanh::lean_inc(v_currNamespace_4848_);
                crate::leanh::lean_inc(v_maxRecDepth_4846_);
                crate::leanh::lean_inc(v_currRecDepth_4845_);
                crate::leanh::lean_inc_ref(v_options_4844_);
                crate::leanh::lean_inc_ref(v_fileMap_4843_);
                crate::leanh::lean_inc_ref(v_fileName_4842_);
                v___x_4860_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4860_, 0, v_fileName_4842_);
                crate::leanh::lean_ctor_set(v___x_4860_, 1, v_fileMap_4843_);
                crate::leanh::lean_ctor_set(v___x_4860_, 2, v_options_4844_);
                crate::leanh::lean_ctor_set(v___x_4860_, 3, v_currRecDepth_4845_);
                crate::leanh::lean_ctor_set(v___x_4860_, 4, v_maxRecDepth_4846_);
                crate::leanh::lean_ctor_set(v___x_4860_, 5, v_ref_4859_);
                crate::leanh::lean_ctor_set(v___x_4860_, 6, v_currNamespace_4848_);
                crate::leanh::lean_ctor_set(v___x_4860_, 7, v_openDecls_4849_);
                crate::leanh::lean_ctor_set(v___x_4860_, 8, v_initHeartbeats_4850_);
                crate::leanh::lean_ctor_set(v___x_4860_, 9, v_maxHeartbeats_4851_);
                crate::leanh::lean_ctor_set(v___x_4860_, 10, v_quotContext_4852_);
                crate::leanh::lean_ctor_set(v___x_4860_, 11, v_currMacroScope_4853_);
                crate::leanh::lean_ctor_set(v___x_4860_, 12, v_cancelTk_x3f_4855_);
                crate::leanh::lean_ctor_set(v___x_4860_, 13, v_inheritedTraceOptions_4857_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4860_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_4854_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4860_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4856_,
                );
                crate::leanh::lean_inc(v_a_4840_);
                crate::leanh::lean_inc(v_a_4838_);
                crate::leanh::lean_inc_ref(v_a_4837_);
                crate::leanh::lean_inc(v_a_4836_);
                crate::leanh::lean_inc_ref(v_a_4835_);
                v___x_4861_ = crate::leanh::lean_apply_8(
                    v_f_4833_,
                    v___x_4858_,
                    v_a_4835_,
                    v_a_4836_,
                    v_a_4837_,
                    v_a_4838_,
                    v___x_4860_,
                    v_a_4840_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4861_) == 0 {
                    v_a_4862_ = crate::leanh::lean_ctor_get(v___x_4861_, 0);
                    v_isSharedCheck_4893_ = (!crate::leanh::lean_is_exclusive(v___x_4861_)) as u8;
                    if v_isSharedCheck_4893_ == 0 {
                        v___x_4864_ = v___x_4861_;
                        v_isShared_4865_ = v_isSharedCheck_4893_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4862_);
                        crate::leanh::lean_dec(v___x_4861_);
                        v___x_4864_ = crate::leanh::lean_box(0);
                        v_isShared_4865_ = v_isSharedCheck_4893_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_4834_);
                    crate::leanh::lean_dec(v_expectedType_x3f_4832_);
                    return v___x_4861_;
                }
            }
            1 => {
                v_snd_4866_ = crate::leanh::lean_ctor_get(v_a_4862_, 1);
                v___x_4867_ = lean_st_ref_get(v_a_4840_);
                v_infoState_4868_ = crate::leanh::lean_ctor_get(v___x_4867_, 7);
                crate::leanh::lean_inc_ref(v_infoState_4868_);
                crate::leanh::lean_dec(v___x_4867_);
                v_enabled_4869_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_4868_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_4868_);
                if v_enabled_4869_ == 0 {
                    crate::leanh::lean_dec(v_stx_4834_);
                    crate::leanh::lean_dec(v_expectedType_x3f_4832_);
                    if v_isShared_4865_ == 0 {
                        v___x_4871_ = v___x_4864_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4862_);
                        v___x_4871_ = v_reuseFailAlloc_4872_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4864_);
                    v___x_4873_ = crate::leanh::lean_box(0);
                    v___x_4874_ = crate::leanh::lean_box(0);
                    v___x_4875_ = 0;
                    crate::leanh::lean_inc(v_snd_4866_);
                    v___x_4876_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_stx_4834_,
                        v_snd_4866_,
                        v_expectedType_x3f_4832_,
                        v___x_4873_,
                        v___x_4874_,
                        v___x_4875_,
                        v___x_4875_,
                        v_a_4835_,
                        v_a_4836_,
                        v_a_4837_,
                        v_a_4838_,
                        v_a_4839_,
                        v_a_4840_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4876_) == 0 {
                        v_isSharedCheck_4883_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4876_)) as u8;
                        if v_isSharedCheck_4883_ == 0 {
                            v_unused_4884_ = crate::leanh::lean_ctor_get(v___x_4876_, 0);
                            crate::leanh::lean_dec(v_unused_4884_);
                            v___x_4878_ = v___x_4876_;
                            v_isShared_4879_ = v_isSharedCheck_4883_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4876_);
                            v___x_4878_ = crate::leanh::lean_box(0);
                            v_isShared_4879_ = v_isSharedCheck_4883_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4862_);
                        v_a_4885_ = crate::leanh::lean_ctor_get(v___x_4876_, 0);
                        v_isSharedCheck_4892_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4876_)) as u8;
                        if v_isSharedCheck_4892_ == 0 {
                            v___x_4887_ = v___x_4876_;
                            v_isShared_4888_ = v_isSharedCheck_4892_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4885_);
                            crate::leanh::lean_dec(v___x_4876_);
                            v___x_4887_ = crate::leanh::lean_box(0);
                            v_isShared_4888_ = v_isSharedCheck_4892_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4871_;
            }
            3 => {
                if v_isShared_4879_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4878_, 0, v_a_4862_);
                    v___x_4881_ = v___x_4878_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4882_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_a_4862_);
                    v___x_4881_ = v_reuseFailAlloc_4882_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4881_;
            }
            5 => {
                if v_isShared_4888_ == 0 {
                    v___x_4890_ = v___x_4887_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4891_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
                    v___x_4890_ = v_reuseFailAlloc_4891_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg___boxed(
    mut v_expectedType_x3f_4894_: *mut crate::leanh::LeanObject,
    mut v_f_4895_: *mut crate::leanh::LeanObject,
    mut v_stx_4896_: *mut crate::leanh::LeanObject,
    mut v_a_4897_: *mut crate::leanh::LeanObject,
    mut v_a_4898_: *mut crate::leanh::LeanObject,
    mut v_a_4899_: *mut crate::leanh::LeanObject,
    mut v_a_4900_: *mut crate::leanh::LeanObject,
    mut v_a_4901_: *mut crate::leanh::LeanObject,
    mut v_a_4902_: *mut crate::leanh::LeanObject,
    mut v_a_4903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4904_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg(
        v_expectedType_x3f_4894_,
        v_f_4895_,
        v_stx_4896_,
        v_a_4897_,
        v_a_4898_,
        v_a_4899_,
        v_a_4900_,
        v_a_4901_,
        v_a_4902_,
    );
    crate::leanh::lean_dec(v_a_4902_);
    crate::leanh::lean_dec_ref(v_a_4901_);
    crate::leanh::lean_dec(v_a_4900_);
    crate::leanh::lean_dec_ref(v_a_4899_);
    crate::leanh::lean_dec(v_a_4898_);
    crate::leanh::lean_dec_ref(v_a_4897_);
    return v_res_4904_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(
    mut v_00_u03b1_4905_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_4906_: *mut crate::leanh::LeanObject,
    mut v_f_4907_: *mut crate::leanh::LeanObject,
    mut v_stx_4908_: *mut crate::leanh::LeanObject,
    mut v_a_4909_: *mut crate::leanh::LeanObject,
    mut v_a_4910_: *mut crate::leanh::LeanObject,
    mut v_a_4911_: *mut crate::leanh::LeanObject,
    mut v_a_4912_: *mut crate::leanh::LeanObject,
    mut v_a_4913_: *mut crate::leanh::LeanObject,
    mut v_a_4914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4928_: u8 = 0;
    let mut v_cancelTk_x3f_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4930_: u8 = 0;
    let mut v_inheritedTraceOptions_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4939_: u8 = 0;
    let mut v_snd_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_4943_: u8 = 0;
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: u8 = 0;
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4953_: u8 = 0;
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4957_: u8 = 0;
    let mut v_unused_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4962_: u8 = 0;
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4966_: u8 = 0;
    let mut v_isSharedCheck_4967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4916_ = crate::leanh::lean_ctor_get(v_a_4913_, 0);
                v_fileMap_4917_ = crate::leanh::lean_ctor_get(v_a_4913_, 1);
                v_options_4918_ = crate::leanh::lean_ctor_get(v_a_4913_, 2);
                v_currRecDepth_4919_ = crate::leanh::lean_ctor_get(v_a_4913_, 3);
                v_maxRecDepth_4920_ = crate::leanh::lean_ctor_get(v_a_4913_, 4);
                v_ref_4921_ = crate::leanh::lean_ctor_get(v_a_4913_, 5);
                v_currNamespace_4922_ = crate::leanh::lean_ctor_get(v_a_4913_, 6);
                v_openDecls_4923_ = crate::leanh::lean_ctor_get(v_a_4913_, 7);
                v_initHeartbeats_4924_ = crate::leanh::lean_ctor_get(v_a_4913_, 8);
                v_maxHeartbeats_4925_ = crate::leanh::lean_ctor_get(v_a_4913_, 9);
                v_quotContext_4926_ = crate::leanh::lean_ctor_get(v_a_4913_, 10);
                v_currMacroScope_4927_ = crate::leanh::lean_ctor_get(v_a_4913_, 11);
                v_diag_4928_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4913_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4929_ = crate::leanh::lean_ctor_get(v_a_4913_, 12);
                v_suppressElabErrors_4930_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4913_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4931_ = crate::leanh::lean_ctor_get(v_a_4913_, 13);
                crate::leanh::lean_inc(v_stx_4908_);
                v___x_4932_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_4908_,
                    );
                v_ref_4933_ = l_Lean_replaceRef(v_stx_4908_, v_ref_4921_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4931_);
                crate::leanh::lean_inc(v_cancelTk_x3f_4929_);
                crate::leanh::lean_inc(v_currMacroScope_4927_);
                crate::leanh::lean_inc(v_quotContext_4926_);
                crate::leanh::lean_inc(v_maxHeartbeats_4925_);
                crate::leanh::lean_inc(v_initHeartbeats_4924_);
                crate::leanh::lean_inc(v_openDecls_4923_);
                crate::leanh::lean_inc(v_currNamespace_4922_);
                crate::leanh::lean_inc(v_maxRecDepth_4920_);
                crate::leanh::lean_inc(v_currRecDepth_4919_);
                crate::leanh::lean_inc_ref(v_options_4918_);
                crate::leanh::lean_inc_ref(v_fileMap_4917_);
                crate::leanh::lean_inc_ref(v_fileName_4916_);
                v___x_4934_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4934_, 0, v_fileName_4916_);
                crate::leanh::lean_ctor_set(v___x_4934_, 1, v_fileMap_4917_);
                crate::leanh::lean_ctor_set(v___x_4934_, 2, v_options_4918_);
                crate::leanh::lean_ctor_set(v___x_4934_, 3, v_currRecDepth_4919_);
                crate::leanh::lean_ctor_set(v___x_4934_, 4, v_maxRecDepth_4920_);
                crate::leanh::lean_ctor_set(v___x_4934_, 5, v_ref_4933_);
                crate::leanh::lean_ctor_set(v___x_4934_, 6, v_currNamespace_4922_);
                crate::leanh::lean_ctor_set(v___x_4934_, 7, v_openDecls_4923_);
                crate::leanh::lean_ctor_set(v___x_4934_, 8, v_initHeartbeats_4924_);
                crate::leanh::lean_ctor_set(v___x_4934_, 9, v_maxHeartbeats_4925_);
                crate::leanh::lean_ctor_set(v___x_4934_, 10, v_quotContext_4926_);
                crate::leanh::lean_ctor_set(v___x_4934_, 11, v_currMacroScope_4927_);
                crate::leanh::lean_ctor_set(v___x_4934_, 12, v_cancelTk_x3f_4929_);
                crate::leanh::lean_ctor_set(v___x_4934_, 13, v_inheritedTraceOptions_4931_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4934_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_4928_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4934_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4930_,
                );
                crate::leanh::lean_inc(v_a_4914_);
                crate::leanh::lean_inc(v_a_4912_);
                crate::leanh::lean_inc_ref(v_a_4911_);
                crate::leanh::lean_inc(v_a_4910_);
                crate::leanh::lean_inc_ref(v_a_4909_);
                v___x_4935_ = crate::leanh::lean_apply_8(
                    v_f_4907_,
                    v___x_4932_,
                    v_a_4909_,
                    v_a_4910_,
                    v_a_4911_,
                    v_a_4912_,
                    v___x_4934_,
                    v_a_4914_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4935_) == 0 {
                    v_a_4936_ = crate::leanh::lean_ctor_get(v___x_4935_, 0);
                    v_isSharedCheck_4967_ = (!crate::leanh::lean_is_exclusive(v___x_4935_)) as u8;
                    if v_isSharedCheck_4967_ == 0 {
                        v___x_4938_ = v___x_4935_;
                        v_isShared_4939_ = v_isSharedCheck_4967_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4936_);
                        crate::leanh::lean_dec(v___x_4935_);
                        v___x_4938_ = crate::leanh::lean_box(0);
                        v_isShared_4939_ = v_isSharedCheck_4967_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_4908_);
                    crate::leanh::lean_dec(v_expectedType_x3f_4906_);
                    return v___x_4935_;
                }
            }
            1 => {
                v_snd_4940_ = crate::leanh::lean_ctor_get(v_a_4936_, 1);
                v___x_4941_ = lean_st_ref_get(v_a_4914_);
                v_infoState_4942_ = crate::leanh::lean_ctor_get(v___x_4941_, 7);
                crate::leanh::lean_inc_ref(v_infoState_4942_);
                crate::leanh::lean_dec(v___x_4941_);
                v_enabled_4943_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_4942_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_4942_);
                if v_enabled_4943_ == 0 {
                    crate::leanh::lean_dec(v_stx_4908_);
                    crate::leanh::lean_dec(v_expectedType_x3f_4906_);
                    if v_isShared_4939_ == 0 {
                        v___x_4945_ = v___x_4938_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4946_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4936_);
                        v___x_4945_ = v_reuseFailAlloc_4946_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4938_);
                    v___x_4947_ = crate::leanh::lean_box(0);
                    v___x_4948_ = crate::leanh::lean_box(0);
                    v___x_4949_ = 0;
                    crate::leanh::lean_inc(v_snd_4940_);
                    v___x_4950_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_stx_4908_,
                        v_snd_4940_,
                        v_expectedType_x3f_4906_,
                        v___x_4947_,
                        v___x_4948_,
                        v___x_4949_,
                        v___x_4949_,
                        v_a_4909_,
                        v_a_4910_,
                        v_a_4911_,
                        v_a_4912_,
                        v_a_4913_,
                        v_a_4914_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4950_) == 0 {
                        v_isSharedCheck_4957_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4950_)) as u8;
                        if v_isSharedCheck_4957_ == 0 {
                            v_unused_4958_ = crate::leanh::lean_ctor_get(v___x_4950_, 0);
                            crate::leanh::lean_dec(v_unused_4958_);
                            v___x_4952_ = v___x_4950_;
                            v_isShared_4953_ = v_isSharedCheck_4957_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4950_);
                            v___x_4952_ = crate::leanh::lean_box(0);
                            v_isShared_4953_ = v_isSharedCheck_4957_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4936_);
                        v_a_4959_ = crate::leanh::lean_ctor_get(v___x_4950_, 0);
                        v_isSharedCheck_4966_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4950_)) as u8;
                        if v_isSharedCheck_4966_ == 0 {
                            v___x_4961_ = v___x_4950_;
                            v_isShared_4962_ = v_isSharedCheck_4966_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4959_);
                            crate::leanh::lean_dec(v___x_4950_);
                            v___x_4961_ = crate::leanh::lean_box(0);
                            v_isShared_4962_ = v_isSharedCheck_4966_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4945_;
            }
            3 => {
                if v_isShared_4953_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4952_, 0, v_a_4936_);
                    v___x_4955_ = v___x_4952_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4956_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4936_);
                    v___x_4955_ = v_reuseFailAlloc_4956_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4955_;
            }
            5 => {
                if v_isShared_4962_ == 0 {
                    v___x_4964_ = v___x_4961_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4965_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
                    v___x_4964_ = v_reuseFailAlloc_4965_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4964_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___boxed(
    mut v_00_u03b1_4968_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_4969_: *mut crate::leanh::LeanObject,
    mut v_f_4970_: *mut crate::leanh::LeanObject,
    mut v_stx_4971_: *mut crate::leanh::LeanObject,
    mut v_a_4972_: *mut crate::leanh::LeanObject,
    mut v_a_4973_: *mut crate::leanh::LeanObject,
    mut v_a_4974_: *mut crate::leanh::LeanObject,
    mut v_a_4975_: *mut crate::leanh::LeanObject,
    mut v_a_4976_: *mut crate::leanh::LeanObject,
    mut v_a_4977_: *mut crate::leanh::LeanObject,
    mut v_a_4978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4979_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(
        v_00_u03b1_4968_,
        v_expectedType_x3f_4969_,
        v_f_4970_,
        v_stx_4971_,
        v_a_4972_,
        v_a_4973_,
        v_a_4974_,
        v_a_4975_,
        v_a_4976_,
        v_a_4977_,
    );
    crate::leanh::lean_dec(v_a_4977_);
    crate::leanh::lean_dec_ref(v_a_4976_);
    crate::leanh::lean_dec(v_a_4975_);
    crate::leanh::lean_dec_ref(v_a_4974_);
    crate::leanh::lean_dec(v_a_4973_);
    crate::leanh::lean_dec_ref(v_a_4972_);
    return v_res_4979_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(
    mut v_inst_4980_: *mut crate::leanh::LeanObject,
    mut v_f_4981_: *mut crate::leanh::LeanObject,
    mut v_stx_4982_: *mut crate::leanh::LeanObject,
    mut v_a_4983_: *mut crate::leanh::LeanObject,
    mut v_a_4984_: *mut crate::leanh::LeanObject,
    mut v_a_4985_: *mut crate::leanh::LeanObject,
    mut v_a_4986_: *mut crate::leanh::LeanObject,
    mut v_a_4987_: *mut crate::leanh::LeanObject,
    mut v_a_4988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toExpr_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4994_: u8 = 0;
    let mut v_fileName_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5007_: u8 = 0;
    let mut v_cancelTk_x3f_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5009_: u8 = 0;
    let mut v_inheritedTraceOptions_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5018_: u8 = 0;
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5021_: u8 = 0;
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: u8 = 0;
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5039_: u8 = 0;
    let mut v_unused_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5044_: u8 = 0;
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5048_: u8 = 0;
    let mut v_reuseFailAlloc_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5050_: u8 = 0;
    let mut v_a_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5054_: u8 = 0;
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5058_: u8 = 0;
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toExpr_4990_ = crate::leanh::lean_ctor_get(v_inst_4980_, 0);
                v_toTypeExpr_4991_ = crate::leanh::lean_ctor_get(v_inst_4980_, 1);
                v_isSharedCheck_5059_ = (!crate::leanh::lean_is_exclusive(v_inst_4980_)) as u8;
                if v_isSharedCheck_5059_ == 0 {
                    v___x_4993_ = v_inst_4980_;
                    v_isShared_4994_ = v_isSharedCheck_5059_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toTypeExpr_4991_);
                    crate::leanh::lean_inc(v_toExpr_4990_);
                    crate::leanh::lean_dec(v_inst_4980_);
                    v___x_4993_ = crate::leanh::lean_box(0);
                    v_isShared_4994_ = v_isSharedCheck_5059_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileName_4995_ = crate::leanh::lean_ctor_get(v_a_4987_, 0);
                v_fileMap_4996_ = crate::leanh::lean_ctor_get(v_a_4987_, 1);
                v_options_4997_ = crate::leanh::lean_ctor_get(v_a_4987_, 2);
                v_currRecDepth_4998_ = crate::leanh::lean_ctor_get(v_a_4987_, 3);
                v_maxRecDepth_4999_ = crate::leanh::lean_ctor_get(v_a_4987_, 4);
                v_ref_5000_ = crate::leanh::lean_ctor_get(v_a_4987_, 5);
                v_currNamespace_5001_ = crate::leanh::lean_ctor_get(v_a_4987_, 6);
                v_openDecls_5002_ = crate::leanh::lean_ctor_get(v_a_4987_, 7);
                v_initHeartbeats_5003_ = crate::leanh::lean_ctor_get(v_a_4987_, 8);
                v_maxHeartbeats_5004_ = crate::leanh::lean_ctor_get(v_a_4987_, 9);
                v_quotContext_5005_ = crate::leanh::lean_ctor_get(v_a_4987_, 10);
                v_currMacroScope_5006_ = crate::leanh::lean_ctor_get(v_a_4987_, 11);
                v_diag_5007_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4987_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5008_ = crate::leanh::lean_ctor_get(v_a_4987_, 12);
                v_suppressElabErrors_5009_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4987_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5010_ = crate::leanh::lean_ctor_get(v_a_4987_, 13);
                crate::leanh::lean_inc(v_stx_4982_);
                v___x_5011_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_4982_,
                    );
                v_ref_5012_ = l_Lean_replaceRef(v_stx_4982_, v_ref_5000_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5010_);
                crate::leanh::lean_inc(v_cancelTk_x3f_5008_);
                crate::leanh::lean_inc(v_currMacroScope_5006_);
                crate::leanh::lean_inc(v_quotContext_5005_);
                crate::leanh::lean_inc(v_maxHeartbeats_5004_);
                crate::leanh::lean_inc(v_initHeartbeats_5003_);
                crate::leanh::lean_inc(v_openDecls_5002_);
                crate::leanh::lean_inc(v_currNamespace_5001_);
                crate::leanh::lean_inc(v_maxRecDepth_4999_);
                crate::leanh::lean_inc(v_currRecDepth_4998_);
                crate::leanh::lean_inc_ref(v_options_4997_);
                crate::leanh::lean_inc_ref(v_fileMap_4996_);
                crate::leanh::lean_inc_ref(v_fileName_4995_);
                v___x_5013_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_5013_, 0, v_fileName_4995_);
                crate::leanh::lean_ctor_set(v___x_5013_, 1, v_fileMap_4996_);
                crate::leanh::lean_ctor_set(v___x_5013_, 2, v_options_4997_);
                crate::leanh::lean_ctor_set(v___x_5013_, 3, v_currRecDepth_4998_);
                crate::leanh::lean_ctor_set(v___x_5013_, 4, v_maxRecDepth_4999_);
                crate::leanh::lean_ctor_set(v___x_5013_, 5, v_ref_5012_);
                crate::leanh::lean_ctor_set(v___x_5013_, 6, v_currNamespace_5001_);
                crate::leanh::lean_ctor_set(v___x_5013_, 7, v_openDecls_5002_);
                crate::leanh::lean_ctor_set(v___x_5013_, 8, v_initHeartbeats_5003_);
                crate::leanh::lean_ctor_set(v___x_5013_, 9, v_maxHeartbeats_5004_);
                crate::leanh::lean_ctor_set(v___x_5013_, 10, v_quotContext_5005_);
                crate::leanh::lean_ctor_set(v___x_5013_, 11, v_currMacroScope_5006_);
                crate::leanh::lean_ctor_set(v___x_5013_, 12, v_cancelTk_x3f_5008_);
                crate::leanh::lean_ctor_set(v___x_5013_, 13, v_inheritedTraceOptions_5010_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5013_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_5007_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5013_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5009_,
                );
                crate::leanh::lean_inc(v_a_4988_);
                crate::leanh::lean_inc(v_a_4986_);
                crate::leanh::lean_inc_ref(v_a_4985_);
                crate::leanh::lean_inc(v_a_4984_);
                crate::leanh::lean_inc_ref(v_a_4983_);
                v___x_5014_ = crate::leanh::lean_apply_8(
                    v_f_4981_,
                    v___x_5011_,
                    v_a_4983_,
                    v_a_4984_,
                    v_a_4985_,
                    v_a_4986_,
                    v___x_5013_,
                    v_a_4988_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5014_) == 0 {
                    v_a_5015_ = crate::leanh::lean_ctor_get(v___x_5014_, 0);
                    v_isSharedCheck_5050_ = (!crate::leanh::lean_is_exclusive(v___x_5014_)) as u8;
                    if v_isSharedCheck_5050_ == 0 {
                        v___x_5017_ = v___x_5014_;
                        v_isShared_5018_ = v_isSharedCheck_5050_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5015_);
                        crate::leanh::lean_dec(v___x_5014_);
                        v___x_5017_ = crate::leanh::lean_box(0);
                        v_isShared_5018_ = v_isSharedCheck_5050_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4993_);
                    crate::leanh::lean_dec_ref(v_toTypeExpr_4991_);
                    crate::leanh::lean_dec_ref(v_toExpr_4990_);
                    crate::leanh::lean_dec(v_stx_4982_);
                    v_a_5051_ = crate::leanh::lean_ctor_get(v___x_5014_, 0);
                    v_isSharedCheck_5058_ = (!crate::leanh::lean_is_exclusive(v___x_5014_)) as u8;
                    if v_isSharedCheck_5058_ == 0 {
                        v___x_5053_ = v___x_5014_;
                        v_isShared_5054_ = v_isSharedCheck_5058_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5051_);
                        crate::leanh::lean_dec(v___x_5014_);
                        v___x_5053_ = crate::leanh::lean_box(0);
                        v_isShared_5054_ = v_isSharedCheck_5058_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5019_ = lean_st_ref_get(v_a_4988_);
                v_infoState_5020_ = crate::leanh::lean_ctor_get(v___x_5019_, 7);
                crate::leanh::lean_inc_ref(v_infoState_5020_);
                crate::leanh::lean_dec(v___x_5019_);
                v_enabled_5021_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_5020_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_5020_);
                crate::leanh::lean_inc(v_a_5015_);
                v___x_5022_ = crate::leanh::lean_apply_1(v_toExpr_4990_, v_a_5015_);
                crate::leanh::lean_inc_ref(v___x_5022_);
                if v_isShared_4994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4993_, 1, v___x_5022_);
                    crate::leanh::lean_ctor_set(v___x_4993_, 0, v_a_5015_);
                    v___x_5024_ = v___x_4993_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5049_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_a_5015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5049_, 1, v___x_5022_);
                    v___x_5024_ = v_reuseFailAlloc_5049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_enabled_5021_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5022_);
                    crate::leanh::lean_dec_ref(v_toTypeExpr_4991_);
                    crate::leanh::lean_dec(v_stx_4982_);
                    if v_isShared_5018_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5017_, 0, v___x_5024_);
                        v___x_5026_ = v___x_5017_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
                        v___x_5026_ = v_reuseFailAlloc_5027_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5017_);
                    v___x_5028_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5028_, 0, v_toTypeExpr_4991_);
                    v___x_5029_ = crate::leanh::lean_box(0);
                    v___x_5030_ = crate::leanh::lean_box(0);
                    v___x_5031_ = 0;
                    v___x_5032_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_stx_4982_,
                        v___x_5022_,
                        v___x_5028_,
                        v___x_5029_,
                        v___x_5030_,
                        v___x_5031_,
                        v___x_5031_,
                        v_a_4983_,
                        v_a_4984_,
                        v_a_4985_,
                        v_a_4986_,
                        v_a_4987_,
                        v_a_4988_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5032_) == 0 {
                        v_isSharedCheck_5039_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5032_)) as u8;
                        if v_isSharedCheck_5039_ == 0 {
                            v_unused_5040_ = crate::leanh::lean_ctor_get(v___x_5032_, 0);
                            crate::leanh::lean_dec(v_unused_5040_);
                            v___x_5034_ = v___x_5032_;
                            v_isShared_5035_ = v_isSharedCheck_5039_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5032_);
                            v___x_5034_ = crate::leanh::lean_box(0);
                            v_isShared_5035_ = v_isSharedCheck_5039_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5024_);
                        v_a_5041_ = crate::leanh::lean_ctor_get(v___x_5032_, 0);
                        v_isSharedCheck_5048_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5032_)) as u8;
                        if v_isSharedCheck_5048_ == 0 {
                            v___x_5043_ = v___x_5032_;
                            v_isShared_5044_ = v_isSharedCheck_5048_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5041_);
                            crate::leanh::lean_dec(v___x_5032_);
                            v___x_5043_ = crate::leanh::lean_box(0);
                            v_isShared_5044_ = v_isSharedCheck_5048_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_5026_;
            }
            5 => {
                if v_isShared_5035_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5034_, 0, v___x_5024_);
                    v___x_5037_ = v___x_5034_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5038_, 0, v___x_5024_);
                    v___x_5037_ = v_reuseFailAlloc_5038_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5037_;
            }
            7 => {
                if v_isShared_5044_ == 0 {
                    v___x_5046_ = v___x_5043_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5047_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5041_);
                    v___x_5046_ = v_reuseFailAlloc_5047_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5046_;
            }
            9 => {
                if v_isShared_5054_ == 0 {
                    v___x_5056_ = v___x_5053_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_a_5051_);
                    v___x_5056_ = v_reuseFailAlloc_5057_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg___boxed(
    mut v_inst_5060_: *mut crate::leanh::LeanObject,
    mut v_f_5061_: *mut crate::leanh::LeanObject,
    mut v_stx_5062_: *mut crate::leanh::LeanObject,
    mut v_a_5063_: *mut crate::leanh::LeanObject,
    mut v_a_5064_: *mut crate::leanh::LeanObject,
    mut v_a_5065_: *mut crate::leanh::LeanObject,
    mut v_a_5066_: *mut crate::leanh::LeanObject,
    mut v_a_5067_: *mut crate::leanh::LeanObject,
    mut v_a_5068_: *mut crate::leanh::LeanObject,
    mut v_a_5069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5070_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(
        v_inst_5060_,
        v_f_5061_,
        v_stx_5062_,
        v_a_5063_,
        v_a_5064_,
        v_a_5065_,
        v_a_5066_,
        v_a_5067_,
        v_a_5068_,
    );
    crate::leanh::lean_dec(v_a_5068_);
    crate::leanh::lean_dec_ref(v_a_5067_);
    crate::leanh::lean_dec(v_a_5066_);
    crate::leanh::lean_dec_ref(v_a_5065_);
    crate::leanh::lean_dec(v_a_5064_);
    crate::leanh::lean_dec_ref(v_a_5063_);
    return v_res_5070_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(
    mut v_00_u03b1_5071_: *mut crate::leanh::LeanObject,
    mut v_inst_5072_: *mut crate::leanh::LeanObject,
    mut v_f_5073_: *mut crate::leanh::LeanObject,
    mut v_stx_5074_: *mut crate::leanh::LeanObject,
    mut v_a_5075_: *mut crate::leanh::LeanObject,
    mut v_a_5076_: *mut crate::leanh::LeanObject,
    mut v_a_5077_: *mut crate::leanh::LeanObject,
    mut v_a_5078_: *mut crate::leanh::LeanObject,
    mut v_a_5079_: *mut crate::leanh::LeanObject,
    mut v_a_5080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toExpr_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5086_: u8 = 0;
    let mut v_fileName_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5099_: u8 = 0;
    let mut v_cancelTk_x3f_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5101_: u8 = 0;
    let mut v_inheritedTraceOptions_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5110_: u8 = 0;
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5113_: u8 = 0;
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: u8 = 0;
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5127_: u8 = 0;
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5131_: u8 = 0;
    let mut v_unused_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5140_: u8 = 0;
    let mut v_reuseFailAlloc_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5142_: u8 = 0;
    let mut v_a_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5150_: u8 = 0;
    let mut v_isSharedCheck_5151_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toExpr_5082_ = crate::leanh::lean_ctor_get(v_inst_5072_, 0);
                v_toTypeExpr_5083_ = crate::leanh::lean_ctor_get(v_inst_5072_, 1);
                v_isSharedCheck_5151_ = (!crate::leanh::lean_is_exclusive(v_inst_5072_)) as u8;
                if v_isSharedCheck_5151_ == 0 {
                    v___x_5085_ = v_inst_5072_;
                    v_isShared_5086_ = v_isSharedCheck_5151_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toTypeExpr_5083_);
                    crate::leanh::lean_inc(v_toExpr_5082_);
                    crate::leanh::lean_dec(v_inst_5072_);
                    v___x_5085_ = crate::leanh::lean_box(0);
                    v_isShared_5086_ = v_isSharedCheck_5151_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileName_5087_ = crate::leanh::lean_ctor_get(v_a_5079_, 0);
                v_fileMap_5088_ = crate::leanh::lean_ctor_get(v_a_5079_, 1);
                v_options_5089_ = crate::leanh::lean_ctor_get(v_a_5079_, 2);
                v_currRecDepth_5090_ = crate::leanh::lean_ctor_get(v_a_5079_, 3);
                v_maxRecDepth_5091_ = crate::leanh::lean_ctor_get(v_a_5079_, 4);
                v_ref_5092_ = crate::leanh::lean_ctor_get(v_a_5079_, 5);
                v_currNamespace_5093_ = crate::leanh::lean_ctor_get(v_a_5079_, 6);
                v_openDecls_5094_ = crate::leanh::lean_ctor_get(v_a_5079_, 7);
                v_initHeartbeats_5095_ = crate::leanh::lean_ctor_get(v_a_5079_, 8);
                v_maxHeartbeats_5096_ = crate::leanh::lean_ctor_get(v_a_5079_, 9);
                v_quotContext_5097_ = crate::leanh::lean_ctor_get(v_a_5079_, 10);
                v_currMacroScope_5098_ = crate::leanh::lean_ctor_get(v_a_5079_, 11);
                v_diag_5099_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5079_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5100_ = crate::leanh::lean_ctor_get(v_a_5079_, 12);
                v_suppressElabErrors_5101_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5079_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5102_ = crate::leanh::lean_ctor_get(v_a_5079_, 13);
                crate::leanh::lean_inc(v_stx_5074_);
                v___x_5103_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_5074_,
                    );
                v_ref_5104_ = l_Lean_replaceRef(v_stx_5074_, v_ref_5092_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5102_);
                crate::leanh::lean_inc(v_cancelTk_x3f_5100_);
                crate::leanh::lean_inc(v_currMacroScope_5098_);
                crate::leanh::lean_inc(v_quotContext_5097_);
                crate::leanh::lean_inc(v_maxHeartbeats_5096_);
                crate::leanh::lean_inc(v_initHeartbeats_5095_);
                crate::leanh::lean_inc(v_openDecls_5094_);
                crate::leanh::lean_inc(v_currNamespace_5093_);
                crate::leanh::lean_inc(v_maxRecDepth_5091_);
                crate::leanh::lean_inc(v_currRecDepth_5090_);
                crate::leanh::lean_inc_ref(v_options_5089_);
                crate::leanh::lean_inc_ref(v_fileMap_5088_);
                crate::leanh::lean_inc_ref(v_fileName_5087_);
                v___x_5105_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_5105_, 0, v_fileName_5087_);
                crate::leanh::lean_ctor_set(v___x_5105_, 1, v_fileMap_5088_);
                crate::leanh::lean_ctor_set(v___x_5105_, 2, v_options_5089_);
                crate::leanh::lean_ctor_set(v___x_5105_, 3, v_currRecDepth_5090_);
                crate::leanh::lean_ctor_set(v___x_5105_, 4, v_maxRecDepth_5091_);
                crate::leanh::lean_ctor_set(v___x_5105_, 5, v_ref_5104_);
                crate::leanh::lean_ctor_set(v___x_5105_, 6, v_currNamespace_5093_);
                crate::leanh::lean_ctor_set(v___x_5105_, 7, v_openDecls_5094_);
                crate::leanh::lean_ctor_set(v___x_5105_, 8, v_initHeartbeats_5095_);
                crate::leanh::lean_ctor_set(v___x_5105_, 9, v_maxHeartbeats_5096_);
                crate::leanh::lean_ctor_set(v___x_5105_, 10, v_quotContext_5097_);
                crate::leanh::lean_ctor_set(v___x_5105_, 11, v_currMacroScope_5098_);
                crate::leanh::lean_ctor_set(v___x_5105_, 12, v_cancelTk_x3f_5100_);
                crate::leanh::lean_ctor_set(v___x_5105_, 13, v_inheritedTraceOptions_5102_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5105_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_5099_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5105_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5101_,
                );
                crate::leanh::lean_inc(v_a_5080_);
                crate::leanh::lean_inc(v_a_5078_);
                crate::leanh::lean_inc_ref(v_a_5077_);
                crate::leanh::lean_inc(v_a_5076_);
                crate::leanh::lean_inc_ref(v_a_5075_);
                v___x_5106_ = crate::leanh::lean_apply_8(
                    v_f_5073_,
                    v___x_5103_,
                    v_a_5075_,
                    v_a_5076_,
                    v_a_5077_,
                    v_a_5078_,
                    v___x_5105_,
                    v_a_5080_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5106_) == 0 {
                    v_a_5107_ = crate::leanh::lean_ctor_get(v___x_5106_, 0);
                    v_isSharedCheck_5142_ = (!crate::leanh::lean_is_exclusive(v___x_5106_)) as u8;
                    if v_isSharedCheck_5142_ == 0 {
                        v___x_5109_ = v___x_5106_;
                        v_isShared_5110_ = v_isSharedCheck_5142_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5107_);
                        crate::leanh::lean_dec(v___x_5106_);
                        v___x_5109_ = crate::leanh::lean_box(0);
                        v_isShared_5110_ = v_isSharedCheck_5142_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5085_);
                    crate::leanh::lean_dec_ref(v_toTypeExpr_5083_);
                    crate::leanh::lean_dec_ref(v_toExpr_5082_);
                    crate::leanh::lean_dec(v_stx_5074_);
                    v_a_5143_ = crate::leanh::lean_ctor_get(v___x_5106_, 0);
                    v_isSharedCheck_5150_ = (!crate::leanh::lean_is_exclusive(v___x_5106_)) as u8;
                    if v_isSharedCheck_5150_ == 0 {
                        v___x_5145_ = v___x_5106_;
                        v_isShared_5146_ = v_isSharedCheck_5150_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5143_);
                        crate::leanh::lean_dec(v___x_5106_);
                        v___x_5145_ = crate::leanh::lean_box(0);
                        v_isShared_5146_ = v_isSharedCheck_5150_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5111_ = lean_st_ref_get(v_a_5080_);
                v_infoState_5112_ = crate::leanh::lean_ctor_get(v___x_5111_, 7);
                crate::leanh::lean_inc_ref(v_infoState_5112_);
                crate::leanh::lean_dec(v___x_5111_);
                v_enabled_5113_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_5112_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_5112_);
                crate::leanh::lean_inc(v_a_5107_);
                v___x_5114_ = crate::leanh::lean_apply_1(v_toExpr_5082_, v_a_5107_);
                crate::leanh::lean_inc_ref(v___x_5114_);
                if v_isShared_5086_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5085_, 1, v___x_5114_);
                    crate::leanh::lean_ctor_set(v___x_5085_, 0, v_a_5107_);
                    v___x_5116_ = v___x_5085_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5141_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5141_, 1, v___x_5114_);
                    v___x_5116_ = v_reuseFailAlloc_5141_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_enabled_5113_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5114_);
                    crate::leanh::lean_dec_ref(v_toTypeExpr_5083_);
                    crate::leanh::lean_dec(v_stx_5074_);
                    if v_isShared_5110_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5109_, 0, v___x_5116_);
                        v___x_5118_ = v___x_5109_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5119_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 0, v___x_5116_);
                        v___x_5118_ = v_reuseFailAlloc_5119_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5109_);
                    v___x_5120_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5120_, 0, v_toTypeExpr_5083_);
                    v___x_5121_ = crate::leanh::lean_box(0);
                    v___x_5122_ = crate::leanh::lean_box(0);
                    v___x_5123_ = 0;
                    v___x_5124_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_stx_5074_,
                        v___x_5114_,
                        v___x_5120_,
                        v___x_5121_,
                        v___x_5122_,
                        v___x_5123_,
                        v___x_5123_,
                        v_a_5075_,
                        v_a_5076_,
                        v_a_5077_,
                        v_a_5078_,
                        v_a_5079_,
                        v_a_5080_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5124_) == 0 {
                        v_isSharedCheck_5131_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5124_)) as u8;
                        if v_isSharedCheck_5131_ == 0 {
                            v_unused_5132_ = crate::leanh::lean_ctor_get(v___x_5124_, 0);
                            crate::leanh::lean_dec(v_unused_5132_);
                            v___x_5126_ = v___x_5124_;
                            v_isShared_5127_ = v_isSharedCheck_5131_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5124_);
                            v___x_5126_ = crate::leanh::lean_box(0);
                            v_isShared_5127_ = v_isSharedCheck_5131_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5116_);
                        v_a_5133_ = crate::leanh::lean_ctor_get(v___x_5124_, 0);
                        v_isSharedCheck_5140_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5124_)) as u8;
                        if v_isSharedCheck_5140_ == 0 {
                            v___x_5135_ = v___x_5124_;
                            v_isShared_5136_ = v_isSharedCheck_5140_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5133_);
                            crate::leanh::lean_dec(v___x_5124_);
                            v___x_5135_ = crate::leanh::lean_box(0);
                            v_isShared_5136_ = v_isSharedCheck_5140_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_5118_;
            }
            5 => {
                if v_isShared_5127_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5126_, 0, v___x_5116_);
                    v___x_5129_ = v___x_5126_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5130_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5130_, 0, v___x_5116_);
                    v___x_5129_ = v_reuseFailAlloc_5130_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5129_;
            }
            7 => {
                if v_isShared_5136_ == 0 {
                    v___x_5138_ = v___x_5135_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5139_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
                    v___x_5138_ = v_reuseFailAlloc_5139_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5138_;
            }
            9 => {
                if v_isShared_5146_ == 0 {
                    v___x_5148_ = v___x_5145_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
                    v___x_5148_ = v_reuseFailAlloc_5149_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___boxed(
    mut v_00_u03b1_5152_: *mut crate::leanh::LeanObject,
    mut v_inst_5153_: *mut crate::leanh::LeanObject,
    mut v_f_5154_: *mut crate::leanh::LeanObject,
    mut v_stx_5155_: *mut crate::leanh::LeanObject,
    mut v_a_5156_: *mut crate::leanh::LeanObject,
    mut v_a_5157_: *mut crate::leanh::LeanObject,
    mut v_a_5158_: *mut crate::leanh::LeanObject,
    mut v_a_5159_: *mut crate::leanh::LeanObject,
    mut v_a_5160_: *mut crate::leanh::LeanObject,
    mut v_a_5161_: *mut crate::leanh::LeanObject,
    mut v_a_5162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5163_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(
        v_00_u03b1_5152_,
        v_inst_5153_,
        v_f_5154_,
        v_stx_5155_,
        v_a_5156_,
        v_a_5157_,
        v_a_5158_,
        v_a_5159_,
        v_a_5160_,
        v_a_5161_,
    );
    crate::leanh::lean_dec(v_a_5161_);
    crate::leanh::lean_dec_ref(v_a_5160_);
    crate::leanh::lean_dec(v_a_5159_);
    crate::leanh::lean_dec_ref(v_a_5158_);
    crate::leanh::lean_dec(v_a_5157_);
    crate::leanh::lean_dec_ref(v_a_5156_);
    return v_res_5163_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(
    mut v_msgData_5164_: *mut crate::leanh::LeanObject,
    mut v___y_5165_: *mut crate::leanh::LeanObject,
    mut v___y_5166_: *mut crate::leanh::LeanObject,
    mut v___y_5167_: *mut crate::leanh::LeanObject,
    mut v___y_5168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5170_ = lean_st_ref_get(v___y_5168_);
    v_env_5171_ = crate::leanh::lean_ctor_get(v___x_5170_, 0);
    crate::leanh::lean_inc_ref(v_env_5171_);
    crate::leanh::lean_dec(v___x_5170_);
    v___x_5172_ = lean_st_ref_get(v___y_5166_);
    v_mctx_5173_ = crate::leanh::lean_ctor_get(v___x_5172_, 0);
    crate::leanh::lean_inc_ref(v_mctx_5173_);
    crate::leanh::lean_dec(v___x_5172_);
    v_lctx_5174_ = crate::leanh::lean_ctor_get(v___y_5165_, 2);
    v_options_5175_ = crate::leanh::lean_ctor_get(v___y_5167_, 2);
    crate::leanh::lean_inc_ref(v_options_5175_);
    crate::leanh::lean_inc_ref(v_lctx_5174_);
    v___x_5176_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5176_, 0, v_env_5171_);
    crate::leanh::lean_ctor_set(v___x_5176_, 1, v_mctx_5173_);
    crate::leanh::lean_ctor_set(v___x_5176_, 2, v_lctx_5174_);
    crate::leanh::lean_ctor_set(v___x_5176_, 3, v_options_5175_);
    v___x_5177_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5177_, 0, v___x_5176_);
    crate::leanh::lean_ctor_set(v___x_5177_, 1, v_msgData_5164_);
    v___x_5178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5178_, 0, v___x_5177_);
    return v___x_5178_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0___boxed(
    mut v_msgData_5179_: *mut crate::leanh::LeanObject,
    mut v___y_5180_: *mut crate::leanh::LeanObject,
    mut v___y_5181_: *mut crate::leanh::LeanObject,
    mut v___y_5182_: *mut crate::leanh::LeanObject,
    mut v___y_5183_: *mut crate::leanh::LeanObject,
    mut v___y_5184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5185_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msgData_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
    crate::leanh::lean_dec(v___y_5183_);
    crate::leanh::lean_dec_ref(v___y_5182_);
    crate::leanh::lean_dec(v___y_5181_);
    crate::leanh::lean_dec_ref(v___y_5180_);
    return v_res_5185_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(
    mut v_msg_5186_: *mut crate::leanh::LeanObject,
    mut v___y_5187_: *mut crate::leanh::LeanObject,
    mut v___y_5188_: *mut crate::leanh::LeanObject,
    mut v___y_5189_: *mut crate::leanh::LeanObject,
    mut v___y_5190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5197_: u8 = 0;
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5192_ = crate::leanh::lean_ctor_get(v___y_5189_, 5);
                v___x_5193_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
                v_a_5194_ = crate::leanh::lean_ctor_get(v___x_5193_, 0);
                v_isSharedCheck_5202_ = (!crate::leanh::lean_is_exclusive(v___x_5193_)) as u8;
                if v_isSharedCheck_5202_ == 0 {
                    v___x_5196_ = v___x_5193_;
                    v_isShared_5197_ = v_isSharedCheck_5202_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5194_);
                    crate::leanh::lean_dec(v___x_5193_);
                    v___x_5196_ = crate::leanh::lean_box(0);
                    v_isShared_5197_ = v_isSharedCheck_5202_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_5192_);
                v___x_5198_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5198_, 0, v_ref_5192_);
                crate::leanh::lean_ctor_set(v___x_5198_, 1, v_a_5194_);
                if v_isShared_5197_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5196_, 1);
                    crate::leanh::lean_ctor_set(v___x_5196_, 0, v___x_5198_);
                    v___x_5200_ = v___x_5196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5201_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5201_, 0, v___x_5198_);
                    v___x_5200_ = v_reuseFailAlloc_5201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg___boxed(
    mut v_msg_5203_: *mut crate::leanh::LeanObject,
    mut v___y_5204_: *mut crate::leanh::LeanObject,
    mut v___y_5205_: *mut crate::leanh::LeanObject,
    mut v___y_5206_: *mut crate::leanh::LeanObject,
    mut v___y_5207_: *mut crate::leanh::LeanObject,
    mut v___y_5208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5209_ =
        l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(
            v_msg_5203_,
            v___y_5204_,
            v___y_5205_,
            v___y_5206_,
            v___y_5207_,
        );
    crate::leanh::lean_dec(v___y_5207_);
    crate::leanh::lean_dec_ref(v___y_5206_);
    crate::leanh::lean_dec(v___y_5205_);
    crate::leanh::lean_dec_ref(v___y_5204_);
    return v_res_5209_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5211_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0;
    v___x_5212_ = l_Lean_stringToMessageData(v___x_5211_);
    return v___x_5212_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
    mut v_f_5213_: *mut crate::leanh::LeanObject,
    mut v_e_5214_: *mut crate::leanh::LeanObject,
    mut v_errMsg_5215_: *mut crate::leanh::LeanObject,
    mut v_a_5216_: *mut crate::leanh::LeanObject,
    mut v_a_5217_: *mut crate::leanh::LeanObject,
    mut v_a_5218_: *mut crate::leanh::LeanObject,
    mut v_a_5219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5227_: u8 = 0;
    let mut v_id_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5231_: u8 = 0;
    let mut v___x_5232_: u8 = 0;
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5240_: u8 = 0;
    let mut v_unused_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: u8 = 0;
    let mut v___x_5246_: u8 = 0;
    let mut v___y_5248_: u8 = 0;
    let mut v_id_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: u8 = 0;
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5258_: u8 = 0;
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5262_: u8 = 0;
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_f_5213_);
                crate::leanh::lean_inc(v_a_5219_);
                crate::leanh::lean_inc_ref(v_a_5218_);
                crate::leanh::lean_inc(v_a_5217_);
                crate::leanh::lean_inc_ref(v_a_5216_);
                crate::leanh::lean_inc_ref(v_e_5214_);
                v___x_5221_ = crate::leanh::lean_apply_6(
                    v_f_5213_,
                    v_e_5214_,
                    v_a_5216_,
                    v_a_5217_,
                    v_a_5218_,
                    v_a_5219_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5221_) == 0 {
                    crate::leanh::lean_dec_ref(v_errMsg_5215_);
                    crate::leanh::lean_dec_ref(v_e_5214_);
                    crate::leanh::lean_dec_ref(v_f_5213_);
                    return v___x_5221_;
                } else {
                    v_a_5222_ = crate::leanh::lean_ctor_get(v___x_5221_, 0);
                    crate::leanh::lean_inc(v_a_5222_);
                    v___x_5223_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
                    v___x_5263_ = l_Lean_Exception_isInterrupt(v_a_5222_);
                    if v___x_5263_ == 0 {
                        crate::leanh::lean_inc(v_a_5222_);
                        v___x_5264_ = l_Lean_Exception_isRuntime(v_a_5222_);
                        v___y_5248_ = v___x_5264_;
                        state = 5;
                        continue;
                    } else {
                        v___y_5248_ = v___x_5263_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5227_ == 0 {
                    if crate::leanh::lean_obj_tag(v___y_5226_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___y_5226_, 2);
                        crate::leanh::lean_dec_ref(v_errMsg_5215_);
                        crate::leanh::lean_dec_ref(v_e_5214_);
                        return v___y_5225_;
                    } else {
                        v_id_5228_ = crate::leanh::lean_ctor_get(v___y_5226_, 0);
                        v_isSharedCheck_5240_ =
                            (!crate::leanh::lean_is_exclusive(v___y_5226_)) as u8;
                        if v_isSharedCheck_5240_ == 0 {
                            v_unused_5241_ = crate::leanh::lean_ctor_get(v___y_5226_, 1);
                            crate::leanh::lean_dec(v_unused_5241_);
                            v___x_5230_ = v___y_5226_;
                            v_isShared_5231_ = v_isSharedCheck_5240_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_id_5228_);
                            crate::leanh::lean_dec(v___y_5226_);
                            v___x_5230_ = crate::leanh::lean_box(0);
                            v_isShared_5231_ = v_isSharedCheck_5240_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_5226_);
                    crate::leanh::lean_dec_ref(v_errMsg_5215_);
                    crate::leanh::lean_dec_ref(v_e_5214_);
                    return v___y_5225_;
                }
            }
            2 => {
                v___x_5232_ = l_Lean_instBEqInternalExceptionId_beq(v___x_5223_, v_id_5228_);
                crate::leanh::lean_dec(v_id_5228_);
                if v___x_5232_ == 0 {
                    crate::leanh::lean_del_object(v___x_5230_);
                    crate::leanh::lean_dec_ref(v_errMsg_5215_);
                    crate::leanh::lean_dec_ref(v_e_5214_);
                    return v___y_5225_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_5225_);
                    v___x_5233_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1,
                    );
                    v___x_5234_ = l_Lean_indentExpr(v_e_5214_);
                    if v_isShared_5231_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5230_, 7);
                        crate::leanh::lean_ctor_set(v___x_5230_, 1, v___x_5234_);
                        crate::leanh::lean_ctor_set(v___x_5230_, 0, v___x_5233_);
                        v___x_5236_ = v___x_5230_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5239_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5233_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5239_, 1, v___x_5234_);
                        v___x_5236_ = v_reuseFailAlloc_5239_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5237_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5237_, 0, v___x_5236_);
                crate::leanh::lean_ctor_set(v___x_5237_, 1, v_errMsg_5215_);
                v___x_5238_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v___x_5237_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_);
                return v___x_5238_;
            }
            4 => {
                v___x_5245_ = l_Lean_Exception_isInterrupt(v_a_5244_);
                if v___x_5245_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_5244_);
                    v___x_5246_ = l_Lean_Exception_isRuntime(v_a_5244_);
                    v___y_5225_ = v___y_5243_;
                    v___y_5226_ = v_a_5244_;
                    v___y_5227_ = v___x_5246_;
                    state = 1;
                    continue;
                } else {
                    v___y_5225_ = v___y_5243_;
                    v___y_5226_ = v_a_5244_;
                    v___y_5227_ = v___x_5245_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v___y_5248_ == 0 {
                    if crate::leanh::lean_obj_tag(v_a_5222_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_a_5222_, 2);
                        crate::leanh::lean_dec_ref(v_errMsg_5215_);
                        crate::leanh::lean_dec_ref(v_e_5214_);
                        crate::leanh::lean_dec_ref(v_f_5213_);
                        return v___x_5221_;
                    } else {
                        v_id_5249_ = crate::leanh::lean_ctor_get(v_a_5222_, 0);
                        crate::leanh::lean_inc(v_id_5249_);
                        crate::leanh::lean_dec_ref_known(v_a_5222_, 2);
                        v___x_5250_ =
                            l_Lean_instBEqInternalExceptionId_beq(v___x_5223_, v_id_5249_);
                        crate::leanh::lean_dec(v_id_5249_);
                        if v___x_5250_ == 0 {
                            crate::leanh::lean_dec_ref(v_errMsg_5215_);
                            crate::leanh::lean_dec_ref(v_e_5214_);
                            crate::leanh::lean_dec_ref(v_f_5213_);
                            return v___x_5221_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_5221_, 1);
                            crate::leanh::lean_inc(v_a_5219_);
                            crate::leanh::lean_inc_ref(v_a_5218_);
                            crate::leanh::lean_inc(v_a_5217_);
                            crate::leanh::lean_inc_ref(v_a_5216_);
                            crate::leanh::lean_inc_ref(v_e_5214_);
                            v___x_5251_ =
                                lean_whnf(v_e_5214_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_);
                            if crate::leanh::lean_obj_tag(v___x_5251_) == 0 {
                                v_a_5252_ = crate::leanh::lean_ctor_get(v___x_5251_, 0);
                                crate::leanh::lean_inc(v_a_5252_);
                                crate::leanh::lean_dec_ref_known(v___x_5251_, 1);
                                crate::leanh::lean_inc(v_a_5219_);
                                crate::leanh::lean_inc_ref(v_a_5218_);
                                crate::leanh::lean_inc(v_a_5217_);
                                crate::leanh::lean_inc_ref(v_a_5216_);
                                v___x_5253_ = crate::leanh::lean_apply_6(
                                    v_f_5213_,
                                    v_a_5252_,
                                    v_a_5216_,
                                    v_a_5217_,
                                    v_a_5218_,
                                    v_a_5219_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_5253_) == 0 {
                                    crate::leanh::lean_dec_ref(v_errMsg_5215_);
                                    crate::leanh::lean_dec_ref(v_e_5214_);
                                    return v___x_5253_;
                                } else {
                                    v_a_5254_ = crate::leanh::lean_ctor_get(v___x_5253_, 0);
                                    crate::leanh::lean_inc(v_a_5254_);
                                    v___y_5243_ = v___x_5253_;
                                    v_a_5244_ = v_a_5254_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_f_5213_);
                                v_a_5255_ = crate::leanh::lean_ctor_get(v___x_5251_, 0);
                                v_isSharedCheck_5262_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5251_)) as u8;
                                if v_isSharedCheck_5262_ == 0 {
                                    v___x_5257_ = v___x_5251_;
                                    v_isShared_5258_ = v_isSharedCheck_5262_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5255_);
                                    crate::leanh::lean_dec(v___x_5251_);
                                    v___x_5257_ = crate::leanh::lean_box(0);
                                    v_isShared_5258_ = v_isSharedCheck_5262_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5222_);
                    crate::leanh::lean_dec_ref(v_errMsg_5215_);
                    crate::leanh::lean_dec_ref(v_e_5214_);
                    crate::leanh::lean_dec_ref(v_f_5213_);
                    return v___x_5221_;
                }
            }
            6 => {
                crate::leanh::lean_inc(v_a_5255_);
                if v_isShared_5258_ == 0 {
                    v___x_5260_ = v___x_5257_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
                    v___x_5260_ = v_reuseFailAlloc_5261_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5243_ = v___x_5260_;
                v_a_5244_ = v_a_5255_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___boxed(
    mut v_f_5265_: *mut crate::leanh::LeanObject,
    mut v_e_5266_: *mut crate::leanh::LeanObject,
    mut v_errMsg_5267_: *mut crate::leanh::LeanObject,
    mut v_a_5268_: *mut crate::leanh::LeanObject,
    mut v_a_5269_: *mut crate::leanh::LeanObject,
    mut v_a_5270_: *mut crate::leanh::LeanObject,
    mut v_a_5271_: *mut crate::leanh::LeanObject,
    mut v_a_5272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5273_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
        v_f_5265_,
        v_e_5266_,
        v_errMsg_5267_,
        v_a_5268_,
        v_a_5269_,
        v_a_5270_,
        v_a_5271_,
    );
    crate::leanh::lean_dec(v_a_5271_);
    crate::leanh::lean_dec_ref(v_a_5270_);
    crate::leanh::lean_dec(v_a_5269_);
    crate::leanh::lean_dec_ref(v_a_5268_);
    return v_res_5273_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(
    mut v_00_u03b1_5274_: *mut crate::leanh::LeanObject,
    mut v_f_5275_: *mut crate::leanh::LeanObject,
    mut v_e_5276_: *mut crate::leanh::LeanObject,
    mut v_errMsg_5277_: *mut crate::leanh::LeanObject,
    mut v_a_5278_: *mut crate::leanh::LeanObject,
    mut v_a_5279_: *mut crate::leanh::LeanObject,
    mut v_a_5280_: *mut crate::leanh::LeanObject,
    mut v_a_5281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5283_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
        v_f_5275_,
        v_e_5276_,
        v_errMsg_5277_,
        v_a_5278_,
        v_a_5279_,
        v_a_5280_,
        v_a_5281_,
    );
    return v___x_5283_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___boxed(
    mut v_00_u03b1_5284_: *mut crate::leanh::LeanObject,
    mut v_f_5285_: *mut crate::leanh::LeanObject,
    mut v_e_5286_: *mut crate::leanh::LeanObject,
    mut v_errMsg_5287_: *mut crate::leanh::LeanObject,
    mut v_a_5288_: *mut crate::leanh::LeanObject,
    mut v_a_5289_: *mut crate::leanh::LeanObject,
    mut v_a_5290_: *mut crate::leanh::LeanObject,
    mut v_a_5291_: *mut crate::leanh::LeanObject,
    mut v_a_5292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5293_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(
        v_00_u03b1_5284_,
        v_f_5285_,
        v_e_5286_,
        v_errMsg_5287_,
        v_a_5288_,
        v_a_5289_,
        v_a_5290_,
        v_a_5291_,
    );
    crate::leanh::lean_dec(v_a_5291_);
    crate::leanh::lean_dec_ref(v_a_5290_);
    crate::leanh::lean_dec(v_a_5289_);
    crate::leanh::lean_dec_ref(v_a_5288_);
    return v_res_5293_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(
    mut v_00_u03b1_5294_: *mut crate::leanh::LeanObject,
    mut v_msg_5295_: *mut crate::leanh::LeanObject,
    mut v___y_5296_: *mut crate::leanh::LeanObject,
    mut v___y_5297_: *mut crate::leanh::LeanObject,
    mut v___y_5298_: *mut crate::leanh::LeanObject,
    mut v___y_5299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5301_ =
        l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(
            v_msg_5295_,
            v___y_5296_,
            v___y_5297_,
            v___y_5298_,
            v___y_5299_,
        );
    return v___x_5301_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___boxed(
    mut v_00_u03b1_5302_: *mut crate::leanh::LeanObject,
    mut v_msg_5303_: *mut crate::leanh::LeanObject,
    mut v___y_5304_: *mut crate::leanh::LeanObject,
    mut v___y_5305_: *mut crate::leanh::LeanObject,
    mut v___y_5306_: *mut crate::leanh::LeanObject,
    mut v___y_5307_: *mut crate::leanh::LeanObject,
    mut v___y_5308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5309_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(
        v_00_u03b1_5302_,
        v_msg_5303_,
        v___y_5304_,
        v___y_5305_,
        v___y_5306_,
        v___y_5307_,
    );
    crate::leanh::lean_dec(v___y_5307_);
    crate::leanh::lean_dec_ref(v___y_5306_);
    crate::leanh::lean_dec(v___y_5305_);
    crate::leanh::lean_dec_ref(v___y_5304_);
    return v_res_5309_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
    mut v_item_5310_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_optionComps_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: u8 = 0;
    v_optionComps_5311_ = crate::leanh::lean_ctor_get(v_item_5310_, 5);
    v___x_5312_ = l_List_isEmpty___redArg(v_optionComps_5311_);
    return v___x_5312_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous___boxed(
    mut v_item_5313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5314_: u8 = 0;
    let mut v_r_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5314_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_5313_);
    crate::leanh::lean_dec_ref(v_item_5313_);
    v_r_5315_ = crate::leanh::lean_box((v_res_5314_) as usize);
    return v_r_5315_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_root(
    mut v_item_5316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_optionComps_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_optionComps_5317_ = crate::leanh::lean_ctor_get(v_item_5316_, 5);
    if crate::leanh::lean_obj_tag(v_optionComps_5317_) == 1 {
        let mut v_head_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_5318_ = crate::leanh::lean_ctor_get(v_optionComps_5317_, 0);
        crate::leanh::lean_inc(v_head_5318_);
        return v_head_5318_;
    } else {
        let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5319_ = crate::leanh::lean_box(0);
        return v___x_5319_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_root___boxed(
    mut v_item_5320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5321_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_5320_);
    crate::leanh::lean_dec_ref(v_item_5320_);
    return v_res_5321_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(
    mut v_item_5322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5323_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_5322_);
    v___x_5324_ = l_Lean_Syntax_getId(v___x_5323_);
    crate::leanh::lean_dec(v___x_5323_);
    if crate::leanh::lean_obj_tag(v___x_5324_) == 1 {
        let mut v_str_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_str_5325_ = crate::leanh::lean_ctor_get(v___x_5324_, 1);
        crate::leanh::lean_inc_ref(v_str_5325_);
        crate::leanh::lean_dec_ref_known(v___x_5324_, 2);
        return v_str_5325_;
    } else {
        let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_5324_);
        v___x_5326_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29;
        return v___x_5326_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_getRootStr___boxed(
    mut v_item_5327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5328_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_5327_);
    crate::leanh::lean_dec_ref(v_item_5327_);
    return v_res_5328_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(
    mut v_item_5329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_prevOptionComps_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_prevOptionComps_5330_ = crate::leanh::lean_ctor_get(v_item_5329_, 6);
    v___x_5331_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5332_ = l_List_get_x3fInternal___redArg(v_prevOptionComps_5330_, v___x_5331_);
    return v___x_5332_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f___boxed(
    mut v_item_5333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5334_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(v_item_5333_);
    crate::leanh::lean_dec_ref(v_item_5333_);
    return v_res_5334_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(
    mut v_item_5335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_prevOptionComps_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_prevOptionComps_5336_ = crate::leanh::lean_ctor_get(v_item_5335_, 6);
    if crate::leanh::lean_obj_tag(v_prevOptionComps_5336_) == 1 {
        let mut v_head_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_5337_ = crate::leanh::lean_ctor_get(v_prevOptionComps_5336_, 0);
        crate::leanh::lean_inc(v_head_5337_);
        return v_head_5337_;
    } else {
        let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5338_ = crate::leanh::lean_box(0);
        return v___x_5338_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_prevRoot___boxed(
    mut v_item_5339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5340_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(v_item_5339_);
    crate::leanh::lean_dec_ref(v_item_5339_);
    return v_res_5340_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(
    mut v_x_5341_: *mut crate::leanh::LeanObject,
    mut v_x_5342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5342_) == 0 {
                    return v_x_5341_;
                } else {
                    v_head_5343_ = crate::leanh::lean_ctor_get(v_x_5342_, 0);
                    crate::leanh::lean_inc(v_head_5343_);
                    v_tail_5344_ = crate::leanh::lean_ctor_get(v_x_5342_, 1);
                    crate::leanh::lean_inc(v_tail_5344_);
                    crate::leanh::lean_dec_ref_known(v_x_5342_, 2);
                    v___x_5345_ = l_Lean_Name_appendCore(v_x_5341_, v_head_5343_);
                    crate::leanh::lean_dec(v_x_5341_);
                    v_x_5341_ = v___x_5345_;
                    v_x_5342_ = v_tail_5344_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__0(
    mut v_a_5347_: *mut crate::leanh::LeanObject,
    mut v_a_5348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5354_: u8 = 0;
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5347_) == 0 {
                    v___x_5349_ = l_List_reverse___redArg(v_a_5348_);
                    return v___x_5349_;
                } else {
                    v_head_5350_ = crate::leanh::lean_ctor_get(v_a_5347_, 0);
                    v_tail_5351_ = crate::leanh::lean_ctor_get(v_a_5347_, 1);
                    v_isSharedCheck_5360_ = (!crate::leanh::lean_is_exclusive(v_a_5347_)) as u8;
                    if v_isSharedCheck_5360_ == 0 {
                        v___x_5353_ = v_a_5347_;
                        v_isShared_5354_ = v_isSharedCheck_5360_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5351_);
                        crate::leanh::lean_inc(v_head_5350_);
                        crate::leanh::lean_dec(v_a_5347_);
                        v___x_5353_ = crate::leanh::lean_box(0);
                        v_isShared_5354_ = v_isSharedCheck_5360_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5355_ = l_Lean_Syntax_getId(v_head_5350_);
                crate::leanh::lean_dec(v_head_5350_);
                if v_isShared_5354_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5353_, 1, v_a_5348_);
                    crate::leanh::lean_ctor_set(v___x_5353_, 0, v___x_5355_);
                    v___x_5357_ = v___x_5353_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5359_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5359_, 1, v_a_5348_);
                    v___x_5357_ = v_reuseFailAlloc_5359_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5347_ = v_tail_5351_;
                v_a_5348_ = v___x_5357_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName(
    mut v_item_5361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_optionComps_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_optionComps_5362_ = crate::leanh::lean_ctor_get(v_item_5361_, 5);
    crate::leanh::lean_inc(v_optionComps_5362_);
    crate::leanh::lean_dec_ref(v_item_5361_);
    v___x_5363_ = crate::leanh::lean_box(0);
    v___x_5364_ = crate::leanh::lean_box(0);
    v___x_5365_ =
        l_List_mapTR_loop___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__0(
            v_optionComps_5362_,
            v___x_5364_,
        );
    v___x_5366_ = l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(
        v___x_5363_,
        v___x_5365_,
    );
    return v___x_5366_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_shift(
    mut v_item_5367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_option_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bool_x3f_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origOptionName_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optionComps_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prevOptionComps_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5380_: u8 = 0;
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5385_: u8 = 0;
    let mut v_unused_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5368_ = crate::leanh::lean_ctor_get(v_item_5367_, 0);
                crate::leanh::lean_inc(v_ref_5368_);
                v_option_5369_ = crate::leanh::lean_ctor_get(v_item_5367_, 1);
                crate::leanh::lean_inc(v_option_5369_);
                v_value_5370_ = crate::leanh::lean_ctor_get(v_item_5367_, 2);
                crate::leanh::lean_inc(v_value_5370_);
                v_bool_x3f_5371_ = crate::leanh::lean_ctor_get(v_item_5367_, 3);
                crate::leanh::lean_inc(v_bool_x3f_5371_);
                v_origOptionName_5372_ = crate::leanh::lean_ctor_get(v_item_5367_, 4);
                crate::leanh::lean_inc(v_origOptionName_5372_);
                v_optionComps_5373_ = crate::leanh::lean_ctor_get(v_item_5367_, 5);
                v_prevOptionComps_5374_ = crate::leanh::lean_ctor_get(v_item_5367_, 6);
                crate::leanh::lean_inc(v_prevOptionComps_5374_);
                if crate::leanh::lean_obj_tag(v_optionComps_5373_) == 0 {
                    v___y_5376_ = v_optionComps_5373_;
                    state = 1;
                    continue;
                } else {
                    v_tail_5393_ = crate::leanh::lean_ctor_get(v_optionComps_5373_, 1);
                    crate::leanh::lean_inc(v_tail_5393_);
                    v___y_5376_ = v_tail_5393_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5377_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_5367_);
                v_isSharedCheck_5385_ = (!crate::leanh::lean_is_exclusive(v_item_5367_)) as u8;
                if v_isSharedCheck_5385_ == 0 {
                    v_unused_5386_ = crate::leanh::lean_ctor_get(v_item_5367_, 6);
                    crate::leanh::lean_dec(v_unused_5386_);
                    v_unused_5387_ = crate::leanh::lean_ctor_get(v_item_5367_, 5);
                    crate::leanh::lean_dec(v_unused_5387_);
                    v_unused_5388_ = crate::leanh::lean_ctor_get(v_item_5367_, 4);
                    crate::leanh::lean_dec(v_unused_5388_);
                    v_unused_5389_ = crate::leanh::lean_ctor_get(v_item_5367_, 3);
                    crate::leanh::lean_dec(v_unused_5389_);
                    v_unused_5390_ = crate::leanh::lean_ctor_get(v_item_5367_, 2);
                    crate::leanh::lean_dec(v_unused_5390_);
                    v_unused_5391_ = crate::leanh::lean_ctor_get(v_item_5367_, 1);
                    crate::leanh::lean_dec(v_unused_5391_);
                    v_unused_5392_ = crate::leanh::lean_ctor_get(v_item_5367_, 0);
                    crate::leanh::lean_dec(v_unused_5392_);
                    v___x_5379_ = v_item_5367_;
                    v_isShared_5380_ = v_isSharedCheck_5385_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_item_5367_);
                    v___x_5379_ = crate::leanh::lean_box(0);
                    v_isShared_5380_ = v_isSharedCheck_5385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5381_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5381_, 0, v___x_5377_);
                crate::leanh::lean_ctor_set(v___x_5381_, 1, v_prevOptionComps_5374_);
                if v_isShared_5380_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5379_, 6, v___x_5381_);
                    crate::leanh::lean_ctor_set(v___x_5379_, 5, v___y_5376_);
                    v___x_5383_ = v___x_5379_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5384_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_ref_5368_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 1, v_option_5369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 2, v_value_5370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 3, v_bool_x3f_5371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 4, v_origOptionName_5372_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 5, v___y_5376_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 6, v___x_5381_);
                    v___x_5383_ = v_reuseFailAlloc_5384_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5383_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5394_ = crate::leanh::lean_box(1);
    v___x_5395_ = l_Lean_MessageData_ofFormat(v___x_5394_);
    return v___x_5395_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5399_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2;
    v___x_5400_ = l_Lean_MessageData_ofFormat(v___x_5399_);
    return v___x_5400_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(
    mut v_x_5401_: *mut crate::leanh::LeanObject,
    mut v_x_5402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5407_: u8 = 0;
    let mut v_before_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5424_: u8 = 0;
    let mut v_unused_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5402_) == 0 {
                    return v_x_5401_;
                } else {
                    v_head_5403_ = crate::leanh::lean_ctor_get(v_x_5402_, 0);
                    v_tail_5404_ = crate::leanh::lean_ctor_get(v_x_5402_, 1);
                    v_isSharedCheck_5426_ = (!crate::leanh::lean_is_exclusive(v_x_5402_)) as u8;
                    if v_isSharedCheck_5426_ == 0 {
                        v___x_5406_ = v_x_5402_;
                        v_isShared_5407_ = v_isSharedCheck_5426_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5404_);
                        crate::leanh::lean_inc(v_head_5403_);
                        crate::leanh::lean_dec(v_x_5402_);
                        v___x_5406_ = crate::leanh::lean_box(0);
                        v_isShared_5407_ = v_isSharedCheck_5426_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_5408_ = crate::leanh::lean_ctor_get(v_head_5403_, 0);
                v_isSharedCheck_5424_ = (!crate::leanh::lean_is_exclusive(v_head_5403_)) as u8;
                if v_isSharedCheck_5424_ == 0 {
                    v_unused_5425_ = crate::leanh::lean_ctor_get(v_head_5403_, 1);
                    crate::leanh::lean_dec(v_unused_5425_);
                    v___x_5410_ = v_head_5403_;
                    v_isShared_5411_ = v_isSharedCheck_5424_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_5408_);
                    crate::leanh::lean_dec(v_head_5403_);
                    v___x_5410_ = crate::leanh::lean_box(0);
                    v_isShared_5411_ = v_isSharedCheck_5424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5412_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_5411_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5410_, 7);
                    crate::leanh::lean_ctor_set(v___x_5410_, 1, v___x_5412_);
                    crate::leanh::lean_ctor_set(v___x_5410_, 0, v_x_5401_);
                    v___x_5414_ = v___x_5410_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5423_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_x_5401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 1, v___x_5412_);
                    v___x_5414_ = v_reuseFailAlloc_5423_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5415_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3);
                if v_isShared_5407_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5406_, 7);
                    crate::leanh::lean_ctor_set(v___x_5406_, 1, v___x_5415_);
                    crate::leanh::lean_ctor_set(v___x_5406_, 0, v___x_5414_);
                    v___x_5417_ = v___x_5406_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5422_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5422_, 0, v___x_5414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5422_, 1, v___x_5415_);
                    v___x_5417_ = v_reuseFailAlloc_5422_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5418_ = l_Lean_MessageData_ofSyntax(v_before_5408_);
                v___x_5419_ = l_Lean_indentD(v___x_5418_);
                v___x_5420_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5420_, 0, v___x_5417_);
                crate::leanh::lean_ctor_set(v___x_5420_, 1, v___x_5419_);
                v_x_5401_ = v___x_5420_;
                v_x_5402_ = v_tail_5404_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(
    mut v_opts_5427_: *mut crate::leanh::LeanObject,
    mut v_opt_5428_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5429_ = crate::leanh::lean_ctor_get(v_opt_5428_, 0);
    v_defValue_5430_ = crate::leanh::lean_ctor_get(v_opt_5428_, 1);
    v_map_5431_ = crate::leanh::lean_ctor_get(v_opts_5427_, 0);
    v___x_5432_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5431_,
            v_name_5429_,
        );
    if crate::leanh::lean_obj_tag(v___x_5432_) == 0 {
        let mut v___x_5433_: u8 = 0;
        v___x_5433_ = (crate::leanh::lean_unbox(v_defValue_5430_) as u8);
        return v___x_5433_;
    } else {
        let mut v_val_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5434_ = crate::leanh::lean_ctor_get(v___x_5432_, 0);
        crate::leanh::lean_inc(v_val_5434_);
        crate::leanh::lean_dec_ref_known(v___x_5432_, 1);
        if crate::leanh::lean_obj_tag(v_val_5434_) == 1 {
            let mut v_v_5435_: u8 = 0;
            v_v_5435_ = crate::leanh::lean_ctor_get_uint8(v_val_5434_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_5434_, 0);
            return v_v_5435_;
        } else {
            let mut v___x_5436_: u8 = 0;
            crate::leanh::lean_dec(v_val_5434_);
            v___x_5436_ = (crate::leanh::lean_unbox(v_defValue_5430_) as u8);
            return v___x_5436_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_opts_5437_: *mut crate::leanh::LeanObject,
    mut v_opt_5438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5439_: u8 = 0;
    let mut v_r_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5439_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_opts_5437_, v_opt_5438_);
    crate::leanh::lean_dec_ref(v_opt_5438_);
    crate::leanh::lean_dec_ref(v_opts_5437_);
    v_r_5440_ = crate::leanh::lean_box((v_res_5439_) as usize);
    return v_r_5440_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5444_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1;
    v___x_5445_ = l_Lean_MessageData_ofFormat(v___x_5444_);
    return v___x_5445_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(
    mut v_msgData_5446_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5447_: *mut crate::leanh::LeanObject,
    mut v___y_5448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: u8 = 0;
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5459_: u8 = 0;
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5471_: u8 = 0;
    let mut v_unused_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5450_ = crate::leanh::lean_ctor_get(v___y_5448_, 2);
                v___x_5451_ = l_Lean_Elab_pp_macroStack;
                v___x_5452_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_options_5450_, v___x_5451_);
                if v___x_5452_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_5447_);
                    v___x_5453_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5453_, 0, v_msgData_5446_);
                    return v___x_5453_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_5447_) == 0 {
                        v___x_5454_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5454_, 0, v_msgData_5446_);
                        return v___x_5454_;
                    } else {
                        v_head_5455_ = crate::leanh::lean_ctor_get(v_macroStack_5447_, 0);
                        crate::leanh::lean_inc(v_head_5455_);
                        v_after_5456_ = crate::leanh::lean_ctor_get(v_head_5455_, 1);
                        v_isSharedCheck_5471_ =
                            (!crate::leanh::lean_is_exclusive(v_head_5455_)) as u8;
                        if v_isSharedCheck_5471_ == 0 {
                            v_unused_5472_ = crate::leanh::lean_ctor_get(v_head_5455_, 0);
                            crate::leanh::lean_dec(v_unused_5472_);
                            v___x_5458_ = v_head_5455_;
                            v_isShared_5459_ = v_isSharedCheck_5471_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_5456_);
                            crate::leanh::lean_dec(v_head_5455_);
                            v___x_5458_ = crate::leanh::lean_box(0);
                            v_isShared_5459_ = v_isSharedCheck_5471_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5460_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_5459_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5458_, 7);
                    crate::leanh::lean_ctor_set(v___x_5458_, 1, v___x_5460_);
                    crate::leanh::lean_ctor_set(v___x_5458_, 0, v_msgData_5446_);
                    v___x_5462_ = v___x_5458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5470_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_msgData_5446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5470_, 1, v___x_5460_);
                    v___x_5462_ = v_reuseFailAlloc_5470_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5463_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2);
                v___x_5464_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5464_, 0, v___x_5462_);
                crate::leanh::lean_ctor_set(v___x_5464_, 1, v___x_5463_);
                v___x_5465_ = l_Lean_MessageData_ofSyntax(v_after_5456_);
                v___x_5466_ = l_Lean_indentD(v___x_5465_);
                v_msgData_5467_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_5467_, 0, v___x_5464_);
                crate::leanh::lean_ctor_set(v_msgData_5467_, 1, v___x_5466_);
                v___x_5468_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(v_msgData_5467_, v_macroStack_5447_);
                v___x_5469_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5469_, 0, v___x_5468_);
                return v___x_5469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msgData_5473_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5474_: *mut crate::leanh::LeanObject,
    mut v___y_5475_: *mut crate::leanh::LeanObject,
    mut v___y_5476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5477_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_5473_, v_macroStack_5474_, v___y_5475_);
    crate::leanh::lean_dec_ref(v___y_5475_);
    return v_res_5477_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(
    mut v_msg_5478_: *mut crate::leanh::LeanObject,
    mut v___y_5479_: *mut crate::leanh::LeanObject,
    mut v___y_5480_: *mut crate::leanh::LeanObject,
    mut v___y_5481_: *mut crate::leanh::LeanObject,
    mut v___y_5482_: *mut crate::leanh::LeanObject,
    mut v___y_5483_: *mut crate::leanh::LeanObject,
    mut v___y_5484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5495_: u8 = 0;
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5486_ = crate::leanh::lean_ctor_get(v___y_5483_, 5);
                v___x_5487_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_5478_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_);
                v_a_5488_ = crate::leanh::lean_ctor_get(v___x_5487_, 0);
                crate::leanh::lean_inc(v_a_5488_);
                crate::leanh::lean_dec_ref(v___x_5487_);
                v_macroStack_5489_ = crate::leanh::lean_ctor_get(v___y_5479_, 1);
                v___x_5490_ = l_Lean_Elab_getBetterRef(v_ref_5486_, v_macroStack_5489_);
                crate::leanh::lean_inc(v_macroStack_5489_);
                v___x_5491_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_a_5488_, v_macroStack_5489_, v___y_5483_);
                v_a_5492_ = crate::leanh::lean_ctor_get(v___x_5491_, 0);
                v_isSharedCheck_5500_ = (!crate::leanh::lean_is_exclusive(v___x_5491_)) as u8;
                if v_isSharedCheck_5500_ == 0 {
                    v___x_5494_ = v___x_5491_;
                    v_isShared_5495_ = v_isSharedCheck_5500_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5492_);
                    crate::leanh::lean_dec(v___x_5491_);
                    v___x_5494_ = crate::leanh::lean_box(0);
                    v_isShared_5495_ = v_isSharedCheck_5500_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5496_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5496_, 0, v___x_5490_);
                crate::leanh::lean_ctor_set(v___x_5496_, 1, v_a_5492_);
                if v_isShared_5495_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5494_, 1);
                    crate::leanh::lean_ctor_set(v___x_5494_, 0, v___x_5496_);
                    v___x_5498_ = v___x_5494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5499_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5499_, 0, v___x_5496_);
                    v___x_5498_ = v_reuseFailAlloc_5499_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5498_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg___boxed(
    mut v_msg_5501_: *mut crate::leanh::LeanObject,
    mut v___y_5502_: *mut crate::leanh::LeanObject,
    mut v___y_5503_: *mut crate::leanh::LeanObject,
    mut v___y_5504_: *mut crate::leanh::LeanObject,
    mut v___y_5505_: *mut crate::leanh::LeanObject,
    mut v___y_5506_: *mut crate::leanh::LeanObject,
    mut v___y_5507_: *mut crate::leanh::LeanObject,
    mut v___y_5508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5509_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_);
    crate::leanh::lean_dec(v___y_5507_);
    crate::leanh::lean_dec_ref(v___y_5506_);
    crate::leanh::lean_dec(v___y_5505_);
    crate::leanh::lean_dec_ref(v___y_5504_);
    crate::leanh::lean_dec(v___y_5503_);
    crate::leanh::lean_dec_ref(v___y_5502_);
    return v_res_5509_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(
    mut v_ref_5510_: *mut crate::leanh::LeanObject,
    mut v_msg_5511_: *mut crate::leanh::LeanObject,
    mut v___y_5512_: *mut crate::leanh::LeanObject,
    mut v___y_5513_: *mut crate::leanh::LeanObject,
    mut v___y_5514_: *mut crate::leanh::LeanObject,
    mut v___y_5515_: *mut crate::leanh::LeanObject,
    mut v___y_5516_: *mut crate::leanh::LeanObject,
    mut v___y_5517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5531_: u8 = 0;
    let mut v_cancelTk_x3f_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5533_: u8 = 0;
    let mut v_inheritedTraceOptions_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5519_ = crate::leanh::lean_ctor_get(v___y_5516_, 0);
    v_fileMap_5520_ = crate::leanh::lean_ctor_get(v___y_5516_, 1);
    v_options_5521_ = crate::leanh::lean_ctor_get(v___y_5516_, 2);
    v_currRecDepth_5522_ = crate::leanh::lean_ctor_get(v___y_5516_, 3);
    v_maxRecDepth_5523_ = crate::leanh::lean_ctor_get(v___y_5516_, 4);
    v_ref_5524_ = crate::leanh::lean_ctor_get(v___y_5516_, 5);
    v_currNamespace_5525_ = crate::leanh::lean_ctor_get(v___y_5516_, 6);
    v_openDecls_5526_ = crate::leanh::lean_ctor_get(v___y_5516_, 7);
    v_initHeartbeats_5527_ = crate::leanh::lean_ctor_get(v___y_5516_, 8);
    v_maxHeartbeats_5528_ = crate::leanh::lean_ctor_get(v___y_5516_, 9);
    v_quotContext_5529_ = crate::leanh::lean_ctor_get(v___y_5516_, 10);
    v_currMacroScope_5530_ = crate::leanh::lean_ctor_get(v___y_5516_, 11);
    v_diag_5531_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5516_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5532_ = crate::leanh::lean_ctor_get(v___y_5516_, 12);
    v_suppressElabErrors_5533_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5516_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5534_ = crate::leanh::lean_ctor_get(v___y_5516_, 13);
    v_ref_5535_ = l_Lean_replaceRef(v_ref_5510_, v_ref_5524_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5534_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5532_);
    crate::leanh::lean_inc(v_currMacroScope_5530_);
    crate::leanh::lean_inc(v_quotContext_5529_);
    crate::leanh::lean_inc(v_maxHeartbeats_5528_);
    crate::leanh::lean_inc(v_initHeartbeats_5527_);
    crate::leanh::lean_inc(v_openDecls_5526_);
    crate::leanh::lean_inc(v_currNamespace_5525_);
    crate::leanh::lean_inc(v_maxRecDepth_5523_);
    crate::leanh::lean_inc(v_currRecDepth_5522_);
    crate::leanh::lean_inc_ref(v_options_5521_);
    crate::leanh::lean_inc_ref(v_fileMap_5520_);
    crate::leanh::lean_inc_ref(v_fileName_5519_);
    v___x_5536_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5536_, 0, v_fileName_5519_);
    crate::leanh::lean_ctor_set(v___x_5536_, 1, v_fileMap_5520_);
    crate::leanh::lean_ctor_set(v___x_5536_, 2, v_options_5521_);
    crate::leanh::lean_ctor_set(v___x_5536_, 3, v_currRecDepth_5522_);
    crate::leanh::lean_ctor_set(v___x_5536_, 4, v_maxRecDepth_5523_);
    crate::leanh::lean_ctor_set(v___x_5536_, 5, v_ref_5535_);
    crate::leanh::lean_ctor_set(v___x_5536_, 6, v_currNamespace_5525_);
    crate::leanh::lean_ctor_set(v___x_5536_, 7, v_openDecls_5526_);
    crate::leanh::lean_ctor_set(v___x_5536_, 8, v_initHeartbeats_5527_);
    crate::leanh::lean_ctor_set(v___x_5536_, 9, v_maxHeartbeats_5528_);
    crate::leanh::lean_ctor_set(v___x_5536_, 10, v_quotContext_5529_);
    crate::leanh::lean_ctor_set(v___x_5536_, 11, v_currMacroScope_5530_);
    crate::leanh::lean_ctor_set(v___x_5536_, 12, v_cancelTk_x3f_5532_);
    crate::leanh::lean_ctor_set(v___x_5536_, 13, v_inheritedTraceOptions_5534_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5536_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5531_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5536_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5533_,
    );
    v___x_5537_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___x_5536_, v___y_5517_);
    crate::leanh::lean_dec_ref_known(v___x_5536_, 14);
    return v___x_5537_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg___boxed(
    mut v_ref_5538_: *mut crate::leanh::LeanObject,
    mut v_msg_5539_: *mut crate::leanh::LeanObject,
    mut v___y_5540_: *mut crate::leanh::LeanObject,
    mut v___y_5541_: *mut crate::leanh::LeanObject,
    mut v___y_5542_: *mut crate::leanh::LeanObject,
    mut v___y_5543_: *mut crate::leanh::LeanObject,
    mut v___y_5544_: *mut crate::leanh::LeanObject,
    mut v___y_5545_: *mut crate::leanh::LeanObject,
    mut v___y_5546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5547_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(
            v_ref_5538_,
            v_msg_5539_,
            v___y_5540_,
            v___y_5541_,
            v___y_5542_,
            v___y_5543_,
            v___y_5544_,
            v___y_5545_,
        );
    crate::leanh::lean_dec(v___y_5545_);
    crate::leanh::lean_dec_ref(v___y_5544_);
    crate::leanh::lean_dec(v___y_5543_);
    crate::leanh::lean_dec_ref(v___y_5542_);
    crate::leanh::lean_dec(v___y_5541_);
    crate::leanh::lean_dec_ref(v___y_5540_);
    crate::leanh::lean_dec(v_ref_5538_);
    return v_res_5547_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5549_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0;
    v___x_5550_ = l_Lean_stringToMessageData(v___x_5549_);
    return v___x_5550_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5552_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2;
    v___x_5553_ = l_Lean_stringToMessageData(v___x_5552_);
    return v___x_5553_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(
    mut v_item_5554_: *mut crate::leanh::LeanObject,
    mut v_a_5555_: *mut crate::leanh::LeanObject,
    mut v_a_5556_: *mut crate::leanh::LeanObject,
    mut v_a_5557_: *mut crate::leanh::LeanObject,
    mut v_a_5558_: *mut crate::leanh::LeanObject,
    mut v_a_5559_: *mut crate::leanh::LeanObject,
    mut v_a_5560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bool_x3f_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bool_x3f_5562_ = crate::leanh::lean_ctor_get(v_item_5554_, 3);
    if crate::leanh::lean_obj_tag(v_bool_x3f_5562_) == 0 {
        let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_item_5554_);
        v___x_5563_ = crate::leanh::lean_box(0);
        v___x_5564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5564_, 0, v___x_5563_);
        return v___x_5564_;
    } else {
        let mut v_option_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_origOptionName_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_option_5565_ = crate::leanh::lean_ctor_get(v_item_5554_, 1);
        crate::leanh::lean_inc(v_option_5565_);
        v_origOptionName_5566_ = crate::leanh::lean_ctor_get(v_item_5554_, 4);
        crate::leanh::lean_inc(v_origOptionName_5566_);
        crate::leanh::lean_dec_ref(v_item_5554_);
        v___x_5567_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1_once
            ),
            _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1,
        );
        v___x_5568_ = l_Lean_MessageData_ofName(v_origOptionName_5566_);
        v___x_5569_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5569_, 0, v___x_5567_);
        crate::leanh::lean_ctor_set(v___x_5569_, 1, v___x_5568_);
        v___x_5570_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3_once
            ),
            _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3,
        );
        v___x_5571_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5571_, 0, v___x_5569_);
        crate::leanh::lean_ctor_set(v___x_5571_, 1, v___x_5570_);
        v___x_5572_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_5565_, v___x_5571_, v_a_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_);
        crate::leanh::lean_dec(v_option_5565_);
        return v___x_5572_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___boxed(
    mut v_item_5573_: *mut crate::leanh::LeanObject,
    mut v_a_5574_: *mut crate::leanh::LeanObject,
    mut v_a_5575_: *mut crate::leanh::LeanObject,
    mut v_a_5576_: *mut crate::leanh::LeanObject,
    mut v_a_5577_: *mut crate::leanh::LeanObject,
    mut v_a_5578_: *mut crate::leanh::LeanObject,
    mut v_a_5579_: *mut crate::leanh::LeanObject,
    mut v_a_5580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5581_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(
        v_item_5573_,
        v_a_5574_,
        v_a_5575_,
        v_a_5576_,
        v_a_5577_,
        v_a_5578_,
        v_a_5579_,
    );
    crate::leanh::lean_dec(v_a_5579_);
    crate::leanh::lean_dec_ref(v_a_5578_);
    crate::leanh::lean_dec(v_a_5577_);
    crate::leanh::lean_dec_ref(v_a_5576_);
    crate::leanh::lean_dec(v_a_5575_);
    crate::leanh::lean_dec_ref(v_a_5574_);
    return v_res_5581_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(
    mut v_00_u03b1_5582_: *mut crate::leanh::LeanObject,
    mut v_ref_5583_: *mut crate::leanh::LeanObject,
    mut v_msg_5584_: *mut crate::leanh::LeanObject,
    mut v___y_5585_: *mut crate::leanh::LeanObject,
    mut v___y_5586_: *mut crate::leanh::LeanObject,
    mut v___y_5587_: *mut crate::leanh::LeanObject,
    mut v___y_5588_: *mut crate::leanh::LeanObject,
    mut v___y_5589_: *mut crate::leanh::LeanObject,
    mut v___y_5590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5592_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(
            v_ref_5583_,
            v_msg_5584_,
            v___y_5585_,
            v___y_5586_,
            v___y_5587_,
            v___y_5588_,
            v___y_5589_,
            v___y_5590_,
        );
    return v___x_5592_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___boxed(
    mut v_00_u03b1_5593_: *mut crate::leanh::LeanObject,
    mut v_ref_5594_: *mut crate::leanh::LeanObject,
    mut v_msg_5595_: *mut crate::leanh::LeanObject,
    mut v___y_5596_: *mut crate::leanh::LeanObject,
    mut v___y_5597_: *mut crate::leanh::LeanObject,
    mut v___y_5598_: *mut crate::leanh::LeanObject,
    mut v___y_5599_: *mut crate::leanh::LeanObject,
    mut v___y_5600_: *mut crate::leanh::LeanObject,
    mut v___y_5601_: *mut crate::leanh::LeanObject,
    mut v___y_5602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5603_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(
        v_00_u03b1_5593_,
        v_ref_5594_,
        v_msg_5595_,
        v___y_5596_,
        v___y_5597_,
        v___y_5598_,
        v___y_5599_,
        v___y_5600_,
        v___y_5601_,
    );
    crate::leanh::lean_dec(v___y_5601_);
    crate::leanh::lean_dec_ref(v___y_5600_);
    crate::leanh::lean_dec(v___y_5599_);
    crate::leanh::lean_dec_ref(v___y_5598_);
    crate::leanh::lean_dec(v___y_5597_);
    crate::leanh::lean_dec_ref(v___y_5596_);
    crate::leanh::lean_dec(v_ref_5594_);
    return v_res_5603_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(
    mut v_00_u03b1_5604_: *mut crate::leanh::LeanObject,
    mut v_msg_5605_: *mut crate::leanh::LeanObject,
    mut v___y_5606_: *mut crate::leanh::LeanObject,
    mut v___y_5607_: *mut crate::leanh::LeanObject,
    mut v___y_5608_: *mut crate::leanh::LeanObject,
    mut v___y_5609_: *mut crate::leanh::LeanObject,
    mut v___y_5610_: *mut crate::leanh::LeanObject,
    mut v___y_5611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5613_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_);
    return v___x_5613_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___boxed(
    mut v_00_u03b1_5614_: *mut crate::leanh::LeanObject,
    mut v_msg_5615_: *mut crate::leanh::LeanObject,
    mut v___y_5616_: *mut crate::leanh::LeanObject,
    mut v___y_5617_: *mut crate::leanh::LeanObject,
    mut v___y_5618_: *mut crate::leanh::LeanObject,
    mut v___y_5619_: *mut crate::leanh::LeanObject,
    mut v___y_5620_: *mut crate::leanh::LeanObject,
    mut v___y_5621_: *mut crate::leanh::LeanObject,
    mut v___y_5622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5623_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(v_00_u03b1_5614_, v_msg_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
    crate::leanh::lean_dec(v___y_5621_);
    crate::leanh::lean_dec_ref(v___y_5620_);
    crate::leanh::lean_dec(v___y_5619_);
    crate::leanh::lean_dec_ref(v___y_5618_);
    crate::leanh::lean_dec(v___y_5617_);
    crate::leanh::lean_dec_ref(v___y_5616_);
    return v_res_5623_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(
    mut v_msgData_5624_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5625_: *mut crate::leanh::LeanObject,
    mut v___y_5626_: *mut crate::leanh::LeanObject,
    mut v___y_5627_: *mut crate::leanh::LeanObject,
    mut v___y_5628_: *mut crate::leanh::LeanObject,
    mut v___y_5629_: *mut crate::leanh::LeanObject,
    mut v___y_5630_: *mut crate::leanh::LeanObject,
    mut v___y_5631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5633_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_5624_, v_macroStack_5625_, v___y_5630_);
    return v___x_5633_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_5634_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5635_: *mut crate::leanh::LeanObject,
    mut v___y_5636_: *mut crate::leanh::LeanObject,
    mut v___y_5637_: *mut crate::leanh::LeanObject,
    mut v___y_5638_: *mut crate::leanh::LeanObject,
    mut v___y_5639_: *mut crate::leanh::LeanObject,
    mut v___y_5640_: *mut crate::leanh::LeanObject,
    mut v___y_5641_: *mut crate::leanh::LeanObject,
    mut v___y_5642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5643_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(v_msgData_5634_, v_macroStack_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_);
    crate::leanh::lean_dec(v___y_5641_);
    crate::leanh::lean_dec_ref(v___y_5640_);
    crate::leanh::lean_dec(v___y_5639_);
    crate::leanh::lean_dec_ref(v___y_5638_);
    crate::leanh::lean_dec(v___y_5637_);
    crate::leanh::lean_dec_ref(v___y_5636_);
    return v_res_5643_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5645_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0;
    v___x_5646_ = l_Lean_stringToMessageData(v___x_5645_);
    return v___x_5646_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5648_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2;
    v___x_5649_ = l_Lean_stringToMessageData(v___x_5648_);
    return v___x_5649_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5651_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4;
    v___x_5652_ = l_Lean_stringToMessageData(v___x_5651_);
    return v___x_5652_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(
    mut v_item_5653_: *mut crate::leanh::LeanObject,
    mut v_structName_x3f_5654_: *mut crate::leanh::LeanObject,
    mut v_a_5655_: *mut crate::leanh::LeanObject,
    mut v_a_5656_: *mut crate::leanh::LeanObject,
    mut v_a_5657_: *mut crate::leanh::LeanObject,
    mut v_a_5658_: *mut crate::leanh::LeanObject,
    mut v_a_5659_: *mut crate::leanh::LeanObject,
    mut v_a_5660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_option_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origOptionName_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: u8 = 0;
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: u8 = 0;
    let mut v___x_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_option_5662_ = crate::leanh::lean_ctor_get(v_item_5653_, 1);
                crate::leanh::lean_inc(v_option_5662_);
                v_origOptionName_5663_ = crate::leanh::lean_ctor_get(v_item_5653_, 4);
                crate::leanh::lean_inc(v_origOptionName_5663_);
                crate::leanh::lean_dec_ref(v_item_5653_);
                v___x_5681_ = l_Lean_Name_isAnonymous(v_origOptionName_5663_);
                if v___x_5681_ == 0 {
                    v___x_5682_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
                    v___x_5683_ = l_Lean_MessageData_ofName(v_origOptionName_5663_);
                    v___x_5684_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5684_, 0, v___x_5682_);
                    crate::leanh::lean_ctor_set(v___x_5684_, 1, v___x_5683_);
                    v___x_5685_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                    );
                    v___x_5686_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5686_, 0, v___x_5684_);
                    crate::leanh::lean_ctor_set(v___x_5686_, 1, v___x_5685_);
                    v___y_5672_ = v___x_5686_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_origOptionName_5663_);
                    v___x_5687_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30,
                    );
                    v___y_5672_ = v___x_5687_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5667_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1);
                v___x_5668_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5668_, 0, v___x_5667_);
                crate::leanh::lean_ctor_set(v___x_5668_, 1, v___y_5665_);
                v___x_5669_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5669_, 0, v___x_5668_);
                crate::leanh::lean_ctor_set(v___x_5669_, 1, v___y_5666_);
                v___x_5670_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_5662_, v___x_5669_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_);
                crate::leanh::lean_dec(v_option_5662_);
                return v___x_5670_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_structName_x3f_5654_) == 1 {
                    v_val_5673_ = crate::leanh::lean_ctor_get(v_structName_x3f_5654_, 0);
                    crate::leanh::lean_inc(v_val_5673_);
                    crate::leanh::lean_dec_ref_known(v_structName_x3f_5654_, 1);
                    v___x_5674_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
                    v___x_5675_ = 0;
                    v___x_5676_ = l_Lean_MessageData_ofConstName(v_val_5673_, v___x_5675_);
                    v___x_5677_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5677_, 0, v___x_5674_);
                    crate::leanh::lean_ctor_set(v___x_5677_, 1, v___x_5676_);
                    v___x_5678_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                    );
                    v___x_5679_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5679_, 0, v___x_5677_);
                    crate::leanh::lean_ctor_set(v___x_5679_, 1, v___x_5678_);
                    v___y_5665_ = v___y_5672_;
                    v___y_5666_ = v___x_5679_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_structName_x3f_5654_);
                    v___x_5680_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30,
                    );
                    v___y_5665_ = v___y_5672_;
                    v___y_5666_ = v___x_5680_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___boxed(
    mut v_item_5688_: *mut crate::leanh::LeanObject,
    mut v_structName_x3f_5689_: *mut crate::leanh::LeanObject,
    mut v_a_5690_: *mut crate::leanh::LeanObject,
    mut v_a_5691_: *mut crate::leanh::LeanObject,
    mut v_a_5692_: *mut crate::leanh::LeanObject,
    mut v_a_5693_: *mut crate::leanh::LeanObject,
    mut v_a_5694_: *mut crate::leanh::LeanObject,
    mut v_a_5695_: *mut crate::leanh::LeanObject,
    mut v_a_5696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5697_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(
        v_item_5688_,
        v_structName_x3f_5689_,
        v_a_5690_,
        v_a_5691_,
        v_a_5692_,
        v_a_5693_,
        v_a_5694_,
        v_a_5695_,
    );
    crate::leanh::lean_dec(v_a_5695_);
    crate::leanh::lean_dec_ref(v_a_5694_);
    crate::leanh::lean_dec(v_a_5693_);
    crate::leanh::lean_dec_ref(v_a_5692_);
    crate::leanh::lean_dec(v_a_5691_);
    crate::leanh::lean_dec_ref(v_a_5690_);
    return v_res_5697_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(
    mut v_00_u03b1_5698_: *mut crate::leanh::LeanObject,
    mut v_item_5699_: *mut crate::leanh::LeanObject,
    mut v_structName_x3f_5700_: *mut crate::leanh::LeanObject,
    mut v_a_5701_: *mut crate::leanh::LeanObject,
    mut v_a_5702_: *mut crate::leanh::LeanObject,
    mut v_a_5703_: *mut crate::leanh::LeanObject,
    mut v_a_5704_: *mut crate::leanh::LeanObject,
    mut v_a_5705_: *mut crate::leanh::LeanObject,
    mut v_a_5706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5708_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(
        v_item_5699_,
        v_structName_x3f_5700_,
        v_a_5701_,
        v_a_5702_,
        v_a_5703_,
        v_a_5704_,
        v_a_5705_,
        v_a_5706_,
    );
    return v___x_5708_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___boxed(
    mut v_00_u03b1_5709_: *mut crate::leanh::LeanObject,
    mut v_item_5710_: *mut crate::leanh::LeanObject,
    mut v_structName_x3f_5711_: *mut crate::leanh::LeanObject,
    mut v_a_5712_: *mut crate::leanh::LeanObject,
    mut v_a_5713_: *mut crate::leanh::LeanObject,
    mut v_a_5714_: *mut crate::leanh::LeanObject,
    mut v_a_5715_: *mut crate::leanh::LeanObject,
    mut v_a_5716_: *mut crate::leanh::LeanObject,
    mut v_a_5717_: *mut crate::leanh::LeanObject,
    mut v_a_5718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5719_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(
        v_00_u03b1_5709_,
        v_item_5710_,
        v_structName_x3f_5711_,
        v_a_5712_,
        v_a_5713_,
        v_a_5714_,
        v_a_5715_,
        v_a_5716_,
        v_a_5717_,
    );
    crate::leanh::lean_dec(v_a_5717_);
    crate::leanh::lean_dec_ref(v_a_5716_);
    crate::leanh::lean_dec(v_a_5715_);
    crate::leanh::lean_dec_ref(v_a_5714_);
    crate::leanh::lean_dec(v_a_5713_);
    crate::leanh::lean_dec_ref(v_a_5712_);
    return v_res_5719_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5721_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0;
    v___x_5722_ = l_Lean_stringToMessageData(v___x_5721_);
    return v___x_5722_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5724_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2;
    v___x_5725_ = l_Lean_stringToMessageData(v___x_5724_);
    return v___x_5725_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(
    mut v_item_5726_: *mut crate::leanh::LeanObject,
    mut v_structName_x3f_5727_: *mut crate::leanh::LeanObject,
    mut v_a_5728_: *mut crate::leanh::LeanObject,
    mut v_a_5729_: *mut crate::leanh::LeanObject,
    mut v_a_5730_: *mut crate::leanh::LeanObject,
    mut v_a_5731_: *mut crate::leanh::LeanObject,
    mut v_a_5732_: *mut crate::leanh::LeanObject,
    mut v_a_5733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_option_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origOptionName_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: u8 = 0;
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: u8 = 0;
    let mut v___x_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_option_5735_ = crate::leanh::lean_ctor_get(v_item_5726_, 1);
                crate::leanh::lean_inc(v_option_5735_);
                v_origOptionName_5736_ = crate::leanh::lean_ctor_get(v_item_5726_, 4);
                crate::leanh::lean_inc(v_origOptionName_5736_);
                crate::leanh::lean_dec_ref(v_item_5726_);
                v___x_5756_ = l_Lean_Name_isAnonymous(v_origOptionName_5736_);
                if v___x_5756_ == 0 {
                    v___x_5757_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
                    v___x_5758_ = l_Lean_MessageData_ofName(v_origOptionName_5736_);
                    v___x_5759_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5759_, 0, v___x_5757_);
                    crate::leanh::lean_ctor_set(v___x_5759_, 1, v___x_5758_);
                    v___x_5760_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                    );
                    v___x_5761_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5761_, 0, v___x_5759_);
                    crate::leanh::lean_ctor_set(v___x_5761_, 1, v___x_5760_);
                    v___y_5747_ = v___x_5761_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_origOptionName_5736_);
                    v___x_5762_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30,
                    );
                    v___y_5747_ = v___x_5762_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5740_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1);
                v___x_5741_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5741_, 0, v___x_5740_);
                crate::leanh::lean_ctor_set(v___x_5741_, 1, v___y_5738_);
                v___x_5742_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5742_, 0, v___x_5741_);
                crate::leanh::lean_ctor_set(v___x_5742_, 1, v___y_5739_);
                v___x_5743_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3);
                v___x_5744_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5744_, 0, v___x_5742_);
                crate::leanh::lean_ctor_set(v___x_5744_, 1, v___x_5743_);
                v___x_5745_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_5735_, v___x_5744_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_);
                crate::leanh::lean_dec(v_option_5735_);
                return v___x_5745_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_structName_x3f_5727_) == 1 {
                    v_val_5748_ = crate::leanh::lean_ctor_get(v_structName_x3f_5727_, 0);
                    crate::leanh::lean_inc(v_val_5748_);
                    crate::leanh::lean_dec_ref_known(v_structName_x3f_5727_, 1);
                    v___x_5749_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
                    v___x_5750_ = 0;
                    v___x_5751_ = l_Lean_MessageData_ofConstName(v_val_5748_, v___x_5750_);
                    v___x_5752_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5752_, 0, v___x_5749_);
                    crate::leanh::lean_ctor_set(v___x_5752_, 1, v___x_5751_);
                    v___x_5753_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                    );
                    v___x_5754_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5754_, 0, v___x_5752_);
                    crate::leanh::lean_ctor_set(v___x_5754_, 1, v___x_5753_);
                    v___y_5738_ = v___y_5747_;
                    v___y_5739_ = v___x_5754_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_structName_x3f_5727_);
                    v___x_5755_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30,
                    );
                    v___y_5738_ = v___y_5747_;
                    v___y_5739_ = v___x_5755_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___boxed(
    mut v_item_5763_: *mut crate::leanh::LeanObject,
    mut v_structName_x3f_5764_: *mut crate::leanh::LeanObject,
    mut v_a_5765_: *mut crate::leanh::LeanObject,
    mut v_a_5766_: *mut crate::leanh::LeanObject,
    mut v_a_5767_: *mut crate::leanh::LeanObject,
    mut v_a_5768_: *mut crate::leanh::LeanObject,
    mut v_a_5769_: *mut crate::leanh::LeanObject,
    mut v_a_5770_: *mut crate::leanh::LeanObject,
    mut v_a_5771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5772_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(
        v_item_5763_,
        v_structName_x3f_5764_,
        v_a_5765_,
        v_a_5766_,
        v_a_5767_,
        v_a_5768_,
        v_a_5769_,
        v_a_5770_,
    );
    crate::leanh::lean_dec(v_a_5770_);
    crate::leanh::lean_dec_ref(v_a_5769_);
    crate::leanh::lean_dec(v_a_5768_);
    crate::leanh::lean_dec_ref(v_a_5767_);
    crate::leanh::lean_dec(v_a_5766_);
    crate::leanh::lean_dec_ref(v_a_5765_);
    return v_res_5772_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(
    mut v_00_u03b1_5773_: *mut crate::leanh::LeanObject,
    mut v_item_5774_: *mut crate::leanh::LeanObject,
    mut v_structName_x3f_5775_: *mut crate::leanh::LeanObject,
    mut v_a_5776_: *mut crate::leanh::LeanObject,
    mut v_a_5777_: *mut crate::leanh::LeanObject,
    mut v_a_5778_: *mut crate::leanh::LeanObject,
    mut v_a_5779_: *mut crate::leanh::LeanObject,
    mut v_a_5780_: *mut crate::leanh::LeanObject,
    mut v_a_5781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5783_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(
        v_item_5774_,
        v_structName_x3f_5775_,
        v_a_5776_,
        v_a_5777_,
        v_a_5778_,
        v_a_5779_,
        v_a_5780_,
        v_a_5781_,
    );
    return v___x_5783_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___boxed(
    mut v_00_u03b1_5784_: *mut crate::leanh::LeanObject,
    mut v_item_5785_: *mut crate::leanh::LeanObject,
    mut v_structName_x3f_5786_: *mut crate::leanh::LeanObject,
    mut v_a_5787_: *mut crate::leanh::LeanObject,
    mut v_a_5788_: *mut crate::leanh::LeanObject,
    mut v_a_5789_: *mut crate::leanh::LeanObject,
    mut v_a_5790_: *mut crate::leanh::LeanObject,
    mut v_a_5791_: *mut crate::leanh::LeanObject,
    mut v_a_5792_: *mut crate::leanh::LeanObject,
    mut v_a_5793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5794_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(
        v_00_u03b1_5784_,
        v_item_5785_,
        v_structName_x3f_5786_,
        v_a_5787_,
        v_a_5788_,
        v_a_5789_,
        v_a_5790_,
        v_a_5791_,
        v_a_5792_,
    );
    crate::leanh::lean_dec(v_a_5792_);
    crate::leanh::lean_dec_ref(v_a_5791_);
    crate::leanh::lean_dec(v_a_5790_);
    crate::leanh::lean_dec_ref(v_a_5789_);
    crate::leanh::lean_dec(v_a_5788_);
    crate::leanh::lean_dec_ref(v_a_5787_);
    return v_res_5794_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5795_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5795_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5796_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
    v___x_5797_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5797_, 0, v___x_5796_);
    return v___x_5797_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5798_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_5799_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5800_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5800_, 0, v___x_5799_);
    crate::leanh::lean_ctor_set(v___x_5800_, 1, v___x_5799_);
    crate::leanh::lean_ctor_set(v___x_5800_, 2, v___x_5799_);
    crate::leanh::lean_ctor_set(v___x_5800_, 3, v___x_5799_);
    crate::leanh::lean_ctor_set(v___x_5800_, 4, v___x_5798_);
    crate::leanh::lean_ctor_set(v___x_5800_, 5, v___x_5798_);
    crate::leanh::lean_ctor_set(v___x_5800_, 6, v___x_5798_);
    crate::leanh::lean_ctor_set(v___x_5800_, 7, v___x_5798_);
    crate::leanh::lean_ctor_set(v___x_5800_, 8, v___x_5798_);
    crate::leanh::lean_ctor_set(v___x_5800_, 9, v___x_5798_);
    return v___x_5800_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5801_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5802_ = lean_mk_empty_array_with_capacity(v___x_5801_);
    v___x_5803_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5803_, 0, v___x_5802_);
    return v___x_5803_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5804_: usize = 0;
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5804_ = 5usize;
    v___x_5805_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5806_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5807_ = lean_mk_empty_array_with_capacity(v___x_5806_);
    v___x_5808_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
    v___x_5809_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_5809_, 0, v___x_5808_);
    crate::leanh::lean_ctor_set(v___x_5809_, 1, v___x_5807_);
    crate::leanh::lean_ctor_set(v___x_5809_, 2, v___x_5805_);
    crate::leanh::lean_ctor_set(v___x_5809_, 3, v___x_5805_);
    crate::leanh::lean_ctor_set_usize(v___x_5809_, 4, v___x_5804_);
    return v___x_5809_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5810_ = crate::leanh::lean_box(1);
    v___x_5811_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_5812_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_5813_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5813_, 0, v___x_5812_);
    crate::leanh::lean_ctor_set(v___x_5813_, 1, v___x_5811_);
    crate::leanh::lean_ctor_set(v___x_5813_, 2, v___x_5810_);
    return v___x_5813_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5815_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_5816_ = l_Lean_stringToMessageData(v___x_5815_);
    return v___x_5816_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5818_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_5819_ = l_Lean_stringToMessageData(v___x_5818_);
    return v___x_5819_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5821_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_5822_ = l_Lean_stringToMessageData(v___x_5821_);
    return v___x_5822_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5824_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_5825_ = l_Lean_stringToMessageData(v___x_5824_);
    return v___x_5825_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14;
    v___x_5828_ = l_Lean_stringToMessageData(v___x_5827_);
    return v___x_5828_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5830_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16;
    v___x_5831_ = l_Lean_stringToMessageData(v___x_5830_);
    return v___x_5831_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5833_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18;
    v___x_5834_ = l_Lean_stringToMessageData(v___x_5833_);
    return v___x_5834_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(
    mut v_msg_5835_: *mut crate::leanh::LeanObject,
    mut v_declHint_5836_: *mut crate::leanh::LeanObject,
    mut v___y_5837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: u8 = 0;
    let mut v_isExporting_5842_: u8 = 0;
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: u8 = 0;
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5864_: u8 = 0;
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: u8 = 0;
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5896_: u8 = 0;
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5839_ = lean_st_ref_get(v___y_5837_);
                v_env_5840_ = crate::leanh::lean_ctor_get(v___x_5839_, 0);
                crate::leanh::lean_inc_ref(v_env_5840_);
                crate::leanh::lean_dec(v___x_5839_);
                v___x_5841_ = l_Lean_Name_isAnonymous(v_declHint_5836_);
                if v___x_5841_ == 0 {
                    v_isExporting_5842_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_5840_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5842_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_5840_);
                        crate::leanh::lean_dec(v_declHint_5836_);
                        v___x_5843_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5843_, 0, v_msg_5835_);
                        return v___x_5843_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_5840_);
                        v___x_5844_ = l_Lean_Environment_setExporting(v_env_5840_, v___x_5841_);
                        crate::leanh::lean_inc(v_declHint_5836_);
                        crate::leanh::lean_inc_ref(v___x_5844_);
                        v___x_5845_ = l_Lean_Environment_contains(
                            v___x_5844_,
                            v_declHint_5836_,
                            v_isExporting_5842_,
                        );
                        if v___x_5845_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5844_);
                            crate::leanh::lean_dec_ref(v_env_5840_);
                            crate::leanh::lean_dec(v_declHint_5836_);
                            v___x_5846_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5846_, 0, v_msg_5835_);
                            return v___x_5846_;
                        } else {
                            v___x_5847_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
                            v___x_5848_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
                            v___x_5849_ = l_Lean_Options_empty;
                            v___x_5850_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5850_, 0, v___x_5844_);
                            crate::leanh::lean_ctor_set(v___x_5850_, 1, v___x_5847_);
                            crate::leanh::lean_ctor_set(v___x_5850_, 2, v___x_5848_);
                            crate::leanh::lean_ctor_set(v___x_5850_, 3, v___x_5849_);
                            crate::leanh::lean_inc(v_declHint_5836_);
                            v___x_5851_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5836_, v___x_5841_);
                            v_c_5852_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_5852_, 0, v___x_5850_);
                            crate::leanh::lean_ctor_set(v_c_5852_, 1, v___x_5851_);
                            v___x_5853_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5840_,
                                v_declHint_5836_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5853_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_5840_);
                                crate::leanh::lean_dec(v_declHint_5836_);
                                v___x_5854_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
                                v___x_5855_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5855_, 0, v___x_5854_);
                                crate::leanh::lean_ctor_set(v___x_5855_, 1, v_c_5852_);
                                v___x_5856_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
                                v___x_5857_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5857_, 0, v___x_5855_);
                                crate::leanh::lean_ctor_set(v___x_5857_, 1, v___x_5856_);
                                v___x_5858_ = l_Lean_MessageData_note(v___x_5857_);
                                v___x_5859_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5859_, 0, v_msg_5835_);
                                crate::leanh::lean_ctor_set(v___x_5859_, 1, v___x_5858_);
                                v___x_5860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5860_, 0, v___x_5859_);
                                return v___x_5860_;
                            } else {
                                v_val_5861_ = crate::leanh::lean_ctor_get(v___x_5853_, 0);
                                v_isSharedCheck_5896_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5853_)) as u8;
                                if v_isSharedCheck_5896_ == 0 {
                                    v___x_5863_ = v___x_5853_;
                                    v_isShared_5864_ = v_isSharedCheck_5896_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_5861_);
                                    crate::leanh::lean_dec(v___x_5853_);
                                    v___x_5863_ = crate::leanh::lean_box(0);
                                    v_isShared_5864_ = v_isSharedCheck_5896_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_5840_);
                    crate::leanh::lean_dec(v_declHint_5836_);
                    v___x_5897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5897_, 0, v_msg_5835_);
                    return v___x_5897_;
                }
            }
            1 => {
                v___x_5865_ = crate::leanh::lean_box(0);
                v___x_5866_ = l_Lean_Environment_header(v_env_5840_);
                crate::leanh::lean_dec_ref(v_env_5840_);
                v___x_5867_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5866_);
                v_mod_5868_ = lean_array_get(v___x_5865_, v___x_5867_, v_val_5861_);
                crate::leanh::lean_dec(v_val_5861_);
                crate::leanh::lean_dec_ref(v___x_5867_);
                v___x_5869_ = l_Lean_isPrivateName(v_declHint_5836_);
                crate::leanh::lean_dec(v_declHint_5836_);
                if v___x_5869_ == 0 {
                    v___x_5870_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_5871_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5871_, 0, v___x_5870_);
                    crate::leanh::lean_ctor_set(v___x_5871_, 1, v_c_5852_);
                    v___x_5872_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_5873_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5873_, 0, v___x_5871_);
                    crate::leanh::lean_ctor_set(v___x_5873_, 1, v___x_5872_);
                    v___x_5874_ = l_Lean_MessageData_ofName(v_mod_5868_);
                    v___x_5875_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5875_, 0, v___x_5873_);
                    crate::leanh::lean_ctor_set(v___x_5875_, 1, v___x_5874_);
                    v___x_5876_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
                    v___x_5877_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5877_, 0, v___x_5875_);
                    crate::leanh::lean_ctor_set(v___x_5877_, 1, v___x_5876_);
                    v___x_5878_ = l_Lean_MessageData_note(v___x_5877_);
                    v___x_5879_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5879_, 0, v_msg_5835_);
                    crate::leanh::lean_ctor_set(v___x_5879_, 1, v___x_5878_);
                    if v_isShared_5864_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5863_, 0);
                        crate::leanh::lean_ctor_set(v___x_5863_, 0, v___x_5879_);
                        v___x_5881_ = v___x_5863_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5882_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5882_, 0, v___x_5879_);
                        v___x_5881_ = v_reuseFailAlloc_5882_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5883_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_5884_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5884_, 0, v___x_5883_);
                    crate::leanh::lean_ctor_set(v___x_5884_, 1, v_c_5852_);
                    v___x_5885_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
                    v___x_5886_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5886_, 0, v___x_5884_);
                    crate::leanh::lean_ctor_set(v___x_5886_, 1, v___x_5885_);
                    v___x_5887_ = l_Lean_MessageData_ofName(v_mod_5868_);
                    v___x_5888_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5888_, 0, v___x_5886_);
                    crate::leanh::lean_ctor_set(v___x_5888_, 1, v___x_5887_);
                    v___x_5889_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
                    v___x_5890_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5890_, 0, v___x_5888_);
                    crate::leanh::lean_ctor_set(v___x_5890_, 1, v___x_5889_);
                    v___x_5891_ = l_Lean_MessageData_note(v___x_5890_);
                    v___x_5892_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5892_, 0, v_msg_5835_);
                    crate::leanh::lean_ctor_set(v___x_5892_, 1, v___x_5891_);
                    if v_isShared_5864_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5863_, 0);
                        crate::leanh::lean_ctor_set(v___x_5863_, 0, v___x_5892_);
                        v___x_5894_ = v___x_5863_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5895_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5895_, 0, v___x_5892_);
                        v___x_5894_ = v_reuseFailAlloc_5895_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5881_;
            }
            3 => {
                return v___x_5894_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(
    mut v_msg_5898_: *mut crate::leanh::LeanObject,
    mut v_declHint_5899_: *mut crate::leanh::LeanObject,
    mut v___y_5900_: *mut crate::leanh::LeanObject,
    mut v___y_5901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5902_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_5898_, v_declHint_5899_, v___y_5900_);
    crate::leanh::lean_dec(v___y_5900_);
    return v_res_5902_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(
    mut v_msg_5903_: *mut crate::leanh::LeanObject,
    mut v_declHint_5904_: *mut crate::leanh::LeanObject,
    mut v___y_5905_: *mut crate::leanh::LeanObject,
    mut v___y_5906_: *mut crate::leanh::LeanObject,
    mut v___y_5907_: *mut crate::leanh::LeanObject,
    mut v___y_5908_: *mut crate::leanh::LeanObject,
    mut v___y_5909_: *mut crate::leanh::LeanObject,
    mut v___y_5910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5912_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_5903_, v_declHint_5904_, v___y_5910_);
                v_a_5913_ = crate::leanh::lean_ctor_get(v___x_5912_, 0);
                v_isSharedCheck_5922_ = (!crate::leanh::lean_is_exclusive(v___x_5912_)) as u8;
                if v_isSharedCheck_5922_ == 0 {
                    v___x_5915_ = v___x_5912_;
                    v_isShared_5916_ = v_isSharedCheck_5922_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5913_);
                    crate::leanh::lean_dec(v___x_5912_);
                    v___x_5915_ = crate::leanh::lean_box(0);
                    v_isShared_5916_ = v_isSharedCheck_5922_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5917_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5918_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5918_, 0, v___x_5917_);
                crate::leanh::lean_ctor_set(v___x_5918_, 1, v_a_5913_);
                if v_isShared_5916_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5915_, 0, v___x_5918_);
                    v___x_5920_ = v___x_5915_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5921_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5921_, 0, v___x_5918_);
                    v___x_5920_ = v_reuseFailAlloc_5921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(
    mut v_msg_5923_: *mut crate::leanh::LeanObject,
    mut v_declHint_5924_: *mut crate::leanh::LeanObject,
    mut v___y_5925_: *mut crate::leanh::LeanObject,
    mut v___y_5926_: *mut crate::leanh::LeanObject,
    mut v___y_5927_: *mut crate::leanh::LeanObject,
    mut v___y_5928_: *mut crate::leanh::LeanObject,
    mut v___y_5929_: *mut crate::leanh::LeanObject,
    mut v___y_5930_: *mut crate::leanh::LeanObject,
    mut v___y_5931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5932_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_5923_, v_declHint_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_);
    crate::leanh::lean_dec(v___y_5930_);
    crate::leanh::lean_dec_ref(v___y_5929_);
    crate::leanh::lean_dec(v___y_5928_);
    crate::leanh::lean_dec_ref(v___y_5927_);
    crate::leanh::lean_dec(v___y_5926_);
    crate::leanh::lean_dec_ref(v___y_5925_);
    return v_res_5932_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(
    mut v_ref_5933_: *mut crate::leanh::LeanObject,
    mut v_msg_5934_: *mut crate::leanh::LeanObject,
    mut v_declHint_5935_: *mut crate::leanh::LeanObject,
    mut v___y_5936_: *mut crate::leanh::LeanObject,
    mut v___y_5937_: *mut crate::leanh::LeanObject,
    mut v___y_5938_: *mut crate::leanh::LeanObject,
    mut v___y_5939_: *mut crate::leanh::LeanObject,
    mut v___y_5940_: *mut crate::leanh::LeanObject,
    mut v___y_5941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5943_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_5934_, v_declHint_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_);
    v_a_5944_ = crate::leanh::lean_ctor_get(v___x_5943_, 0);
    crate::leanh::lean_inc(v_a_5944_);
    crate::leanh::lean_dec_ref(v___x_5943_);
    v___x_5945_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(
            v_ref_5933_,
            v_a_5944_,
            v___y_5936_,
            v___y_5937_,
            v___y_5938_,
            v___y_5939_,
            v___y_5940_,
            v___y_5941_,
        );
    return v___x_5945_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(
    mut v_ref_5946_: *mut crate::leanh::LeanObject,
    mut v_msg_5947_: *mut crate::leanh::LeanObject,
    mut v_declHint_5948_: *mut crate::leanh::LeanObject,
    mut v___y_5949_: *mut crate::leanh::LeanObject,
    mut v___y_5950_: *mut crate::leanh::LeanObject,
    mut v___y_5951_: *mut crate::leanh::LeanObject,
    mut v___y_5952_: *mut crate::leanh::LeanObject,
    mut v___y_5953_: *mut crate::leanh::LeanObject,
    mut v___y_5954_: *mut crate::leanh::LeanObject,
    mut v___y_5955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5956_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_5946_, v_msg_5947_, v_declHint_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
    crate::leanh::lean_dec(v___y_5954_);
    crate::leanh::lean_dec_ref(v___y_5953_);
    crate::leanh::lean_dec(v___y_5952_);
    crate::leanh::lean_dec_ref(v___y_5951_);
    crate::leanh::lean_dec(v___y_5950_);
    crate::leanh::lean_dec_ref(v___y_5949_);
    crate::leanh::lean_dec(v_ref_5946_);
    return v_res_5956_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5958_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0;
    v___x_5959_ = l_Lean_stringToMessageData(v___x_5958_);
    return v___x_5959_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_ref_5960_: *mut crate::leanh::LeanObject,
    mut v_constName_5961_: *mut crate::leanh::LeanObject,
    mut v___y_5962_: *mut crate::leanh::LeanObject,
    mut v___y_5963_: *mut crate::leanh::LeanObject,
    mut v___y_5964_: *mut crate::leanh::LeanObject,
    mut v___y_5965_: *mut crate::leanh::LeanObject,
    mut v___y_5966_: *mut crate::leanh::LeanObject,
    mut v___y_5967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: u8 = 0;
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5969_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
    v___x_5970_ = 0;
    crate::leanh::lean_inc(v_constName_5961_);
    v___x_5971_ = l_Lean_MessageData_ofConstName(v_constName_5961_, v___x_5970_);
    v___x_5972_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5972_, 0, v___x_5969_);
    crate::leanh::lean_ctor_set(v___x_5972_, 1, v___x_5971_);
    v___x_5973_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
    );
    v___x_5974_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5974_, 0, v___x_5972_);
    crate::leanh::lean_ctor_set(v___x_5974_, 1, v___x_5973_);
    v___x_5975_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_5960_, v___x_5974_, v_constName_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_);
    return v___x_5975_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_ref_5976_: *mut crate::leanh::LeanObject,
    mut v_constName_5977_: *mut crate::leanh::LeanObject,
    mut v___y_5978_: *mut crate::leanh::LeanObject,
    mut v___y_5979_: *mut crate::leanh::LeanObject,
    mut v___y_5980_: *mut crate::leanh::LeanObject,
    mut v___y_5981_: *mut crate::leanh::LeanObject,
    mut v___y_5982_: *mut crate::leanh::LeanObject,
    mut v___y_5983_: *mut crate::leanh::LeanObject,
    mut v___y_5984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5985_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_5976_, v_constName_5977_, v___y_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
    crate::leanh::lean_dec(v___y_5983_);
    crate::leanh::lean_dec_ref(v___y_5982_);
    crate::leanh::lean_dec(v___y_5981_);
    crate::leanh::lean_dec_ref(v___y_5980_);
    crate::leanh::lean_dec(v___y_5979_);
    crate::leanh::lean_dec_ref(v___y_5978_);
    crate::leanh::lean_dec(v_ref_5976_);
    return v_res_5985_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_constName_5986_: *mut crate::leanh::LeanObject,
    mut v___y_5987_: *mut crate::leanh::LeanObject,
    mut v___y_5988_: *mut crate::leanh::LeanObject,
    mut v___y_5989_: *mut crate::leanh::LeanObject,
    mut v___y_5990_: *mut crate::leanh::LeanObject,
    mut v___y_5991_: *mut crate::leanh::LeanObject,
    mut v___y_5992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_5994_ = crate::leanh::lean_ctor_get(v___y_5991_, 5);
    v___x_5995_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_5994_, v_constName_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_);
    return v___x_5995_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_constName_5996_: *mut crate::leanh::LeanObject,
    mut v___y_5997_: *mut crate::leanh::LeanObject,
    mut v___y_5998_: *mut crate::leanh::LeanObject,
    mut v___y_5999_: *mut crate::leanh::LeanObject,
    mut v___y_6000_: *mut crate::leanh::LeanObject,
    mut v___y_6001_: *mut crate::leanh::LeanObject,
    mut v___y_6002_: *mut crate::leanh::LeanObject,
    mut v___y_6003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6004_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_);
    crate::leanh::lean_dec(v___y_6002_);
    crate::leanh::lean_dec_ref(v___y_6001_);
    crate::leanh::lean_dec(v___y_6000_);
    crate::leanh::lean_dec_ref(v___y_5999_);
    crate::leanh::lean_dec(v___y_5998_);
    crate::leanh::lean_dec_ref(v___y_5997_);
    return v_res_6004_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(
    mut v_constName_6005_: *mut crate::leanh::LeanObject,
    mut v___y_6006_: *mut crate::leanh::LeanObject,
    mut v___y_6007_: *mut crate::leanh::LeanObject,
    mut v___y_6008_: *mut crate::leanh::LeanObject,
    mut v___y_6009_: *mut crate::leanh::LeanObject,
    mut v___y_6010_: *mut crate::leanh::LeanObject,
    mut v___y_6011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: u8 = 0;
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6021_: u8 = 0;
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6013_ = lean_st_ref_get(v___y_6011_);
                v_env_6014_ = crate::leanh::lean_ctor_get(v___x_6013_, 0);
                crate::leanh::lean_inc_ref(v_env_6014_);
                crate::leanh::lean_dec(v___x_6013_);
                v___x_6015_ = 0;
                crate::leanh::lean_inc(v_constName_6005_);
                v___x_6016_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_6014_,
                    v_constName_6005_,
                    v___x_6015_,
                );
                if crate::leanh::lean_obj_tag(v___x_6016_) == 0 {
                    v___x_6017_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_);
                    return v___x_6017_;
                } else {
                    crate::leanh::lean_dec(v_constName_6005_);
                    v_val_6018_ = crate::leanh::lean_ctor_get(v___x_6016_, 0);
                    v_isSharedCheck_6025_ = (!crate::leanh::lean_is_exclusive(v___x_6016_)) as u8;
                    if v_isSharedCheck_6025_ == 0 {
                        v___x_6020_ = v___x_6016_;
                        v_isShared_6021_ = v_isSharedCheck_6025_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6018_);
                        crate::leanh::lean_dec(v___x_6016_);
                        v___x_6020_ = crate::leanh::lean_box(0);
                        v_isShared_6021_ = v_isSharedCheck_6025_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6021_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6020_, 0);
                    v___x_6023_ = v___x_6020_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6024_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6024_, 0, v_val_6018_);
                    v___x_6023_ = v_reuseFailAlloc_6024_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1___boxed(
    mut v_constName_6026_: *mut crate::leanh::LeanObject,
    mut v___y_6027_: *mut crate::leanh::LeanObject,
    mut v___y_6028_: *mut crate::leanh::LeanObject,
    mut v___y_6029_: *mut crate::leanh::LeanObject,
    mut v___y_6030_: *mut crate::leanh::LeanObject,
    mut v___y_6031_: *mut crate::leanh::LeanObject,
    mut v___y_6032_: *mut crate::leanh::LeanObject,
    mut v___y_6033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6034_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_);
    crate::leanh::lean_dec(v___y_6032_);
    crate::leanh::lean_dec_ref(v___y_6031_);
    crate::leanh::lean_dec(v___y_6030_);
    crate::leanh::lean_dec_ref(v___y_6029_);
    crate::leanh::lean_dec(v___y_6028_);
    crate::leanh::lean_dec_ref(v___y_6027_);
    return v_res_6034_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(
    mut v_a_6035_: *mut crate::leanh::LeanObject,
    mut v_a_6036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6042_: u8 = 0;
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6048_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6035_) == 0 {
                    v___x_6037_ = l_List_reverse___redArg(v_a_6036_);
                    return v___x_6037_;
                } else {
                    v_head_6038_ = crate::leanh::lean_ctor_get(v_a_6035_, 0);
                    v_tail_6039_ = crate::leanh::lean_ctor_get(v_a_6035_, 1);
                    v_isSharedCheck_6048_ = (!crate::leanh::lean_is_exclusive(v_a_6035_)) as u8;
                    if v_isSharedCheck_6048_ == 0 {
                        v___x_6041_ = v_a_6035_;
                        v_isShared_6042_ = v_isSharedCheck_6048_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6039_);
                        crate::leanh::lean_inc(v_head_6038_);
                        crate::leanh::lean_dec(v_a_6035_);
                        v___x_6041_ = crate::leanh::lean_box(0);
                        v_isShared_6042_ = v_isSharedCheck_6048_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6043_ = l_Lean_mkLevelParam(v_head_6038_);
                if v_isShared_6042_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6041_, 1, v_a_6036_);
                    crate::leanh::lean_ctor_set(v___x_6041_, 0, v___x_6043_);
                    v___x_6045_ = v___x_6041_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6047_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6047_, 0, v___x_6043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6047_, 1, v_a_6036_);
                    v___x_6045_ = v_reuseFailAlloc_6047_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6035_ = v_tail_6039_;
                v_a_6036_ = v___x_6045_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(
    mut v_constName_6049_: *mut crate::leanh::LeanObject,
    mut v___y_6050_: *mut crate::leanh::LeanObject,
    mut v___y_6051_: *mut crate::leanh::LeanObject,
    mut v___y_6052_: *mut crate::leanh::LeanObject,
    mut v___y_6053_: *mut crate::leanh::LeanObject,
    mut v___y_6054_: *mut crate::leanh::LeanObject,
    mut v___y_6055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6061_: u8 = 0;
    let mut v_levelParams_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6069_: u8 = 0;
    let mut v_a_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6073_: u8 = 0;
    let mut v___x_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_constName_6049_);
                v___x_6057_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_);
                if crate::leanh::lean_obj_tag(v___x_6057_) == 0 {
                    v_a_6058_ = crate::leanh::lean_ctor_get(v___x_6057_, 0);
                    v_isSharedCheck_6069_ = (!crate::leanh::lean_is_exclusive(v___x_6057_)) as u8;
                    if v_isSharedCheck_6069_ == 0 {
                        v___x_6060_ = v___x_6057_;
                        v_isShared_6061_ = v_isSharedCheck_6069_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6058_);
                        crate::leanh::lean_dec(v___x_6057_);
                        v___x_6060_ = crate::leanh::lean_box(0);
                        v_isShared_6061_ = v_isSharedCheck_6069_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_constName_6049_);
                    v_a_6070_ = crate::leanh::lean_ctor_get(v___x_6057_, 0);
                    v_isSharedCheck_6077_ = (!crate::leanh::lean_is_exclusive(v___x_6057_)) as u8;
                    if v_isSharedCheck_6077_ == 0 {
                        v___x_6072_ = v___x_6057_;
                        v_isShared_6073_ = v_isSharedCheck_6077_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6070_);
                        crate::leanh::lean_dec(v___x_6057_);
                        v___x_6072_ = crate::leanh::lean_box(0);
                        v_isShared_6073_ = v_isSharedCheck_6077_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_6062_ = crate::leanh::lean_ctor_get(v_a_6058_, 1);
                crate::leanh::lean_inc(v_levelParams_6062_);
                crate::leanh::lean_dec(v_a_6058_);
                v___x_6063_ = crate::leanh::lean_box(0);
                v___x_6064_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(v_levelParams_6062_, v___x_6063_);
                v___x_6065_ = l_Lean_mkConst(v_constName_6049_, v___x_6064_);
                if v_isShared_6061_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6060_, 0, v___x_6065_);
                    v___x_6067_ = v___x_6060_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6068_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6068_, 0, v___x_6065_);
                    v___x_6067_ = v_reuseFailAlloc_6068_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6067_;
            }
            3 => {
                if v_isShared_6073_ == 0 {
                    v___x_6075_ = v___x_6072_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6076_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6076_, 0, v_a_6070_);
                    v___x_6075_ = v_reuseFailAlloc_6076_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0___boxed(
    mut v_constName_6078_: *mut crate::leanh::LeanObject,
    mut v___y_6079_: *mut crate::leanh::LeanObject,
    mut v___y_6080_: *mut crate::leanh::LeanObject,
    mut v___y_6081_: *mut crate::leanh::LeanObject,
    mut v___y_6082_: *mut crate::leanh::LeanObject,
    mut v___y_6083_: *mut crate::leanh::LeanObject,
    mut v___y_6084_: *mut crate::leanh::LeanObject,
    mut v___y_6085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6086_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_constName_6078_, v___y_6079_, v___y_6080_, v___y_6081_, v___y_6082_, v___y_6083_, v___y_6084_);
    crate::leanh::lean_dec(v___y_6084_);
    crate::leanh::lean_dec_ref(v___y_6083_);
    crate::leanh::lean_dec(v___y_6082_);
    crate::leanh::lean_dec_ref(v___y_6081_);
    crate::leanh::lean_dec(v___y_6080_);
    crate::leanh::lean_dec_ref(v___y_6079_);
    return v_res_6086_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(
    mut v_t_6087_: *mut crate::leanh::LeanObject,
    mut v___y_6088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6092_: u8 = 0;
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6107_: u8 = 0;
    let mut v_enabled_6108_: u8 = 0;
    let mut v_assignment_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6114_: u8 = 0;
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6125_: u8 = 0;
    let mut v_isSharedCheck_6126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6090_ = lean_st_ref_get(v___y_6088_);
                v_infoState_6091_ = crate::leanh::lean_ctor_get(v___x_6090_, 7);
                crate::leanh::lean_inc_ref(v_infoState_6091_);
                crate::leanh::lean_dec(v___x_6090_);
                v_enabled_6092_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_6091_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_6091_);
                if v_enabled_6092_ == 0 {
                    crate::leanh::lean_dec_ref(v_t_6087_);
                    v___x_6093_ = crate::leanh::lean_box(0);
                    v___x_6094_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6094_, 0, v___x_6093_);
                    return v___x_6094_;
                } else {
                    v___x_6095_ = lean_st_ref_take(v___y_6088_);
                    v_infoState_6096_ = crate::leanh::lean_ctor_get(v___x_6095_, 7);
                    v_env_6097_ = crate::leanh::lean_ctor_get(v___x_6095_, 0);
                    v_nextMacroScope_6098_ = crate::leanh::lean_ctor_get(v___x_6095_, 1);
                    v_ngen_6099_ = crate::leanh::lean_ctor_get(v___x_6095_, 2);
                    v_auxDeclNGen_6100_ = crate::leanh::lean_ctor_get(v___x_6095_, 3);
                    v_traceState_6101_ = crate::leanh::lean_ctor_get(v___x_6095_, 4);
                    v_cache_6102_ = crate::leanh::lean_ctor_get(v___x_6095_, 5);
                    v_messages_6103_ = crate::leanh::lean_ctor_get(v___x_6095_, 6);
                    v_snapshotTasks_6104_ = crate::leanh::lean_ctor_get(v___x_6095_, 8);
                    v_isSharedCheck_6126_ = (!crate::leanh::lean_is_exclusive(v___x_6095_)) as u8;
                    if v_isSharedCheck_6126_ == 0 {
                        v___x_6106_ = v___x_6095_;
                        v_isShared_6107_ = v_isSharedCheck_6126_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_6104_);
                        crate::leanh::lean_inc(v_infoState_6096_);
                        crate::leanh::lean_inc(v_messages_6103_);
                        crate::leanh::lean_inc(v_cache_6102_);
                        crate::leanh::lean_inc(v_traceState_6101_);
                        crate::leanh::lean_inc(v_auxDeclNGen_6100_);
                        crate::leanh::lean_inc(v_ngen_6099_);
                        crate::leanh::lean_inc(v_nextMacroScope_6098_);
                        crate::leanh::lean_inc(v_env_6097_);
                        crate::leanh::lean_dec(v___x_6095_);
                        v___x_6106_ = crate::leanh::lean_box(0);
                        v_isShared_6107_ = v_isSharedCheck_6126_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_6108_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_6096_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_6109_ = crate::leanh::lean_ctor_get(v_infoState_6096_, 0);
                v_lazyAssignment_6110_ = crate::leanh::lean_ctor_get(v_infoState_6096_, 1);
                v_trees_6111_ = crate::leanh::lean_ctor_get(v_infoState_6096_, 2);
                v_isSharedCheck_6125_ = (!crate::leanh::lean_is_exclusive(v_infoState_6096_)) as u8;
                if v_isSharedCheck_6125_ == 0 {
                    v___x_6113_ = v_infoState_6096_;
                    v_isShared_6114_ = v_isSharedCheck_6125_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trees_6111_);
                    crate::leanh::lean_inc(v_lazyAssignment_6110_);
                    crate::leanh::lean_inc(v_assignment_6109_);
                    crate::leanh::lean_dec(v_infoState_6096_);
                    v___x_6113_ = crate::leanh::lean_box(0);
                    v_isShared_6114_ = v_isSharedCheck_6125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6115_ = l_Lean_PersistentArray_push___redArg(v_trees_6111_, v_t_6087_);
                if v_isShared_6114_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6113_, 2, v___x_6115_);
                    v___x_6117_ = v___x_6113_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6124_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_assignment_6109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6124_, 1, v_lazyAssignment_6110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6124_, 2, v___x_6115_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6124_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_6108_,
                    );
                    v___x_6117_ = v_reuseFailAlloc_6124_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6107_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6106_, 7, v___x_6117_);
                    v___x_6119_ = v___x_6106_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6123_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 0, v_env_6097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 1, v_nextMacroScope_6098_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 2, v_ngen_6099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 3, v_auxDeclNGen_6100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 4, v_traceState_6101_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 5, v_cache_6102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 6, v_messages_6103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 7, v___x_6117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 8, v_snapshotTasks_6104_);
                    v___x_6119_ = v_reuseFailAlloc_6123_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6120_ = lean_st_ref_set(v___y_6088_, v___x_6119_);
                v___x_6121_ = crate::leanh::lean_box(0);
                v___x_6122_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6122_, 0, v___x_6121_);
                return v___x_6122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_t_6127_: *mut crate::leanh::LeanObject,
    mut v___y_6128_: *mut crate::leanh::LeanObject,
    mut v___y_6129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6130_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_6127_, v___y_6128_);
    crate::leanh::lean_dec(v___y_6128_);
    return v_res_6130_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6131_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6132_ = lean_mk_empty_array_with_capacity(v___x_6131_);
    v___x_6133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6133_, 0, v___x_6132_);
    return v___x_6133_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6134_: usize = 0;
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6134_ = 5usize;
    v___x_6135_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6136_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6137_ = lean_mk_empty_array_with_capacity(v___x_6136_);
    v___x_6138_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0);
    v___x_6139_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_6139_, 0, v___x_6138_);
    crate::leanh::lean_ctor_set(v___x_6139_, 1, v___x_6137_);
    crate::leanh::lean_ctor_set(v___x_6139_, 2, v___x_6135_);
    crate::leanh::lean_ctor_set(v___x_6139_, 3, v___x_6135_);
    crate::leanh::lean_ctor_set_usize(v___x_6139_, 4, v___x_6134_);
    return v___x_6139_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(
    mut v_t_6140_: *mut crate::leanh::LeanObject,
    mut v___y_6141_: *mut crate::leanh::LeanObject,
    mut v___y_6142_: *mut crate::leanh::LeanObject,
    mut v___y_6143_: *mut crate::leanh::LeanObject,
    mut v___y_6144_: *mut crate::leanh::LeanObject,
    mut v___y_6145_: *mut crate::leanh::LeanObject,
    mut v___y_6146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6150_: u8 = 0;
    v___x_6148_ = lean_st_ref_get(v___y_6146_);
    v_infoState_6149_ = crate::leanh::lean_ctor_get(v___x_6148_, 7);
    crate::leanh::lean_inc_ref(v_infoState_6149_);
    crate::leanh::lean_dec(v___x_6148_);
    v_enabled_6150_ = crate::leanh::lean_ctor_get_uint8(
        v_infoState_6149_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_infoState_6149_);
    if v_enabled_6150_ == 0 {
        let mut v___x_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_t_6140_);
        v___x_6151_ = crate::leanh::lean_box(0);
        v___x_6152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6152_, 0, v___x_6151_);
        return v___x_6152_;
    } else {
        let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6153_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
        v___x_6154_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6154_, 0, v_t_6140_);
        crate::leanh::lean_ctor_set(v___x_6154_, 1, v___x_6153_);
        v___x_6155_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v___x_6154_, v___y_6146_);
        return v___x_6155_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___boxed(
    mut v_t_6156_: *mut crate::leanh::LeanObject,
    mut v___y_6157_: *mut crate::leanh::LeanObject,
    mut v___y_6158_: *mut crate::leanh::LeanObject,
    mut v___y_6159_: *mut crate::leanh::LeanObject,
    mut v___y_6160_: *mut crate::leanh::LeanObject,
    mut v___y_6161_: *mut crate::leanh::LeanObject,
    mut v___y_6162_: *mut crate::leanh::LeanObject,
    mut v___y_6163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6164_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v_t_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_);
    crate::leanh::lean_dec(v___y_6162_);
    crate::leanh::lean_dec_ref(v___y_6161_);
    crate::leanh::lean_dec(v___y_6160_);
    crate::leanh::lean_dec_ref(v___y_6159_);
    crate::leanh::lean_dec(v___y_6158_);
    crate::leanh::lean_dec_ref(v___y_6157_);
    return v_res_6164_;
}
pub unsafe fn l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(
    mut v_stx_6165_: *mut crate::leanh::LeanObject,
    mut v_n_6166_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_6167_: *mut crate::leanh::LeanObject,
    mut v___y_6168_: *mut crate::leanh::LeanObject,
    mut v___y_6169_: *mut crate::leanh::LeanObject,
    mut v___y_6170_: *mut crate::leanh::LeanObject,
    mut v___y_6171_: *mut crate::leanh::LeanObject,
    mut v___y_6172_: *mut crate::leanh::LeanObject,
    mut v___y_6173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: u8 = 0;
    let mut v___x_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6187_: u8 = 0;
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6175_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_n_6166_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_);
                if crate::leanh::lean_obj_tag(v___x_6175_) == 0 {
                    v_a_6176_ = crate::leanh::lean_ctor_get(v___x_6175_, 0);
                    crate::leanh::lean_inc(v_a_6176_);
                    crate::leanh::lean_dec_ref_known(v___x_6175_, 1);
                    v___x_6177_ = crate::leanh::lean_box(0);
                    v___x_6178_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6178_, 0, v___x_6177_);
                    crate::leanh::lean_ctor_set(v___x_6178_, 1, v_stx_6165_);
                    v___x_6179_ = l_Lean_LocalContext_empty;
                    v___x_6180_ = 0;
                    v___x_6181_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_6181_, 0, v___x_6178_);
                    crate::leanh::lean_ctor_set(v___x_6181_, 1, v___x_6179_);
                    crate::leanh::lean_ctor_set(v___x_6181_, 2, v_expectedType_x3f_6167_);
                    crate::leanh::lean_ctor_set(v___x_6181_, 3, v_a_6176_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6181_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v___x_6180_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6181_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v___x_6180_,
                    );
                    v___x_6182_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6182_, 0, v___x_6181_);
                    v___x_6183_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_6182_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_);
                    return v___x_6183_;
                } else {
                    crate::leanh::lean_dec(v_expectedType_x3f_6167_);
                    crate::leanh::lean_dec(v_stx_6165_);
                    v_a_6184_ = crate::leanh::lean_ctor_get(v___x_6175_, 0);
                    v_isSharedCheck_6191_ = (!crate::leanh::lean_is_exclusive(v___x_6175_)) as u8;
                    if v_isSharedCheck_6191_ == 0 {
                        v___x_6186_ = v___x_6175_;
                        v_isShared_6187_ = v_isSharedCheck_6191_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6184_);
                        crate::leanh::lean_dec(v___x_6175_);
                        v___x_6186_ = crate::leanh::lean_box(0);
                        v_isShared_6187_ = v_isSharedCheck_6191_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6187_ == 0 {
                    v___x_6189_ = v___x_6186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6190_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6190_, 0, v_a_6184_);
                    v___x_6189_ = v_reuseFailAlloc_6190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0___boxed(
    mut v_stx_6192_: *mut crate::leanh::LeanObject,
    mut v_n_6193_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_6194_: *mut crate::leanh::LeanObject,
    mut v___y_6195_: *mut crate::leanh::LeanObject,
    mut v___y_6196_: *mut crate::leanh::LeanObject,
    mut v___y_6197_: *mut crate::leanh::LeanObject,
    mut v___y_6198_: *mut crate::leanh::LeanObject,
    mut v___y_6199_: *mut crate::leanh::LeanObject,
    mut v___y_6200_: *mut crate::leanh::LeanObject,
    mut v___y_6201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6202_ =
        l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(
            v_stx_6192_,
            v_n_6193_,
            v_expectedType_x3f_6194_,
            v___y_6195_,
            v___y_6196_,
            v___y_6197_,
            v___y_6198_,
            v___y_6199_,
            v___y_6200_,
        );
    crate::leanh::lean_dec(v___y_6200_);
    crate::leanh::lean_dec_ref(v___y_6199_);
    crate::leanh::lean_dec(v___y_6198_);
    crate::leanh::lean_dec_ref(v___y_6197_);
    crate::leanh::lean_dec(v___y_6196_);
    crate::leanh::lean_dec_ref(v___y_6195_);
    return v_res_6202_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
    mut v_item_6203_: *mut crate::leanh::LeanObject,
    mut v_projFn_6204_: *mut crate::leanh::LeanObject,
    mut v_a_6205_: *mut crate::leanh::LeanObject,
    mut v_a_6206_: *mut crate::leanh::LeanObject,
    mut v_a_6207_: *mut crate::leanh::LeanObject,
    mut v_a_6208_: *mut crate::leanh::LeanObject,
    mut v_a_6209_: *mut crate::leanh::LeanObject,
    mut v_a_6210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6214_: u8 = 0;
    v___x_6212_ = lean_st_ref_get(v_a_6210_);
    v_infoState_6213_ = crate::leanh::lean_ctor_get(v___x_6212_, 7);
    crate::leanh::lean_inc_ref(v_infoState_6213_);
    crate::leanh::lean_dec(v___x_6212_);
    v_enabled_6214_ = crate::leanh::lean_ctor_get_uint8(
        v_infoState_6213_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_infoState_6213_);
    if v_enabled_6214_ == 0 {
        let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_projFn_6204_);
        v___x_6215_ = crate::leanh::lean_box(0);
        v___x_6216_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6216_, 0, v___x_6215_);
        return v___x_6216_;
    } else {
        let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_env_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6219_: u8 = 0;
        v___x_6217_ = lean_st_ref_get(v_a_6210_);
        v_env_6218_ = crate::leanh::lean_ctor_get(v___x_6217_, 0);
        crate::leanh::lean_inc_ref(v_env_6218_);
        crate::leanh::lean_dec(v___x_6217_);
        crate::leanh::lean_inc(v_projFn_6204_);
        v___x_6219_ = l_Lean_Environment_contains(v_env_6218_, v_projFn_6204_, v_enabled_6214_);
        if v___x_6219_ == 0 {
            let mut v___x_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_projFn_6204_);
            v___x_6220_ = crate::leanh::lean_box(0);
            v___x_6221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6221_, 0, v___x_6220_);
            return v___x_6221_;
        } else {
            let mut v___x_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6222_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_6203_);
            v___x_6223_ = crate::leanh::lean_box(0);
            v___x_6224_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v___x_6222_, v_projFn_6204_, v___x_6223_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_);
            return v___x_6224_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___boxed(
    mut v_item_6225_: *mut crate::leanh::LeanObject,
    mut v_projFn_6226_: *mut crate::leanh::LeanObject,
    mut v_a_6227_: *mut crate::leanh::LeanObject,
    mut v_a_6228_: *mut crate::leanh::LeanObject,
    mut v_a_6229_: *mut crate::leanh::LeanObject,
    mut v_a_6230_: *mut crate::leanh::LeanObject,
    mut v_a_6231_: *mut crate::leanh::LeanObject,
    mut v_a_6232_: *mut crate::leanh::LeanObject,
    mut v_a_6233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6234_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
        v_item_6225_,
        v_projFn_6226_,
        v_a_6227_,
        v_a_6228_,
        v_a_6229_,
        v_a_6230_,
        v_a_6231_,
        v_a_6232_,
    );
    crate::leanh::lean_dec(v_a_6232_);
    crate::leanh::lean_dec_ref(v_a_6231_);
    crate::leanh::lean_dec(v_a_6230_);
    crate::leanh::lean_dec_ref(v_a_6229_);
    crate::leanh::lean_dec(v_a_6228_);
    crate::leanh::lean_dec_ref(v_a_6227_);
    crate::leanh::lean_dec_ref(v_item_6225_);
    return v_res_6234_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(
    mut v_t_6235_: *mut crate::leanh::LeanObject,
    mut v___y_6236_: *mut crate::leanh::LeanObject,
    mut v___y_6237_: *mut crate::leanh::LeanObject,
    mut v___y_6238_: *mut crate::leanh::LeanObject,
    mut v___y_6239_: *mut crate::leanh::LeanObject,
    mut v___y_6240_: *mut crate::leanh::LeanObject,
    mut v___y_6241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6243_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_6235_, v___y_6241_);
    return v___x_6243_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___boxed(
    mut v_t_6244_: *mut crate::leanh::LeanObject,
    mut v___y_6245_: *mut crate::leanh::LeanObject,
    mut v___y_6246_: *mut crate::leanh::LeanObject,
    mut v___y_6247_: *mut crate::leanh::LeanObject,
    mut v___y_6248_: *mut crate::leanh::LeanObject,
    mut v___y_6249_: *mut crate::leanh::LeanObject,
    mut v___y_6250_: *mut crate::leanh::LeanObject,
    mut v___y_6251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6252_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(v_t_6244_, v___y_6245_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_);
    crate::leanh::lean_dec(v___y_6250_);
    crate::leanh::lean_dec_ref(v___y_6249_);
    crate::leanh::lean_dec(v___y_6248_);
    crate::leanh::lean_dec_ref(v___y_6247_);
    crate::leanh::lean_dec(v___y_6246_);
    crate::leanh::lean_dec_ref(v___y_6245_);
    return v_res_6252_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_6253_: *mut crate::leanh::LeanObject,
    mut v_constName_6254_: *mut crate::leanh::LeanObject,
    mut v___y_6255_: *mut crate::leanh::LeanObject,
    mut v___y_6256_: *mut crate::leanh::LeanObject,
    mut v___y_6257_: *mut crate::leanh::LeanObject,
    mut v___y_6258_: *mut crate::leanh::LeanObject,
    mut v___y_6259_: *mut crate::leanh::LeanObject,
    mut v___y_6260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6262_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_);
    return v___x_6262_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_6263_: *mut crate::leanh::LeanObject,
    mut v_constName_6264_: *mut crate::leanh::LeanObject,
    mut v___y_6265_: *mut crate::leanh::LeanObject,
    mut v___y_6266_: *mut crate::leanh::LeanObject,
    mut v___y_6267_: *mut crate::leanh::LeanObject,
    mut v___y_6268_: *mut crate::leanh::LeanObject,
    mut v___y_6269_: *mut crate::leanh::LeanObject,
    mut v___y_6270_: *mut crate::leanh::LeanObject,
    mut v___y_6271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6272_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_6263_, v_constName_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_);
    crate::leanh::lean_dec(v___y_6270_);
    crate::leanh::lean_dec_ref(v___y_6269_);
    crate::leanh::lean_dec(v___y_6268_);
    crate::leanh::lean_dec_ref(v___y_6267_);
    crate::leanh::lean_dec(v___y_6266_);
    crate::leanh::lean_dec_ref(v___y_6265_);
    return v_res_6272_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b1_6273_: *mut crate::leanh::LeanObject,
    mut v_ref_6274_: *mut crate::leanh::LeanObject,
    mut v_constName_6275_: *mut crate::leanh::LeanObject,
    mut v___y_6276_: *mut crate::leanh::LeanObject,
    mut v___y_6277_: *mut crate::leanh::LeanObject,
    mut v___y_6278_: *mut crate::leanh::LeanObject,
    mut v___y_6279_: *mut crate::leanh::LeanObject,
    mut v___y_6280_: *mut crate::leanh::LeanObject,
    mut v___y_6281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6283_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_6274_, v_constName_6275_, v___y_6276_, v___y_6277_, v___y_6278_, v___y_6279_, v___y_6280_, v___y_6281_);
    return v___x_6283_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b1_6284_: *mut crate::leanh::LeanObject,
    mut v_ref_6285_: *mut crate::leanh::LeanObject,
    mut v_constName_6286_: *mut crate::leanh::LeanObject,
    mut v___y_6287_: *mut crate::leanh::LeanObject,
    mut v___y_6288_: *mut crate::leanh::LeanObject,
    mut v___y_6289_: *mut crate::leanh::LeanObject,
    mut v___y_6290_: *mut crate::leanh::LeanObject,
    mut v___y_6291_: *mut crate::leanh::LeanObject,
    mut v___y_6292_: *mut crate::leanh::LeanObject,
    mut v___y_6293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6294_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_6284_, v_ref_6285_, v_constName_6286_, v___y_6287_, v___y_6288_, v___y_6289_, v___y_6290_, v___y_6291_, v___y_6292_);
    crate::leanh::lean_dec(v___y_6292_);
    crate::leanh::lean_dec_ref(v___y_6291_);
    crate::leanh::lean_dec(v___y_6290_);
    crate::leanh::lean_dec_ref(v___y_6289_);
    crate::leanh::lean_dec(v___y_6288_);
    crate::leanh::lean_dec_ref(v___y_6287_);
    crate::leanh::lean_dec(v_ref_6285_);
    return v_res_6294_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(
    mut v_00_u03b1_6295_: *mut crate::leanh::LeanObject,
    mut v_ref_6296_: *mut crate::leanh::LeanObject,
    mut v_msg_6297_: *mut crate::leanh::LeanObject,
    mut v_declHint_6298_: *mut crate::leanh::LeanObject,
    mut v___y_6299_: *mut crate::leanh::LeanObject,
    mut v___y_6300_: *mut crate::leanh::LeanObject,
    mut v___y_6301_: *mut crate::leanh::LeanObject,
    mut v___y_6302_: *mut crate::leanh::LeanObject,
    mut v___y_6303_: *mut crate::leanh::LeanObject,
    mut v___y_6304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6306_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_6296_, v_msg_6297_, v_declHint_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
    return v___x_6306_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(
    mut v_00_u03b1_6307_: *mut crate::leanh::LeanObject,
    mut v_ref_6308_: *mut crate::leanh::LeanObject,
    mut v_msg_6309_: *mut crate::leanh::LeanObject,
    mut v_declHint_6310_: *mut crate::leanh::LeanObject,
    mut v___y_6311_: *mut crate::leanh::LeanObject,
    mut v___y_6312_: *mut crate::leanh::LeanObject,
    mut v___y_6313_: *mut crate::leanh::LeanObject,
    mut v___y_6314_: *mut crate::leanh::LeanObject,
    mut v___y_6315_: *mut crate::leanh::LeanObject,
    mut v___y_6316_: *mut crate::leanh::LeanObject,
    mut v___y_6317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6318_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_6307_, v_ref_6308_, v_msg_6309_, v_declHint_6310_, v___y_6311_, v___y_6312_, v___y_6313_, v___y_6314_, v___y_6315_, v___y_6316_);
    crate::leanh::lean_dec(v___y_6316_);
    crate::leanh::lean_dec_ref(v___y_6315_);
    crate::leanh::lean_dec(v___y_6314_);
    crate::leanh::lean_dec_ref(v___y_6313_);
    crate::leanh::lean_dec(v___y_6312_);
    crate::leanh::lean_dec_ref(v___y_6311_);
    crate::leanh::lean_dec(v_ref_6308_);
    return v_res_6318_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(
    mut v_msg_6319_: *mut crate::leanh::LeanObject,
    mut v_declHint_6320_: *mut crate::leanh::LeanObject,
    mut v___y_6321_: *mut crate::leanh::LeanObject,
    mut v___y_6322_: *mut crate::leanh::LeanObject,
    mut v___y_6323_: *mut crate::leanh::LeanObject,
    mut v___y_6324_: *mut crate::leanh::LeanObject,
    mut v___y_6325_: *mut crate::leanh::LeanObject,
    mut v___y_6326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6328_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_6319_, v_declHint_6320_, v___y_6326_);
    return v___x_6328_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(
    mut v_msg_6329_: *mut crate::leanh::LeanObject,
    mut v_declHint_6330_: *mut crate::leanh::LeanObject,
    mut v___y_6331_: *mut crate::leanh::LeanObject,
    mut v___y_6332_: *mut crate::leanh::LeanObject,
    mut v___y_6333_: *mut crate::leanh::LeanObject,
    mut v___y_6334_: *mut crate::leanh::LeanObject,
    mut v___y_6335_: *mut crate::leanh::LeanObject,
    mut v___y_6336_: *mut crate::leanh::LeanObject,
    mut v___y_6337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6338_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_6329_, v_declHint_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_);
    crate::leanh::lean_dec(v___y_6336_);
    crate::leanh::lean_dec_ref(v___y_6335_);
    crate::leanh::lean_dec(v___y_6334_);
    crate::leanh::lean_dec_ref(v___y_6333_);
    crate::leanh::lean_dec(v___y_6332_);
    crate::leanh::lean_dec_ref(v___y_6331_);
    return v_res_6338_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(
    mut v_info_6339_: *mut crate::leanh::LeanObject,
    mut v___y_6340_: *mut crate::leanh::LeanObject,
    mut v___y_6341_: *mut crate::leanh::LeanObject,
    mut v___y_6342_: *mut crate::leanh::LeanObject,
    mut v___y_6343_: *mut crate::leanh::LeanObject,
    mut v___y_6344_: *mut crate::leanh::LeanObject,
    mut v___y_6345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6347_ = crate::leanh::lean_alloc_ctor(8, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6347_, 0, v_info_6339_);
    v___x_6348_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_6347_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_, v___y_6345_);
    return v___x_6348_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0___boxed(
    mut v_info_6349_: *mut crate::leanh::LeanObject,
    mut v___y_6350_: *mut crate::leanh::LeanObject,
    mut v___y_6351_: *mut crate::leanh::LeanObject,
    mut v___y_6352_: *mut crate::leanh::LeanObject,
    mut v___y_6353_: *mut crate::leanh::LeanObject,
    mut v___y_6354_: *mut crate::leanh::LeanObject,
    mut v___y_6355_: *mut crate::leanh::LeanObject,
    mut v___y_6356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6357_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v_info_6349_, v___y_6350_, v___y_6351_, v___y_6352_, v___y_6353_, v___y_6354_, v___y_6355_);
    crate::leanh::lean_dec(v___y_6355_);
    crate::leanh::lean_dec_ref(v___y_6354_);
    crate::leanh::lean_dec(v___y_6353_);
    crate::leanh::lean_dec_ref(v___y_6352_);
    crate::leanh::lean_dec(v___y_6351_);
    crate::leanh::lean_dec_ref(v___y_6350_);
    return v_res_6357_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6358_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6358_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6359_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0,
    );
    v___x_6360_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6360_, 0, v___x_6359_);
    return v___x_6360_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6361_ = crate::leanh::lean_box(1);
    v___x_6362_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_6363_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1,
    );
    v___x_6364_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6364_, 0, v___x_6363_);
    crate::leanh::lean_ctor_set(v___x_6364_, 1, v___x_6362_);
    crate::leanh::lean_ctor_set(v___x_6364_, 2, v___x_6361_);
    return v___x_6364_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(
    mut v_item_6365_: *mut crate::leanh::LeanObject,
    mut v_structName_6366_: *mut crate::leanh::LeanObject,
    mut v_a_6367_: *mut crate::leanh::LeanObject,
    mut v_a_6368_: *mut crate::leanh::LeanObject,
    mut v_a_6369_: *mut crate::leanh::LeanObject,
    mut v_a_6370_: *mut crate::leanh::LeanObject,
    mut v_a_6371_: *mut crate::leanh::LeanObject,
    mut v_a_6372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6376_: u8 = 0;
    v___x_6374_ = lean_st_ref_get(v_a_6372_);
    v_infoState_6375_ = crate::leanh::lean_ctor_get(v___x_6374_, 7);
    crate::leanh::lean_inc_ref(v_infoState_6375_);
    crate::leanh::lean_dec(v___x_6374_);
    v_enabled_6376_ = crate::leanh::lean_ctor_get_uint8(
        v_infoState_6375_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_infoState_6375_);
    if v_enabled_6376_ == 0 {
        let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_structName_6366_);
        v___x_6377_ = crate::leanh::lean_box(0);
        v___x_6378_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6378_, 0, v___x_6377_);
        return v___x_6378_;
    } else {
        let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_env_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6381_: u8 = 0;
        v___x_6379_ = lean_st_ref_get(v_a_6372_);
        v_env_6380_ = crate::leanh::lean_ctor_get(v___x_6379_, 0);
        crate::leanh::lean_inc_ref(v_env_6380_);
        crate::leanh::lean_dec(v___x_6379_);
        crate::leanh::lean_inc(v_structName_6366_);
        v___x_6381_ = l_Lean_Environment_contains(v_env_6380_, v_structName_6366_, v_enabled_6376_);
        if v___x_6381_ == 0 {
            let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_structName_6366_);
            v___x_6382_ = crate::leanh::lean_box(0);
            v___x_6383_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6383_, 0, v___x_6382_);
            return v___x_6383_;
        } else {
            let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6384_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_6365_);
            v___x_6385_ = l_Lean_Syntax_getId(v___x_6384_);
            v___x_6386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6386_, 0, v___x_6385_);
            v___x_6387_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once
                ),
                _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2,
            );
            v___x_6388_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6388_, 0, v___x_6384_);
            crate::leanh::lean_ctor_set(v___x_6388_, 1, v___x_6386_);
            crate::leanh::lean_ctor_set(v___x_6388_, 2, v___x_6387_);
            crate::leanh::lean_ctor_set(v___x_6388_, 3, v_structName_6366_);
            v___x_6389_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_6388_, v_a_6367_, v_a_6368_, v_a_6369_, v_a_6370_, v_a_6371_, v_a_6372_);
            return v___x_6389_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___boxed(
    mut v_item_6390_: *mut crate::leanh::LeanObject,
    mut v_structName_6391_: *mut crate::leanh::LeanObject,
    mut v_a_6392_: *mut crate::leanh::LeanObject,
    mut v_a_6393_: *mut crate::leanh::LeanObject,
    mut v_a_6394_: *mut crate::leanh::LeanObject,
    mut v_a_6395_: *mut crate::leanh::LeanObject,
    mut v_a_6396_: *mut crate::leanh::LeanObject,
    mut v_a_6397_: *mut crate::leanh::LeanObject,
    mut v_a_6398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6399_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(
        v_item_6390_,
        v_structName_6391_,
        v_a_6392_,
        v_a_6393_,
        v_a_6394_,
        v_a_6395_,
        v_a_6396_,
        v_a_6397_,
    );
    crate::leanh::lean_dec(v_a_6397_);
    crate::leanh::lean_dec_ref(v_a_6396_);
    crate::leanh::lean_dec(v_a_6395_);
    crate::leanh::lean_dec_ref(v_a_6394_);
    crate::leanh::lean_dec(v_a_6393_);
    crate::leanh::lean_dec_ref(v_a_6392_);
    crate::leanh::lean_dec_ref(v_item_6390_);
    return v_res_6399_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(
    mut v_cfg_6400_: *mut crate::leanh::LeanObject,
    mut v_withRef_6401_: *mut crate::leanh::LeanObject,
    mut v___x_6402_: *mut crate::leanh::LeanObject,
    mut v_oldRef_6403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_6404_ = l_Lean_replaceRef(v_cfg_6400_, v_oldRef_6403_);
    v___x_6405_ = crate::leanh::lean_apply_3(
        v_withRef_6401_,
        crate::leanh::lean_box(0),
        v_ref_6404_,
        v___x_6402_,
    );
    return v___x_6405_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed(
    mut v_cfg_6406_: *mut crate::leanh::LeanObject,
    mut v_withRef_6407_: *mut crate::leanh::LeanObject,
    mut v___x_6408_: *mut crate::leanh::LeanObject,
    mut v_oldRef_6409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6410_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(
        v_cfg_6406_,
        v_withRef_6407_,
        v___x_6408_,
        v_oldRef_6409_,
    );
    crate::leanh::lean_dec(v_oldRef_6409_);
    crate::leanh::lean_dec(v_cfg_6406_);
    return v_res_6410_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(mut v_x_6411_: u32) -> u8 {
    let mut v___x_6412_: u32 = 0;
    let mut v___x_6413_: u8 = 0;
    v___x_6412_ = 46;
    v___x_6413_ = lean_uint32_dec_eq(v_x_6411_, v___x_6412_);
    return v___x_6413_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed(
    mut v_x_6414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1685__boxed_6415_: u32 = 0;
    let mut v_res_6416_: u8 = 0;
    let mut v_r_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1685__boxed_6415_ = crate::leanh::lean_unbox_uint32(v_x_6414_);
    crate::leanh::lean_dec(v_x_6414_);
    v_res_6416_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(v_x_1685__boxed_6415_);
    v_r_6417_ = crate::leanh::lean_box((v_res_6416_) as usize);
    return v_r_6417_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2(
    mut v___f_6418_: *mut crate::leanh::LeanObject,
    mut v_s_6419_: *mut crate::leanh::LeanObject,
    mut v___y_6420_: *mut crate::leanh::LeanObject,
    mut v___y_6421_: *mut crate::leanh::LeanObject,
    mut v___y_6422_: *mut crate::leanh::LeanObject,
    mut v___y_6423_: *mut crate::leanh::LeanObject,
    mut v___y_6424_: *mut crate::leanh::LeanObject,
    mut v___y_6425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6426_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_6418_);
    v___x_6427_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_6419_, v___x_6426_, v___y_6420_, crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___y_6423_, v___y_6424_, v___y_6425_);
    return v___x_6427_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(
    mut v___f_6429_: *mut crate::leanh::LeanObject,
    mut v_si_6430_: *mut crate::leanh::LeanObject,
    mut v_val_6431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: u8 = 0;
    let mut v___x_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6439_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0;
                v___x_6440_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6441_ = lean_string_utf8_byte_size(v_val_6431_);
                crate::leanh::lean_inc_ref(v_val_6431_);
                v___x_6442_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6442_, 0, v_val_6431_);
                crate::leanh::lean_ctor_set(v___x_6442_, 1, v___x_6440_);
                crate::leanh::lean_ctor_set(v___x_6442_, 2, v___x_6441_);
                v___x_6443_ =
                    l_String_Slice_contains___redArg(v___f_6429_, v___x_6442_, v___f_6439_);
                if v___x_6443_ == 0 {
                    v___x_6444_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_val_6431_);
                    v___x_6445_ = l_Lean_Name_str___override(v___x_6444_, v_val_6431_);
                    v___y_6433_ = v___x_6445_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_val_6431_);
                    v___x_6446_ = l_String_toName(v_val_6431_);
                    v___y_6433_ = v___x_6446_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6434_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6435_ = lean_string_utf8_byte_size(v_val_6431_);
                v___x_6436_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6436_, 0, v_val_6431_);
                crate::leanh::lean_ctor_set(v___x_6436_, 1, v___x_6434_);
                crate::leanh::lean_ctor_set(v___x_6436_, 2, v___x_6435_);
                v___x_6437_ = crate::leanh::lean_box(0);
                v___x_6438_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6438_, 0, v_si_6430_);
                crate::leanh::lean_ctor_set(v___x_6438_, 1, v___x_6436_);
                crate::leanh::lean_ctor_set(v___x_6438_, 2, v___y_6433_);
                crate::leanh::lean_ctor_set(v___x_6438_, 3, v___x_6437_);
                return v___x_6438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(
    mut v_atomAsIdent_6447_: *mut crate::leanh::LeanObject,
    mut v_stx_6448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_stx_6448_) {
        3 => {
            let mut v___x_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_atomAsIdent_6447_);
            v___x_6449_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6449_, 0, v_stx_6448_);
            return v___x_6449_;
        }
        2 => {
            let mut v_info_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_info_6450_ = crate::leanh::lean_ctor_get(v_stx_6448_, 0);
            crate::leanh::lean_inc(v_info_6450_);
            v_val_6451_ = crate::leanh::lean_ctor_get(v_stx_6448_, 1);
            crate::leanh::lean_inc_ref(v_val_6451_);
            crate::leanh::lean_dec_ref_known(v_stx_6448_, 2);
            v___x_6452_ =
                crate::leanh::lean_apply_2(v_atomAsIdent_6447_, v_info_6450_, v_val_6451_);
            v___x_6453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6453_, 0, v___x_6452_);
            return v___x_6453_;
        }
        _ => {
            let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_stx_6448_);
            crate::leanh::lean_dec_ref(v_atomAsIdent_6447_);
            v___x_6454_ = crate::leanh::lean_box(0);
            return v___x_6454_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___redArg(
    mut v_inst_6478_: *mut crate::leanh::LeanObject,
    mut v_inst_6479_: *mut crate::leanh::LeanObject,
    mut v_init_6480_: *mut crate::leanh::LeanObject,
    mut v_cfgs_6481_: *mut crate::leanh::LeanObject,
    mut v_k_6482_: *mut crate::leanh::LeanObject,
    mut v_onErr_6483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: u8 = 0;
    v___x_6484_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6485_ = lean_array_get_size(v_cfgs_6481_);
    v___x_6486_ = lean_nat_dec_lt(v___x_6484_, v___x_6485_);
    if v___x_6486_ == 0 {
        let mut v_toApplicative_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_onErr_6483_);
        crate::leanh::lean_dec(v_k_6482_);
        crate::leanh::lean_dec_ref(v_cfgs_6481_);
        crate::leanh::lean_dec_ref(v_inst_6479_);
        v_toApplicative_6487_ = crate::leanh::lean_ctor_get(v_inst_6478_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_6487_);
        crate::leanh::lean_dec_ref(v_inst_6478_);
        v_toPure_6488_ = crate::leanh::lean_ctor_get(v_toApplicative_6487_, 1);
        crate::leanh::lean_inc(v_toPure_6488_);
        crate::leanh::lean_dec_ref(v_toApplicative_6487_);
        v___x_6489_ =
            crate::leanh::lean_apply_2(v_toPure_6488_, crate::leanh::lean_box(0), v_init_6480_);
        return v___x_6489_;
    } else {
        let mut v___f_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6491_: u8 = 0;
        crate::leanh::lean_inc_ref(v_inst_6478_);
        v___f_6490_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0 as *mut core::ffi::c_void,
            6,
            4,
        );
        crate::leanh::lean_closure_set(v___f_6490_, 0, v_inst_6478_);
        crate::leanh::lean_closure_set(v___f_6490_, 1, v_inst_6479_);
        crate::leanh::lean_closure_set(v___f_6490_, 2, v_k_6482_);
        crate::leanh::lean_closure_set(v___f_6490_, 3, v_onErr_6483_);
        v___x_6491_ = lean_nat_dec_le(v___x_6485_, v___x_6485_);
        if v___x_6491_ == 0 {
            if v___x_6486_ == 0 {
                let mut v_toApplicative_6492_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_6490_);
                crate::leanh::lean_dec_ref(v_cfgs_6481_);
                v_toApplicative_6492_ = crate::leanh::lean_ctor_get(v_inst_6478_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_6492_);
                crate::leanh::lean_dec_ref(v_inst_6478_);
                v_toPure_6493_ = crate::leanh::lean_ctor_get(v_toApplicative_6492_, 1);
                crate::leanh::lean_inc(v_toPure_6493_);
                crate::leanh::lean_dec_ref(v_toApplicative_6492_);
                v___x_6494_ = crate::leanh::lean_apply_2(
                    v_toPure_6493_,
                    crate::leanh::lean_box(0),
                    v_init_6480_,
                );
                return v___x_6494_;
            } else {
                let mut v___x_6495_: usize = 0;
                let mut v___x_6496_: usize = 0;
                let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6495_ = 0usize;
                v___x_6496_ = lean_usize_of_nat(v___x_6485_);
                v___x_6497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_6478_,
                    v___f_6490_,
                    v_cfgs_6481_,
                    v___x_6495_,
                    v___x_6496_,
                    v_init_6480_,
                );
                return v___x_6497_;
            }
        } else {
            let mut v___x_6498_: usize = 0;
            let mut v___x_6499_: usize = 0;
            let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6498_ = 0usize;
            v___x_6499_ = lean_usize_of_nat(v___x_6485_);
            v___x_6500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_6478_,
                v___f_6490_,
                v_cfgs_6481_,
                v___x_6498_,
                v___x_6499_,
                v_init_6480_,
            );
            return v___x_6500_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg(
    mut v_inst_6501_: *mut crate::leanh::LeanObject,
    mut v_inst_6502_: *mut crate::leanh::LeanObject,
    mut v_init_6503_: *mut crate::leanh::LeanObject,
    mut v_cfg_6504_: *mut crate::leanh::LeanObject,
    mut v_k_6505_: *mut crate::leanh::LeanObject,
    mut v_onErr_6506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRef_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: u8 = 0;
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: u8 = 0;
    let mut v___f_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atomAsIdent_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: u8 = 0;
    let mut v_info_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6551_: u8 = 0;
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: u8 = 0;
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: u8 = 0;
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: u8 = 0;
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: u8 = 0;
    let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: u8 = 0;
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6525_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1;
                crate::leanh::lean_inc(v_cfg_6504_);
                v___x_6526_ = l_Lean_Syntax_isOfKind(v_cfg_6504_, v___x_6525_);
                if v___x_6526_ == 0 {
                    v___x_6527_ = l_Lean_Syntax_getNumArgs(v_cfg_6504_);
                    v___x_6528_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6529_ = lean_nat_dec_eq(v___x_6527_, v___x_6528_);
                    if v___x_6529_ == 0 {
                        v___f_6530_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3;
                        v_atomAsIdent_6531_ =
                            l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4;
                        v___x_6532_ = lean_nat_dec_le(v___x_6528_, v___x_6527_);
                        if v___x_6532_ == 0 {
                            crate::leanh::lean_dec(v___x_6527_);
                            if crate::leanh::lean_obj_tag(v_cfg_6504_) == 2 {
                                crate::leanh::lean_dec(v_onErr_6506_);
                                crate::leanh::lean_dec_ref(v_inst_6502_);
                                crate::leanh::lean_dec_ref(v_inst_6501_);
                                v_info_6533_ = crate::leanh::lean_ctor_get(v_cfg_6504_, 0);
                                v_val_6534_ = crate::leanh::lean_ctor_get(v_cfg_6504_, 1);
                                crate::leanh::lean_inc_ref(v_val_6534_);
                                crate::leanh::lean_inc(v_info_6533_);
                                v___x_6535_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(
                                    v___f_6530_,
                                    v_info_6533_,
                                    v_val_6534_,
                                );
                                v___x_6536_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7;
                                v___x_6537_ =
                                    l_Lean_mkCIdentFrom(v_cfg_6504_, v___x_6536_, v___x_6529_);
                                v___x_6538_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8;
                                v___x_6539_ = l_Lean_TSyntax_getId(v___x_6535_);
                                v___x_6540_ = lean_erase_macro_scopes(v___x_6539_);
                                v___x_6541_ = crate::leanh::lean_box(0);
                                crate::leanh::lean_inc(v___x_6535_);
                                v___x_6542_ =
                                    l_Lean_Syntax_identComponents(v___x_6535_, v___x_6541_);
                                v___x_6543_ = crate::leanh::lean_box(0);
                                v___x_6544_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6544_, 0, v_cfg_6504_);
                                crate::leanh::lean_ctor_set(v___x_6544_, 1, v___x_6535_);
                                crate::leanh::lean_ctor_set(v___x_6544_, 2, v___x_6537_);
                                crate::leanh::lean_ctor_set(v___x_6544_, 3, v___x_6538_);
                                crate::leanh::lean_ctor_set(v___x_6544_, 4, v___x_6540_);
                                crate::leanh::lean_ctor_set(v___x_6544_, 5, v___x_6542_);
                                crate::leanh::lean_ctor_set(v___x_6544_, 6, v___x_6543_);
                                v___x_6545_ = crate::leanh::lean_apply_2(
                                    v_k_6505_,
                                    v_init_6503_,
                                    v___x_6544_,
                                );
                                return v___x_6545_;
                            } else {
                                crate::leanh::lean_dec(v_k_6505_);
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_6546_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_6547_ = l_Lean_Syntax_getArg(v_cfg_6504_, v___x_6546_);
                            if crate::leanh::lean_obj_tag(v___x_6547_) == 2 {
                                v_val_6548_ = crate::leanh::lean_ctor_get(v___x_6547_, 1);
                                crate::leanh::lean_inc_ref(v_val_6548_);
                                v___x_6562_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11;
                                v___x_6563_ = lean_string_dec_eq(v_val_6548_, v___x_6562_);
                                if v___x_6563_ == 0 {
                                    v___x_6564_ =
                                        l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12;
                                    v___x_6565_ = lean_string_dec_eq(v_val_6548_, v___x_6564_);
                                    if v___x_6565_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_6547_, 2);
                                        v___x_6566_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13;
                                        v___x_6567_ = lean_string_dec_eq(v_val_6548_, v___x_6566_);
                                        crate::leanh::lean_dec_ref(v_val_6548_);
                                        if v___x_6567_ == 0 {
                                            crate::leanh::lean_dec(v___x_6527_);
                                            crate::leanh::lean_dec(v_k_6505_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_6568_ = crate::leanh::lean_unsigned_to_nat(5);
                                            v___x_6569_ = lean_nat_dec_le(v___x_6527_, v___x_6568_);
                                            crate::leanh::lean_dec(v___x_6527_);
                                            if v___x_6569_ == 0 {
                                                crate::leanh::lean_dec(v_k_6505_);
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_6570_ =
                                                    l_Lean_Syntax_getArg(v_cfg_6504_, v___x_6528_);
                                                v___x_6571_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_6531_, v___x_6570_);
                                                if crate::leanh::lean_obj_tag(v___x_6571_) == 1 {
                                                    crate::leanh::lean_dec(v_onErr_6506_);
                                                    crate::leanh::lean_dec_ref(v_inst_6502_);
                                                    crate::leanh::lean_dec_ref(v_inst_6501_);
                                                    v_val_6572_ =
                                                        crate::leanh::lean_ctor_get(v___x_6571_, 0);
                                                    crate::leanh::lean_inc_n(v_val_6572_, 2);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_6571_,
                                                        1,
                                                    );
                                                    v___x_6573_ =
                                                        crate::leanh::lean_unsigned_to_nat(3);
                                                    v___x_6574_ = l_Lean_Syntax_getArg(
                                                        v_cfg_6504_,
                                                        v___x_6573_,
                                                    );
                                                    v___x_6575_ = crate::leanh::lean_box(0);
                                                    v___x_6576_ = l_Lean_TSyntax_getId(v_val_6572_);
                                                    v___x_6577_ =
                                                        lean_erase_macro_scopes(v___x_6576_);
                                                    v___x_6578_ = l_Lean_Syntax_identComponents(
                                                        v_val_6572_,
                                                        v___x_6575_,
                                                    );
                                                    v___x_6579_ = crate::leanh::lean_box(0);
                                                    v___x_6580_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        7,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        0,
                                                        v_cfg_6504_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        1,
                                                        v_val_6572_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        2,
                                                        v___x_6574_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        3,
                                                        v___x_6575_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        4,
                                                        v___x_6577_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        5,
                                                        v___x_6578_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        6,
                                                        v___x_6579_,
                                                    );
                                                    v___x_6581_ = crate::leanh::lean_apply_2(
                                                        v_k_6505_,
                                                        v_init_6503_,
                                                        v___x_6580_,
                                                    );
                                                    return v___x_6581_;
                                                } else {
                                                    crate::leanh::lean_dec(v___x_6571_);
                                                    crate::leanh::lean_dec(v_k_6505_);
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_val_6548_);
                                        v___x_6582_ =
                                            crate::leanh::lean_box((v___x_6529_) as usize);
                                        v___x_6583_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_6583_, 0, v___x_6582_);
                                        v___y_6550_ = v___x_6583_;
                                        v_val_6551_ = v___x_6529_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_val_6548_);
                                    v___x_6584_ = crate::leanh::lean_box((v___x_6563_) as usize);
                                    v___x_6585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6585_, 0, v___x_6584_);
                                    v___y_6550_ = v___x_6585_;
                                    v_val_6551_ = v___x_6563_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_6547_);
                                crate::leanh::lean_dec(v___x_6527_);
                                crate::leanh::lean_dec(v_k_6505_);
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6527_);
                        v___x_6586_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6587_ = l_Lean_Syntax_getArg(v_cfg_6504_, v___x_6586_);
                        crate::leanh::lean_dec(v_cfg_6504_);
                        v_cfg_6504_ = v___x_6587_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_6589_ = l_Lean_Syntax_getArgs(v_cfg_6504_);
                    crate::leanh::lean_dec(v_cfg_6504_);
                    v___x_6590_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(
                        v_inst_6501_,
                        v_inst_6502_,
                        v_init_6503_,
                        v___x_6589_,
                        v_k_6505_,
                        v_onErr_6506_,
                    );
                    return v___x_6590_;
                }
            }
            1 => {
                v___x_6511_ = l_Lean_TSyntax_getId(v___y_6508_);
                v___x_6512_ = lean_erase_macro_scopes(v___x_6511_);
                v___x_6513_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_6508_);
                v___x_6514_ = l_Lean_Syntax_identComponents(v___y_6508_, v___x_6513_);
                v___x_6515_ = crate::leanh::lean_box(0);
                v___x_6516_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6516_, 0, v_cfg_6504_);
                crate::leanh::lean_ctor_set(v___x_6516_, 1, v___y_6508_);
                crate::leanh::lean_ctor_set(v___x_6516_, 2, v___y_6510_);
                crate::leanh::lean_ctor_set(v___x_6516_, 3, v___y_6509_);
                crate::leanh::lean_ctor_set(v___x_6516_, 4, v___x_6512_);
                crate::leanh::lean_ctor_set(v___x_6516_, 5, v___x_6514_);
                crate::leanh::lean_ctor_set(v___x_6516_, 6, v___x_6515_);
                v___x_6517_ = crate::leanh::lean_apply_2(v_k_6505_, v_init_6503_, v___x_6516_);
                return v___x_6517_;
            }
            2 => {
                v_toBind_6519_ = crate::leanh::lean_ctor_get(v_inst_6501_, 1);
                crate::leanh::lean_inc(v_toBind_6519_);
                crate::leanh::lean_dec_ref(v_inst_6501_);
                v_getRef_6520_ = crate::leanh::lean_ctor_get(v_inst_6502_, 0);
                crate::leanh::lean_inc(v_getRef_6520_);
                v_withRef_6521_ = crate::leanh::lean_ctor_get(v_inst_6502_, 1);
                crate::leanh::lean_inc(v_withRef_6521_);
                crate::leanh::lean_dec_ref(v_inst_6502_);
                crate::leanh::lean_inc(v_cfg_6504_);
                v___x_6522_ = crate::leanh::lean_apply_2(v_onErr_6506_, v_init_6503_, v_cfg_6504_);
                v___f_6523_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_6523_, 0, v_cfg_6504_);
                crate::leanh::lean_closure_set(v___f_6523_, 1, v_withRef_6521_);
                crate::leanh::lean_closure_set(v___f_6523_, 2, v___x_6522_);
                v___x_6524_ = crate::leanh::lean_apply_4(
                    v_toBind_6519_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_getRef_6520_,
                    v___f_6523_,
                );
                return v___x_6524_;
            }
            3 => {
                v___x_6552_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6553_ = lean_nat_dec_eq(v___x_6527_, v___x_6552_);
                crate::leanh::lean_dec(v___x_6527_);
                if v___x_6553_ == 0 {
                    crate::leanh::lean_dec(v___y_6550_);
                    crate::leanh::lean_dec_ref_known(v___x_6547_, 2);
                    crate::leanh::lean_dec(v_k_6505_);
                    state = 2;
                    continue;
                } else {
                    v___x_6554_ = l_Lean_Syntax_getArg(v_cfg_6504_, v___x_6528_);
                    v___x_6555_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(
                        v_atomAsIdent_6531_,
                        v___x_6554_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6555_) == 1 {
                        crate::leanh::lean_dec(v_onErr_6506_);
                        crate::leanh::lean_dec_ref(v_inst_6502_);
                        crate::leanh::lean_dec_ref(v_inst_6501_);
                        if v_val_6551_ == 0 {
                            v_val_6556_ = crate::leanh::lean_ctor_get(v___x_6555_, 0);
                            crate::leanh::lean_inc(v_val_6556_);
                            crate::leanh::lean_dec_ref_known(v___x_6555_, 1);
                            v___x_6557_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10;
                            v___x_6558_ =
                                l_Lean_mkCIdentFrom(v___x_6547_, v___x_6557_, v___x_6529_);
                            crate::leanh::lean_dec_ref_known(v___x_6547_, 2);
                            v___y_6508_ = v_val_6556_;
                            v___y_6509_ = v___y_6550_;
                            v___y_6510_ = v___x_6558_;
                            state = 1;
                            continue;
                        } else {
                            v_val_6559_ = crate::leanh::lean_ctor_get(v___x_6555_, 0);
                            crate::leanh::lean_inc(v_val_6559_);
                            crate::leanh::lean_dec_ref_known(v___x_6555_, 1);
                            v___x_6560_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7;
                            v___x_6561_ =
                                l_Lean_mkCIdentFrom(v___x_6547_, v___x_6560_, v___x_6529_);
                            crate::leanh::lean_dec_ref_known(v___x_6547_, 2);
                            v___y_6508_ = v_val_6559_;
                            v___y_6509_ = v___y_6550_;
                            v___y_6510_ = v___x_6561_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6555_);
                        crate::leanh::lean_dec(v___y_6550_);
                        crate::leanh::lean_dec_ref_known(v___x_6547_, 2);
                        crate::leanh::lean_dec(v_k_6505_);
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0(
    mut v_inst_6591_: *mut crate::leanh::LeanObject,
    mut v_inst_6592_: *mut crate::leanh::LeanObject,
    mut v_k_6593_: *mut crate::leanh::LeanObject,
    mut v_onErr_6594_: *mut crate::leanh::LeanObject,
    mut v_x_6595_: *mut crate::leanh::LeanObject,
    mut v_cfg_x27_6596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6597_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(
        v_inst_6591_,
        v_inst_6592_,
        v_x_6595_,
        v_cfg_x27_6596_,
        v_k_6593_,
        v_onErr_6594_,
    );
    return v___x_6597_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM(
    mut v_00_u03b1_6598_: *mut crate::leanh::LeanObject,
    mut v_m_6599_: *mut crate::leanh::LeanObject,
    mut v_inst_6600_: *mut crate::leanh::LeanObject,
    mut v_inst_6601_: *mut crate::leanh::LeanObject,
    mut v_init_6602_: *mut crate::leanh::LeanObject,
    mut v_cfg_6603_: *mut crate::leanh::LeanObject,
    mut v_k_6604_: *mut crate::leanh::LeanObject,
    mut v_onErr_6605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6606_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(
        v_inst_6600_,
        v_inst_6601_,
        v_init_6602_,
        v_cfg_6603_,
        v_k_6604_,
        v_onErr_6605_,
    );
    return v___x_6606_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM(
    mut v_00_u03b1_6607_: *mut crate::leanh::LeanObject,
    mut v_m_6608_: *mut crate::leanh::LeanObject,
    mut v_inst_6609_: *mut crate::leanh::LeanObject,
    mut v_inst_6610_: *mut crate::leanh::LeanObject,
    mut v_init_6611_: *mut crate::leanh::LeanObject,
    mut v_cfgs_6612_: *mut crate::leanh::LeanObject,
    mut v_k_6613_: *mut crate::leanh::LeanObject,
    mut v_onErr_6614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6615_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(
        v_inst_6609_,
        v_inst_6610_,
        v_init_6611_,
        v_cfgs_6612_,
        v_k_6613_,
        v_onErr_6614_,
    );
    return v___x_6615_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(
    mut v___y_6624_: u8,
    mut v_suppressElabErrors_6625_: u8,
    mut v_x_6626_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_6626_) == 1 {
        let mut v_pre_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_6627_ = crate::leanh::lean_ctor_get(v_x_6626_, 0);
        match crate::leanh::lean_obj_tag(v_pre_6627_) {
            1 => {
                let mut v_pre_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_6628_ = crate::leanh::lean_ctor_get(v_pre_6627_, 0);
                match crate::leanh::lean_obj_tag(v_pre_6628_) {
                    0 => {
                        let mut v_str_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_6632_: u8 = 0;
                        v_str_6629_ = crate::leanh::lean_ctor_get(v_x_6626_, 1);
                        v_str_6630_ = crate::leanh::lean_ctor_get(v_pre_6627_, 1);
                        v___x_6631_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0;
                        v___x_6632_ = lean_string_dec_eq(v_str_6630_, v___x_6631_);
                        if v___x_6632_ == 0 {
                            let mut v___x_6633_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6634_: u8 = 0;
                            v___x_6633_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1;
                            v___x_6634_ = lean_string_dec_eq(v_str_6630_, v___x_6633_);
                            if v___x_6634_ == 0 {
                                return v___y_6624_;
                            } else {
                                let mut v___x_6635_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_6636_: u8 = 0;
                                v___x_6635_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2;
                                v___x_6636_ = lean_string_dec_eq(v_str_6629_, v___x_6635_);
                                if v___x_6636_ == 0 {
                                    return v___y_6624_;
                                } else {
                                    return v_suppressElabErrors_6625_;
                                }
                            }
                        } else {
                            let mut v___x_6637_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6638_: u8 = 0;
                            v___x_6637_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3;
                            v___x_6638_ = lean_string_dec_eq(v_str_6629_, v___x_6637_);
                            if v___x_6638_ == 0 {
                                return v___y_6624_;
                            } else {
                                return v_suppressElabErrors_6625_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_6639_ = crate::leanh::lean_ctor_get(v_pre_6628_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_6639_) == 0 {
                            let mut v_str_6640_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_6641_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_6642_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6643_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6644_: u8 = 0;
                            v_str_6640_ = crate::leanh::lean_ctor_get(v_x_6626_, 1);
                            v_str_6641_ = crate::leanh::lean_ctor_get(v_pre_6627_, 1);
                            v_str_6642_ = crate::leanh::lean_ctor_get(v_pre_6628_, 1);
                            v___x_6643_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4;
                            v___x_6644_ = lean_string_dec_eq(v_str_6642_, v___x_6643_);
                            if v___x_6644_ == 0 {
                                return v___y_6624_;
                            } else {
                                let mut v___x_6645_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_6646_: u8 = 0;
                                v___x_6645_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5;
                                v___x_6646_ = lean_string_dec_eq(v_str_6641_, v___x_6645_);
                                if v___x_6646_ == 0 {
                                    return v___y_6624_;
                                } else {
                                    let mut v___x_6647_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_6648_: u8 = 0;
                                    v___x_6647_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6;
                                    v___x_6648_ = lean_string_dec_eq(v_str_6640_, v___x_6647_);
                                    if v___x_6648_ == 0 {
                                        return v___y_6624_;
                                    } else {
                                        return v_suppressElabErrors_6625_;
                                    }
                                }
                            }
                        } else {
                            return v___y_6624_;
                        }
                    }
                    _ => {
                        return v___y_6624_;
                    }
                }
            }
            0 => {
                let mut v_str_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6651_: u8 = 0;
                v_str_6649_ = crate::leanh::lean_ctor_get(v_x_6626_, 1);
                v___x_6650_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7;
                v___x_6651_ = lean_string_dec_eq(v_str_6649_, v___x_6650_);
                if v___x_6651_ == 0 {
                    return v___y_6624_;
                } else {
                    return v_suppressElabErrors_6625_;
                }
            }
            _ => {
                return v___y_6624_;
            }
        }
    } else {
        return v___y_6624_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed(
    mut v___y_6652_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_6653_: *mut crate::leanh::LeanObject,
    mut v_x_6654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6697__boxed_6655_: u8 = 0;
    let mut v_suppressElabErrors_boxed_6656_: u8 = 0;
    let mut v_res_6657_: u8 = 0;
    let mut v_r_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_6697__boxed_6655_ = (crate::leanh::lean_unbox(v___y_6652_) as u8);
    v_suppressElabErrors_boxed_6656_ = (crate::leanh::lean_unbox(v_suppressElabErrors_6653_) as u8);
    v_res_6657_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(v___y_6697__boxed_6655_, v_suppressElabErrors_boxed_6656_, v_x_6654_);
    crate::leanh::lean_dec(v_x_6654_);
    v_r_6658_ = crate::leanh::lean_box((v_res_6657_) as usize);
    return v_r_6658_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(
    mut v_ref_6659_: *mut crate::leanh::LeanObject,
    mut v_msgData_6660_: *mut crate::leanh::LeanObject,
    mut v_severity_6661_: u8,
    mut v_isSilent_6662_: u8,
    mut v___y_6663_: *mut crate::leanh::LeanObject,
    mut v___y_6664_: *mut crate::leanh::LeanObject,
    mut v___y_6665_: *mut crate::leanh::LeanObject,
    mut v___y_6666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6672_: u8 = 0;
    let mut v___y_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6674_: u8 = 0;
    let mut v___y_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6692_: u8 = 0;
    let mut v___x_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6703_: u8 = 0;
    let mut v___y_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6707_: u8 = 0;
    let mut v___y_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6709_: u8 = 0;
    let mut v___y_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6711_: u8 = 0;
    let mut v___y_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6718_: u8 = 0;
    let mut v___x_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: u8 = 0;
    let mut v___x_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6728_: u8 = 0;
    let mut v___y_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6733_: u8 = 0;
    let mut v___y_6734_: u8 = 0;
    let mut v___y_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6736_: u8 = 0;
    let mut v___y_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6742_: u8 = 0;
    let mut v___y_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6744_: u8 = 0;
    let mut v___y_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6747_: u8 = 0;
    let mut v_ref_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: u8 = 0;
    let mut v___y_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6756_: u8 = 0;
    let mut v___y_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6759_: u8 = 0;
    let mut v___y_6760_: u8 = 0;
    let mut v___y_6762_: u8 = 0;
    let mut v_fileName_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6767_: u8 = 0;
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: u8 = 0;
    let mut v___x_6772_: u8 = 0;
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: u8 = 0;
    let mut v___x_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: u8 = 0;
    let mut v___x_6778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6752_ = 2;
                v___x_6777_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6661_, v___x_6752_);
                if v___x_6777_ == 0 {
                    v___y_6762_ = v___x_6777_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_6660_);
                    v___x_6778_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6660_);
                    v___y_6762_ = v___x_6778_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_6678_ = lean_st_ref_take(v___y_6677_);
                v_currNamespace_6679_ = crate::leanh::lean_ctor_get(v___y_6676_, 6);
                v_openDecls_6680_ = crate::leanh::lean_ctor_get(v___y_6676_, 7);
                v_env_6681_ = crate::leanh::lean_ctor_get(v___x_6678_, 0);
                v_nextMacroScope_6682_ = crate::leanh::lean_ctor_get(v___x_6678_, 1);
                v_ngen_6683_ = crate::leanh::lean_ctor_get(v___x_6678_, 2);
                v_auxDeclNGen_6684_ = crate::leanh::lean_ctor_get(v___x_6678_, 3);
                v_traceState_6685_ = crate::leanh::lean_ctor_get(v___x_6678_, 4);
                v_cache_6686_ = crate::leanh::lean_ctor_get(v___x_6678_, 5);
                v_messages_6687_ = crate::leanh::lean_ctor_get(v___x_6678_, 6);
                v_infoState_6688_ = crate::leanh::lean_ctor_get(v___x_6678_, 7);
                v_snapshotTasks_6689_ = crate::leanh::lean_ctor_get(v___x_6678_, 8);
                v_isSharedCheck_6703_ = (!crate::leanh::lean_is_exclusive(v___x_6678_)) as u8;
                if v_isSharedCheck_6703_ == 0 {
                    v___x_6691_ = v___x_6678_;
                    v_isShared_6692_ = v_isSharedCheck_6703_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6689_);
                    crate::leanh::lean_inc(v_infoState_6688_);
                    crate::leanh::lean_inc(v_messages_6687_);
                    crate::leanh::lean_inc(v_cache_6686_);
                    crate::leanh::lean_inc(v_traceState_6685_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6684_);
                    crate::leanh::lean_inc(v_ngen_6683_);
                    crate::leanh::lean_inc(v_nextMacroScope_6682_);
                    crate::leanh::lean_inc(v_env_6681_);
                    crate::leanh::lean_dec(v___x_6678_);
                    v___x_6691_ = crate::leanh::lean_box(0);
                    v_isShared_6692_ = v_isSharedCheck_6703_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_6680_);
                crate::leanh::lean_inc(v_currNamespace_6679_);
                v___x_6693_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6693_, 0, v_currNamespace_6679_);
                crate::leanh::lean_ctor_set(v___x_6693_, 1, v_openDecls_6680_);
                v___x_6694_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6694_, 0, v___x_6693_);
                crate::leanh::lean_ctor_set(v___x_6694_, 1, v___y_6669_);
                crate::leanh::lean_inc_ref(v___y_6671_);
                crate::leanh::lean_inc_ref(v___y_6673_);
                v___x_6695_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_6695_, 0, v___y_6673_);
                crate::leanh::lean_ctor_set(v___x_6695_, 1, v___y_6670_);
                crate::leanh::lean_ctor_set(v___x_6695_, 2, v___y_6675_);
                crate::leanh::lean_ctor_set(v___x_6695_, 3, v___y_6671_);
                crate::leanh::lean_ctor_set(v___x_6695_, 4, v___x_6694_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6695_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_6672_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6695_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_6674_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6695_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_6662_,
                );
                v___x_6696_ = l_Lean_MessageLog_add(v___x_6695_, v_messages_6687_);
                if v_isShared_6692_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6691_, 6, v___x_6696_);
                    v___x_6698_ = v___x_6691_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6702_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 0, v_env_6681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 1, v_nextMacroScope_6682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 2, v_ngen_6683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 3, v_auxDeclNGen_6684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 4, v_traceState_6685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 5, v_cache_6686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 6, v___x_6696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 7, v_infoState_6688_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 8, v_snapshotTasks_6689_);
                    v___x_6698_ = v_reuseFailAlloc_6702_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6699_ = lean_st_ref_set(v___y_6677_, v___x_6698_);
                v___x_6700_ = crate::leanh::lean_box(0);
                v___x_6701_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6701_, 0, v___x_6700_);
                return v___x_6701_;
            }
            4 => {
                v___x_6713_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_6660_,
                    );
                v___x_6714_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v___x_6713_, v___y_6663_, v___y_6664_, v___y_6665_, v___y_6666_);
                v_a_6715_ = crate::leanh::lean_ctor_get(v___x_6714_, 0);
                v_isSharedCheck_6728_ = (!crate::leanh::lean_is_exclusive(v___x_6714_)) as u8;
                if v_isSharedCheck_6728_ == 0 {
                    v___x_6717_ = v___x_6714_;
                    v_isShared_6718_ = v_isSharedCheck_6728_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6715_);
                    crate::leanh::lean_dec(v___x_6714_);
                    v___x_6717_ = crate::leanh::lean_box(0);
                    v_isShared_6718_ = v_isSharedCheck_6728_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_6708_, 2);
                v___x_6719_ = l_Lean_FileMap_toPosition(v___y_6708_, v___y_6706_);
                crate::leanh::lean_dec(v___y_6706_);
                v___x_6720_ = l_Lean_FileMap_toPosition(v___y_6708_, v___y_6712_);
                crate::leanh::lean_dec(v___y_6712_);
                v___x_6721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6721_, 0, v___x_6720_);
                v___x_6722_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29;
                if v___y_6707_ == 0 {
                    crate::leanh::lean_del_object(v___x_6717_);
                    crate::leanh::lean_dec_ref(v___y_6705_);
                    v___y_6669_ = v_a_6715_;
                    v___y_6670_ = v___x_6719_;
                    v___y_6671_ = v___x_6722_;
                    v___y_6672_ = v___y_6709_;
                    v___y_6673_ = v___y_6710_;
                    v___y_6674_ = v___y_6711_;
                    v___y_6675_ = v___x_6721_;
                    v___y_6676_ = v___y_6665_;
                    v___y_6677_ = v___y_6666_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6715_);
                    v___x_6723_ = l_Lean_MessageData_hasTag(v___y_6705_, v_a_6715_);
                    if v___x_6723_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6721_, 1);
                        crate::leanh::lean_dec_ref(v___x_6719_);
                        crate::leanh::lean_dec(v_a_6715_);
                        v___x_6724_ = crate::leanh::lean_box(0);
                        if v_isShared_6718_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6717_, 0, v___x_6724_);
                            v___x_6726_ = v___x_6717_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_6727_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6727_, 0, v___x_6724_);
                            v___x_6726_ = v_reuseFailAlloc_6727_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6717_);
                        v___y_6669_ = v_a_6715_;
                        v___y_6670_ = v___x_6719_;
                        v___y_6671_ = v___x_6722_;
                        v___y_6672_ = v___y_6709_;
                        v___y_6673_ = v___y_6710_;
                        v___y_6674_ = v___y_6711_;
                        v___y_6675_ = v___x_6721_;
                        v___y_6676_ = v___y_6665_;
                        v___y_6677_ = v___y_6666_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_6726_;
            }
            7 => {
                v___x_6738_ = l_Lean_Syntax_getTailPos_x3f(v___y_6731_, v___y_6734_);
                crate::leanh::lean_dec(v___y_6731_);
                if crate::leanh::lean_obj_tag(v___x_6738_) == 0 {
                    crate::leanh::lean_inc(v___y_6737_);
                    v___y_6705_ = v___y_6730_;
                    v___y_6706_ = v___y_6737_;
                    v___y_6707_ = v___y_6733_;
                    v___y_6708_ = v___y_6732_;
                    v___y_6709_ = v___y_6734_;
                    v___y_6710_ = v___y_6735_;
                    v___y_6711_ = v___y_6736_;
                    v___y_6712_ = v___y_6737_;
                    state = 4;
                    continue;
                } else {
                    v_val_6739_ = crate::leanh::lean_ctor_get(v___x_6738_, 0);
                    crate::leanh::lean_inc(v_val_6739_);
                    crate::leanh::lean_dec_ref_known(v___x_6738_, 1);
                    v___y_6705_ = v___y_6730_;
                    v___y_6706_ = v___y_6737_;
                    v___y_6707_ = v___y_6733_;
                    v___y_6708_ = v___y_6732_;
                    v___y_6709_ = v___y_6734_;
                    v___y_6710_ = v___y_6735_;
                    v___y_6711_ = v___y_6736_;
                    v___y_6712_ = v_val_6739_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_6748_ = l_Lean_replaceRef(v_ref_6659_, v___y_6746_);
                v___x_6749_ = l_Lean_Syntax_getPos_x3f(v_ref_6748_, v___y_6744_);
                if crate::leanh::lean_obj_tag(v___x_6749_) == 0 {
                    v___x_6750_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6730_ = v___y_6741_;
                    v___y_6731_ = v_ref_6748_;
                    v___y_6732_ = v___y_6743_;
                    v___y_6733_ = v___y_6742_;
                    v___y_6734_ = v___y_6744_;
                    v___y_6735_ = v___y_6745_;
                    v___y_6736_ = v___y_6747_;
                    v___y_6737_ = v___x_6750_;
                    state = 7;
                    continue;
                } else {
                    v_val_6751_ = crate::leanh::lean_ctor_get(v___x_6749_, 0);
                    crate::leanh::lean_inc(v_val_6751_);
                    crate::leanh::lean_dec_ref_known(v___x_6749_, 1);
                    v___y_6730_ = v___y_6741_;
                    v___y_6731_ = v_ref_6748_;
                    v___y_6732_ = v___y_6743_;
                    v___y_6733_ = v___y_6742_;
                    v___y_6734_ = v___y_6744_;
                    v___y_6735_ = v___y_6745_;
                    v___y_6736_ = v___y_6747_;
                    v___y_6737_ = v_val_6751_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_6760_ == 0 {
                    v___y_6741_ = v___y_6754_;
                    v___y_6742_ = v___y_6756_;
                    v___y_6743_ = v___y_6755_;
                    v___y_6744_ = v___y_6759_;
                    v___y_6745_ = v___y_6757_;
                    v___y_6746_ = v___y_6758_;
                    v___y_6747_ = v_severity_6661_;
                    state = 8;
                    continue;
                } else {
                    v___y_6741_ = v___y_6754_;
                    v___y_6742_ = v___y_6756_;
                    v___y_6743_ = v___y_6755_;
                    v___y_6744_ = v___y_6759_;
                    v___y_6745_ = v___y_6757_;
                    v___y_6746_ = v___y_6758_;
                    v___y_6747_ = v___x_6752_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_6762_ == 0 {
                    v_fileName_6763_ = crate::leanh::lean_ctor_get(v___y_6665_, 0);
                    v_fileMap_6764_ = crate::leanh::lean_ctor_get(v___y_6665_, 1);
                    v_options_6765_ = crate::leanh::lean_ctor_get(v___y_6665_, 2);
                    v_ref_6766_ = crate::leanh::lean_ctor_get(v___y_6665_, 5);
                    v_suppressElabErrors_6767_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_6665_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_6768_ = crate::leanh::lean_box((v___y_6762_) as usize);
                    v___x_6769_ = crate::leanh::lean_box((v_suppressElabErrors_6767_) as usize);
                    v___f_6770_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_6770_, 0, v___x_6768_);
                    crate::leanh::lean_closure_set(v___f_6770_, 1, v___x_6769_);
                    v___x_6771_ = 1;
                    v___x_6772_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6661_, v___x_6771_);
                    if v___x_6772_ == 0 {
                        v___y_6754_ = v___f_6770_;
                        v___y_6755_ = v_fileMap_6764_;
                        v___y_6756_ = v_suppressElabErrors_6767_;
                        v___y_6757_ = v_fileName_6763_;
                        v___y_6758_ = v_ref_6766_;
                        v___y_6759_ = v___y_6762_;
                        v___y_6760_ = v___x_6772_;
                        state = 9;
                        continue;
                    } else {
                        v___x_6773_ = l_Lean_warningAsError;
                        v___x_6774_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_options_6765_, v___x_6773_);
                        v___y_6754_ = v___f_6770_;
                        v___y_6755_ = v_fileMap_6764_;
                        v___y_6756_ = v_suppressElabErrors_6767_;
                        v___y_6757_ = v_fileName_6763_;
                        v___y_6758_ = v_ref_6766_;
                        v___y_6759_ = v___y_6762_;
                        v___y_6760_ = v___x_6774_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_6660_);
                    v___x_6775_ = crate::leanh::lean_box(0);
                    v___x_6776_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6776_, 0, v___x_6775_);
                    return v___x_6776_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_6779_: *mut crate::leanh::LeanObject,
    mut v_msgData_6780_: *mut crate::leanh::LeanObject,
    mut v_severity_6781_: *mut crate::leanh::LeanObject,
    mut v_isSilent_6782_: *mut crate::leanh::LeanObject,
    mut v___y_6783_: *mut crate::leanh::LeanObject,
    mut v___y_6784_: *mut crate::leanh::LeanObject,
    mut v___y_6785_: *mut crate::leanh::LeanObject,
    mut v___y_6786_: *mut crate::leanh::LeanObject,
    mut v___y_6787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_6788_: u8 = 0;
    let mut v_isSilent_boxed_6789_: u8 = 0;
    let mut v_res_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6788_ = (crate::leanh::lean_unbox(v_severity_6781_) as u8);
    v_isSilent_boxed_6789_ = (crate::leanh::lean_unbox(v_isSilent_6782_) as u8);
    v_res_6790_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_6779_, v_msgData_6780_, v_severity_boxed_6788_, v_isSilent_boxed_6789_, v___y_6783_, v___y_6784_, v___y_6785_, v___y_6786_);
    crate::leanh::lean_dec(v___y_6786_);
    crate::leanh::lean_dec_ref(v___y_6785_);
    crate::leanh::lean_dec(v___y_6784_);
    crate::leanh::lean_dec_ref(v___y_6783_);
    crate::leanh::lean_dec(v_ref_6779_);
    return v_res_6790_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(
    mut v_msgData_6791_: *mut crate::leanh::LeanObject,
    mut v_severity_6792_: u8,
    mut v_isSilent_6793_: u8,
    mut v___y_6794_: *mut crate::leanh::LeanObject,
    mut v___y_6795_: *mut crate::leanh::LeanObject,
    mut v___y_6796_: *mut crate::leanh::LeanObject,
    mut v___y_6797_: *mut crate::leanh::LeanObject,
    mut v___y_6798_: *mut crate::leanh::LeanObject,
    mut v___y_6799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_6801_ = crate::leanh::lean_ctor_get(v___y_6798_, 5);
    v___x_6802_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_6801_, v_msgData_6791_, v_severity_6792_, v_isSilent_6793_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_);
    return v___x_6802_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3___boxed(
    mut v_msgData_6803_: *mut crate::leanh::LeanObject,
    mut v_severity_6804_: *mut crate::leanh::LeanObject,
    mut v_isSilent_6805_: *mut crate::leanh::LeanObject,
    mut v___y_6806_: *mut crate::leanh::LeanObject,
    mut v___y_6807_: *mut crate::leanh::LeanObject,
    mut v___y_6808_: *mut crate::leanh::LeanObject,
    mut v___y_6809_: *mut crate::leanh::LeanObject,
    mut v___y_6810_: *mut crate::leanh::LeanObject,
    mut v___y_6811_: *mut crate::leanh::LeanObject,
    mut v___y_6812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_6813_: u8 = 0;
    let mut v_isSilent_boxed_6814_: u8 = 0;
    let mut v_res_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6813_ = (crate::leanh::lean_unbox(v_severity_6804_) as u8);
    v_isSilent_boxed_6814_ = (crate::leanh::lean_unbox(v_isSilent_6805_) as u8);
    v_res_6815_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_6803_, v_severity_boxed_6813_, v_isSilent_boxed_6814_, v___y_6806_, v___y_6807_, v___y_6808_, v___y_6809_, v___y_6810_, v___y_6811_);
    crate::leanh::lean_dec(v___y_6811_);
    crate::leanh::lean_dec_ref(v___y_6810_);
    crate::leanh::lean_dec(v___y_6809_);
    crate::leanh::lean_dec_ref(v___y_6808_);
    crate::leanh::lean_dec(v___y_6807_);
    crate::leanh::lean_dec_ref(v___y_6806_);
    return v_res_6815_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(
    mut v_msgData_6816_: *mut crate::leanh::LeanObject,
    mut v___y_6817_: *mut crate::leanh::LeanObject,
    mut v___y_6818_: *mut crate::leanh::LeanObject,
    mut v___y_6819_: *mut crate::leanh::LeanObject,
    mut v___y_6820_: *mut crate::leanh::LeanObject,
    mut v___y_6821_: *mut crate::leanh::LeanObject,
    mut v___y_6822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6824_: u8 = 0;
    let mut v___x_6825_: u8 = 0;
    let mut v___x_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6824_ = 2;
    v___x_6825_ = 0;
    v___x_6826_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_6816_, v___x_6824_, v___x_6825_, v___y_6817_, v___y_6818_, v___y_6819_, v___y_6820_, v___y_6821_, v___y_6822_);
    return v___x_6826_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1___boxed(
    mut v_msgData_6827_: *mut crate::leanh::LeanObject,
    mut v___y_6828_: *mut crate::leanh::LeanObject,
    mut v___y_6829_: *mut crate::leanh::LeanObject,
    mut v___y_6830_: *mut crate::leanh::LeanObject,
    mut v___y_6831_: *mut crate::leanh::LeanObject,
    mut v___y_6832_: *mut crate::leanh::LeanObject,
    mut v___y_6833_: *mut crate::leanh::LeanObject,
    mut v___y_6834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6835_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v_msgData_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_, v___y_6833_);
    crate::leanh::lean_dec(v___y_6833_);
    crate::leanh::lean_dec_ref(v___y_6832_);
    crate::leanh::lean_dec(v___y_6831_);
    crate::leanh::lean_dec_ref(v___y_6830_);
    crate::leanh::lean_dec(v___y_6829_);
    crate::leanh::lean_dec_ref(v___y_6828_);
    return v_res_6835_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(
    mut v_ref_6836_: *mut crate::leanh::LeanObject,
    mut v_msgData_6837_: *mut crate::leanh::LeanObject,
    mut v___y_6838_: *mut crate::leanh::LeanObject,
    mut v___y_6839_: *mut crate::leanh::LeanObject,
    mut v___y_6840_: *mut crate::leanh::LeanObject,
    mut v___y_6841_: *mut crate::leanh::LeanObject,
    mut v___y_6842_: *mut crate::leanh::LeanObject,
    mut v___y_6843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6845_: u8 = 0;
    let mut v___x_6846_: u8 = 0;
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6845_ = 2;
    v___x_6846_ = 0;
    v___x_6847_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_6836_, v_msgData_6837_, v___x_6845_, v___x_6846_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_);
    return v___x_6847_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0___boxed(
    mut v_ref_6848_: *mut crate::leanh::LeanObject,
    mut v_msgData_6849_: *mut crate::leanh::LeanObject,
    mut v___y_6850_: *mut crate::leanh::LeanObject,
    mut v___y_6851_: *mut crate::leanh::LeanObject,
    mut v___y_6852_: *mut crate::leanh::LeanObject,
    mut v___y_6853_: *mut crate::leanh::LeanObject,
    mut v___y_6854_: *mut crate::leanh::LeanObject,
    mut v___y_6855_: *mut crate::leanh::LeanObject,
    mut v___y_6856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6857_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_6848_, v_msgData_6849_, v___y_6850_, v___y_6851_, v___y_6852_, v___y_6853_, v___y_6854_, v___y_6855_);
    crate::leanh::lean_dec(v___y_6855_);
    crate::leanh::lean_dec_ref(v___y_6854_);
    crate::leanh::lean_dec(v___y_6853_);
    crate::leanh::lean_dec_ref(v___y_6852_);
    crate::leanh::lean_dec(v___y_6851_);
    crate::leanh::lean_dec_ref(v___y_6850_);
    crate::leanh::lean_dec(v_ref_6848_);
    return v_res_6857_;
}
pub unsafe fn _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6859_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0;
    v___x_6860_ = l_Lean_stringToMessageData(v___x_6859_);
    return v___x_6860_;
}
pub unsafe fn l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(
    mut v_ex_6861_: *mut crate::leanh::LeanObject,
    mut v___y_6862_: *mut crate::leanh::LeanObject,
    mut v___y_6863_: *mut crate::leanh::LeanObject,
    mut v___y_6864_: *mut crate::leanh::LeanObject,
    mut v___y_6865_: *mut crate::leanh::LeanObject,
    mut v___y_6866_: *mut crate::leanh::LeanObject,
    mut v___y_6867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_6870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6874_: u8 = 0;
    let mut v___x_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6884_: u8 = 0;
    let mut v_ref_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6893_: u8 = 0;
    let mut v___x_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: u8 = 0;
    let mut v___x_6897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_ex_6861_) == 0 {
                    v_ref_6869_ = crate::leanh::lean_ctor_get(v_ex_6861_, 0);
                    crate::leanh::lean_inc(v_ref_6869_);
                    v_msg_6870_ = crate::leanh::lean_ctor_get(v_ex_6861_, 1);
                    crate::leanh::lean_inc_ref(v_msg_6870_);
                    crate::leanh::lean_dec_ref_known(v_ex_6861_, 2);
                    v___x_6871_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_6869_, v_msg_6870_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_, v___y_6867_);
                    crate::leanh::lean_dec(v_ref_6869_);
                    return v___x_6871_;
                } else {
                    v_id_6872_ = crate::leanh::lean_ctor_get(v_ex_6861_, 0);
                    crate::leanh::lean_inc(v_id_6872_);
                    v___x_6896_ = l_Lean_Elab_isAbortExceptionId(v_id_6872_);
                    if v___x_6896_ == 0 {
                        v___x_6897_ = l_Lean_Exception_isInterrupt(v_ex_6861_);
                        crate::leanh::lean_dec_ref_known(v_ex_6861_, 2);
                        v___y_6874_ = v___x_6897_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_ex_6861_, 2);
                        v___y_6874_ = v___x_6896_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6874_ == 0 {
                    v___x_6875_ = l_Lean_InternalExceptionId_getName(v_id_6872_);
                    crate::leanh::lean_dec(v_id_6872_);
                    if crate::leanh::lean_obj_tag(v___x_6875_) == 0 {
                        v_a_6876_ = crate::leanh::lean_ctor_get(v___x_6875_, 0);
                        crate::leanh::lean_inc(v_a_6876_);
                        crate::leanh::lean_dec_ref_known(v___x_6875_, 1);
                        v___x_6877_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once), _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1);
                        v___x_6878_ = l_Lean_MessageData_ofName(v_a_6876_);
                        v___x_6879_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6879_, 0, v___x_6877_);
                        crate::leanh::lean_ctor_set(v___x_6879_, 1, v___x_6878_);
                        v___x_6880_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v___x_6879_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_, v___y_6867_);
                        return v___x_6880_;
                    } else {
                        v_a_6881_ = crate::leanh::lean_ctor_get(v___x_6875_, 0);
                        v_isSharedCheck_6893_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6875_)) as u8;
                        if v_isSharedCheck_6893_ == 0 {
                            v___x_6883_ = v___x_6875_;
                            v_isShared_6884_ = v_isSharedCheck_6893_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6881_);
                            crate::leanh::lean_dec(v___x_6875_);
                            v___x_6883_ = crate::leanh::lean_box(0);
                            v_isShared_6884_ = v_isSharedCheck_6893_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_id_6872_);
                    v___x_6894_ = crate::leanh::lean_box(0);
                    v___x_6895_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6895_, 0, v___x_6894_);
                    return v___x_6895_;
                }
            }
            2 => {
                v_ref_6885_ = crate::leanh::lean_ctor_get(v___y_6866_, 5);
                v___x_6886_ = lean_io_error_to_string(v_a_6881_);
                v___x_6887_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6887_, 0, v___x_6886_);
                v___x_6888_ = l_Lean_MessageData_ofFormat(v___x_6887_);
                crate::leanh::lean_inc(v_ref_6885_);
                v___x_6889_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6889_, 0, v_ref_6885_);
                crate::leanh::lean_ctor_set(v___x_6889_, 1, v___x_6888_);
                if v_isShared_6884_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6883_, 0, v___x_6889_);
                    v___x_6891_ = v___x_6883_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6892_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6892_, 0, v___x_6889_);
                    v___x_6891_ = v_reuseFailAlloc_6892_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___boxed(
    mut v_ex_6898_: *mut crate::leanh::LeanObject,
    mut v___y_6899_: *mut crate::leanh::LeanObject,
    mut v___y_6900_: *mut crate::leanh::LeanObject,
    mut v___y_6901_: *mut crate::leanh::LeanObject,
    mut v___y_6902_: *mut crate::leanh::LeanObject,
    mut v___y_6903_: *mut crate::leanh::LeanObject,
    mut v___y_6904_: *mut crate::leanh::LeanObject,
    mut v___y_6905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6906_ =
        l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(
            v_ex_6898_,
            v___y_6899_,
            v___y_6900_,
            v___y_6901_,
            v___y_6902_,
            v___y_6903_,
            v___y_6904_,
        );
    crate::leanh::lean_dec(v___y_6904_);
    crate::leanh::lean_dec_ref(v___y_6903_);
    crate::leanh::lean_dec(v___y_6902_);
    crate::leanh::lean_dec_ref(v___y_6901_);
    crate::leanh::lean_dec(v___y_6900_);
    crate::leanh::lean_dec_ref(v___y_6899_);
    return v_res_6906_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(
    mut v_a_6907_: *mut crate::leanh::LeanObject,
    mut v_config_6908_: *mut crate::leanh::LeanObject,
    mut v_____r_6909_: *mut crate::leanh::LeanObject,
    mut v___y_6910_: *mut crate::leanh::LeanObject,
    mut v___y_6911_: *mut crate::leanh::LeanObject,
    mut v___y_6912_: *mut crate::leanh::LeanObject,
    mut v___y_6913_: *mut crate::leanh::LeanObject,
    mut v___y_6914_: *mut crate::leanh::LeanObject,
    mut v___y_6915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6920_: u8 = 0;
    let mut v___x_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6925_: u8 = 0;
    let mut v_unused_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6930_: u8 = 0;
    let mut v___x_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6917_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_a_6907_, v___y_6910_, v___y_6911_, v___y_6912_, v___y_6913_, v___y_6914_, v___y_6915_);
                if crate::leanh::lean_obj_tag(v___x_6917_) == 0 {
                    v_isSharedCheck_6925_ = (!crate::leanh::lean_is_exclusive(v___x_6917_)) as u8;
                    if v_isSharedCheck_6925_ == 0 {
                        v_unused_6926_ = crate::leanh::lean_ctor_get(v___x_6917_, 0);
                        crate::leanh::lean_dec(v_unused_6926_);
                        v___x_6919_ = v___x_6917_;
                        v_isShared_6920_ = v_isSharedCheck_6925_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6917_);
                        v___x_6919_ = crate::leanh::lean_box(0);
                        v_isShared_6920_ = v_isSharedCheck_6925_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_config_6908_);
                    v_a_6927_ = crate::leanh::lean_ctor_get(v___x_6917_, 0);
                    v_isSharedCheck_6934_ = (!crate::leanh::lean_is_exclusive(v___x_6917_)) as u8;
                    if v_isSharedCheck_6934_ == 0 {
                        v___x_6929_ = v___x_6917_;
                        v_isShared_6930_ = v_isSharedCheck_6934_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6927_);
                        crate::leanh::lean_dec(v___x_6917_);
                        v___x_6929_ = crate::leanh::lean_box(0);
                        v_isShared_6930_ = v_isSharedCheck_6934_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6921_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6921_, 0, v_config_6908_);
                if v_isShared_6920_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6919_, 0, v___x_6921_);
                    v___x_6923_ = v___x_6919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6924_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6924_, 0, v___x_6921_);
                    v___x_6923_ = v_reuseFailAlloc_6924_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6923_;
            }
            3 => {
                if v_isShared_6930_ == 0 {
                    v___x_6932_ = v___x_6929_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6933_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6933_, 0, v_a_6927_);
                    v___x_6932_ = v_reuseFailAlloc_6933_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed(
    mut v_a_6935_: *mut crate::leanh::LeanObject,
    mut v_config_6936_: *mut crate::leanh::LeanObject,
    mut v_____r_6937_: *mut crate::leanh::LeanObject,
    mut v___y_6938_: *mut crate::leanh::LeanObject,
    mut v___y_6939_: *mut crate::leanh::LeanObject,
    mut v___y_6940_: *mut crate::leanh::LeanObject,
    mut v___y_6941_: *mut crate::leanh::LeanObject,
    mut v___y_6942_: *mut crate::leanh::LeanObject,
    mut v___y_6943_: *mut crate::leanh::LeanObject,
    mut v___y_6944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6945_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(
        v_a_6935_,
        v_config_6936_,
        v_____r_6937_,
        v___y_6938_,
        v___y_6939_,
        v___y_6940_,
        v___y_6941_,
        v___y_6942_,
        v___y_6943_,
    );
    crate::leanh::lean_dec(v___y_6943_);
    crate::leanh::lean_dec_ref(v___y_6942_);
    crate::leanh::lean_dec(v___y_6941_);
    crate::leanh::lean_dec_ref(v___y_6940_);
    crate::leanh::lean_dec(v___y_6939_);
    crate::leanh::lean_dec_ref(v___y_6938_);
    return v_res_6945_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(
    mut v___f_6946_: *mut crate::leanh::LeanObject,
    mut v_x_6947_: *mut crate::leanh::LeanObject,
    mut v___y_6948_: *mut crate::leanh::LeanObject,
    mut v___y_6949_: *mut crate::leanh::LeanObject,
    mut v___y_6950_: *mut crate::leanh::LeanObject,
    mut v___y_6951_: *mut crate::leanh::LeanObject,
    mut v___y_6952_: *mut crate::leanh::LeanObject,
    mut v___y_6953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6955_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v___y_6953_);
    crate::leanh::lean_inc_ref(v___y_6952_);
    crate::leanh::lean_inc(v___y_6951_);
    crate::leanh::lean_inc_ref(v___y_6950_);
    crate::leanh::lean_inc(v___y_6949_);
    crate::leanh::lean_inc_ref(v___y_6948_);
    v___x_6956_ = crate::leanh::lean_apply_8(
        v___f_6946_,
        v___x_6955_,
        v___y_6948_,
        v___y_6949_,
        v___y_6950_,
        v___y_6951_,
        v___y_6952_,
        v___y_6953_,
        crate::leanh::lean_box(0),
    );
    return v___x_6956_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1___boxed(
    mut v___f_6957_: *mut crate::leanh::LeanObject,
    mut v_x_6958_: *mut crate::leanh::LeanObject,
    mut v___y_6959_: *mut crate::leanh::LeanObject,
    mut v___y_6960_: *mut crate::leanh::LeanObject,
    mut v___y_6961_: *mut crate::leanh::LeanObject,
    mut v___y_6962_: *mut crate::leanh::LeanObject,
    mut v___y_6963_: *mut crate::leanh::LeanObject,
    mut v___y_6964_: *mut crate::leanh::LeanObject,
    mut v___y_6965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6966_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(
        v___f_6957_,
        v_x_6958_,
        v___y_6959_,
        v___y_6960_,
        v___y_6961_,
        v___y_6962_,
        v___y_6963_,
        v___y_6964_,
    );
    crate::leanh::lean_dec(v___y_6964_);
    crate::leanh::lean_dec_ref(v___y_6963_);
    crate::leanh::lean_dec(v___y_6962_);
    crate::leanh::lean_dec_ref(v___y_6961_);
    crate::leanh::lean_dec(v___y_6960_);
    crate::leanh::lean_dec_ref(v___y_6959_);
    crate::leanh::lean_dec_ref(v_x_6958_);
    return v_res_6966_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(
    mut v_eval_6967_: *mut crate::leanh::LeanObject,
    mut v_config_6968_: *mut crate::leanh::LeanObject,
    mut v_item_6969_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_6970_: u8,
    mut v_a_6971_: *mut crate::leanh::LeanObject,
    mut v_a_6972_: *mut crate::leanh::LeanObject,
    mut v_a_6973_: *mut crate::leanh::LeanObject,
    mut v_a_6974_: *mut crate::leanh::LeanObject,
    mut v_a_6975_: *mut crate::leanh::LeanObject,
    mut v_a_6976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6983_: u8 = 0;
    let mut v_a_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6988_: u8 = 0;
    let mut v_a_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6992_: u8 = 0;
    let mut v___x_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6996_: u8 = 0;
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7001_: u8 = 0;
    let mut v___x_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7004_: u8 = 0;
    let mut v_extra_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: u8 = 0;
    let mut v___x_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7016_: u8 = 0;
    let mut v_unused_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: u8 = 0;
    let mut v___x_7019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_6976_);
                crate::leanh::lean_inc_ref(v_a_6975_);
                crate::leanh::lean_inc(v_a_6974_);
                crate::leanh::lean_inc_ref(v_a_6973_);
                crate::leanh::lean_inc(v_a_6972_);
                crate::leanh::lean_inc_ref(v_a_6971_);
                crate::leanh::lean_inc(v_config_6968_);
                v___x_6997_ = crate::leanh::lean_apply_9(
                    v_eval_6967_,
                    v_config_6968_,
                    v_item_6969_,
                    v_a_6971_,
                    v_a_6972_,
                    v_a_6973_,
                    v_a_6974_,
                    v_a_6975_,
                    v_a_6976_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6997_) == 0 {
                    crate::leanh::lean_dec(v_config_6968_);
                    return v___x_6997_;
                } else {
                    v_a_6998_ = crate::leanh::lean_ctor_get(v___x_6997_, 0);
                    crate::leanh::lean_inc_n(v_a_6998_, 2);
                    crate::leanh::lean_inc(v_config_6968_);
                    v___f_6999_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_6999_, 0, v_a_6998_);
                    crate::leanh::lean_closure_set(v___f_6999_, 1, v_config_6968_);
                    v___x_7018_ = l_Lean_Exception_isInterrupt(v_a_6998_);
                    if v___x_7018_ == 0 {
                        crate::leanh::lean_inc(v_a_6998_);
                        v___x_7019_ = l_Lean_Exception_isRuntime(v_a_6998_);
                        v___y_7001_ = v___x_7019_;
                        state = 6;
                        continue;
                    } else {
                        v___y_7001_ = v___x_7018_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_6979_) == 0 {
                    v_a_6980_ = crate::leanh::lean_ctor_get(v___y_6979_, 0);
                    v_isSharedCheck_6988_ = (!crate::leanh::lean_is_exclusive(v___y_6979_)) as u8;
                    if v_isSharedCheck_6988_ == 0 {
                        v___x_6982_ = v___y_6979_;
                        v_isShared_6983_ = v_isSharedCheck_6988_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6980_);
                        crate::leanh::lean_dec(v___y_6979_);
                        v___x_6982_ = crate::leanh::lean_box(0);
                        v_isShared_6983_ = v_isSharedCheck_6988_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6989_ = crate::leanh::lean_ctor_get(v___y_6979_, 0);
                    v_isSharedCheck_6996_ = (!crate::leanh::lean_is_exclusive(v___y_6979_)) as u8;
                    if v_isSharedCheck_6996_ == 0 {
                        v___x_6991_ = v___y_6979_;
                        v_isShared_6992_ = v_isSharedCheck_6996_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6989_);
                        crate::leanh::lean_dec(v___y_6979_);
                        v___x_6991_ = crate::leanh::lean_box(0);
                        v_isShared_6992_ = v_isSharedCheck_6996_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_a_6984_ = crate::leanh::lean_ctor_get(v_a_6980_, 0);
                crate::leanh::lean_inc(v_a_6984_);
                crate::leanh::lean_dec(v_a_6980_);
                if v_isShared_6983_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6982_, 0, v_a_6984_);
                    v___x_6986_ = v___x_6982_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6987_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6987_, 0, v_a_6984_);
                    v___x_6986_ = v_reuseFailAlloc_6987_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6986_;
            }
            4 => {
                if v_isShared_6992_ == 0 {
                    v___x_6994_ = v___x_6991_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6995_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6995_, 0, v_a_6989_);
                    v___x_6994_ = v_reuseFailAlloc_6995_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6994_;
            }
            6 => {
                if v___y_7001_ == 0 {
                    if v_logExceptions_6970_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_6999_);
                        crate::leanh::lean_dec(v_a_6998_);
                        crate::leanh::lean_dec(v_config_6968_);
                        return v___x_6997_;
                    } else {
                        v_isSharedCheck_7016_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6997_)) as u8;
                        if v_isSharedCheck_7016_ == 0 {
                            v_unused_7017_ = crate::leanh::lean_ctor_get(v___x_6997_, 0);
                            crate::leanh::lean_dec(v_unused_7017_);
                            v___x_7003_ = v___x_6997_;
                            v_isShared_7004_ = v_isSharedCheck_7016_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6997_);
                            v___x_7003_ = crate::leanh::lean_box(0);
                            v_isShared_7004_ = v_isSharedCheck_7016_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_6999_);
                    crate::leanh::lean_dec(v_a_6998_);
                    crate::leanh::lean_dec(v_config_6968_);
                    return v___x_6997_;
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_6998_) == 1 {
                    v_extra_7005_ = crate::leanh::lean_ctor_get(v_a_6998_, 1);
                    if crate::leanh::lean_obj_tag(v_extra_7005_) == 0 {
                        crate::leanh::lean_dec_ref(v___f_6999_);
                        v_id_7006_ = crate::leanh::lean_ctor_get(v_a_6998_, 0);
                        v___x_7007_ = l_Lean_Elab_abortTermExceptionId;
                        v___x_7008_ =
                            l_Lean_instBEqInternalExceptionId_beq(v_id_7006_, v___x_7007_);
                        if v___x_7008_ == 0 {
                            crate::leanh::lean_del_object(v___x_7003_);
                            v___x_7009_ = crate::leanh::lean_box(0);
                            v___x_7010_ =
                                l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(
                                    v_a_6998_,
                                    v_config_6968_,
                                    v___x_7009_,
                                    v_a_6971_,
                                    v_a_6972_,
                                    v_a_6973_,
                                    v_a_6974_,
                                    v_a_6975_,
                                    v_a_6976_,
                                );
                            v___y_6979_ = v___x_7010_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_6998_, 2);
                            if v_isShared_7004_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_7003_, 0);
                                crate::leanh::lean_ctor_set(v___x_7003_, 0, v_config_6968_);
                                v___x_7012_ = v___x_7003_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_7013_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_7013_,
                                    0,
                                    v_config_6968_,
                                );
                                v___x_7012_ = v_reuseFailAlloc_7013_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_7003_);
                        crate::leanh::lean_dec(v_config_6968_);
                        v___x_7014_ =
                            l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(
                                v___f_6999_,
                                v_a_6998_,
                                v_a_6971_,
                                v_a_6972_,
                                v_a_6973_,
                                v_a_6974_,
                                v_a_6975_,
                                v_a_6976_,
                            );
                        crate::leanh::lean_dec_ref_known(v_a_6998_, 2);
                        v___y_6979_ = v___x_7014_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7003_);
                    crate::leanh::lean_dec(v_config_6968_);
                    v___x_7015_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(
                        v___f_6999_,
                        v_a_6998_,
                        v_a_6971_,
                        v_a_6972_,
                        v_a_6973_,
                        v_a_6974_,
                        v_a_6975_,
                        v_a_6976_,
                    );
                    crate::leanh::lean_dec(v_a_6998_);
                    v___y_6979_ = v___x_7015_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                return v___x_7012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___boxed(
    mut v_eval_7020_: *mut crate::leanh::LeanObject,
    mut v_config_7021_: *mut crate::leanh::LeanObject,
    mut v_item_7022_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7023_: *mut crate::leanh::LeanObject,
    mut v_a_7024_: *mut crate::leanh::LeanObject,
    mut v_a_7025_: *mut crate::leanh::LeanObject,
    mut v_a_7026_: *mut crate::leanh::LeanObject,
    mut v_a_7027_: *mut crate::leanh::LeanObject,
    mut v_a_7028_: *mut crate::leanh::LeanObject,
    mut v_a_7029_: *mut crate::leanh::LeanObject,
    mut v_a_7030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_7031_: u8 = 0;
    let mut v_res_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7031_ = (crate::leanh::lean_unbox(v_logExceptions_7023_) as u8);
    v_res_7032_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(
        v_eval_7020_,
        v_config_7021_,
        v_item_7022_,
        v_logExceptions_boxed_7031_,
        v_a_7024_,
        v_a_7025_,
        v_a_7026_,
        v_a_7027_,
        v_a_7028_,
        v_a_7029_,
    );
    crate::leanh::lean_dec(v_a_7029_);
    crate::leanh::lean_dec_ref(v_a_7028_);
    crate::leanh::lean_dec(v_a_7027_);
    crate::leanh::lean_dec_ref(v_a_7026_);
    crate::leanh::lean_dec(v_a_7025_);
    crate::leanh::lean_dec_ref(v_a_7024_);
    return v_res_7032_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(
    mut v_00_u03b1_7033_: *mut crate::leanh::LeanObject,
    mut v_eval_7034_: *mut crate::leanh::LeanObject,
    mut v_config_7035_: *mut crate::leanh::LeanObject,
    mut v_item_7036_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7037_: u8,
    mut v_a_7038_: *mut crate::leanh::LeanObject,
    mut v_a_7039_: *mut crate::leanh::LeanObject,
    mut v_a_7040_: *mut crate::leanh::LeanObject,
    mut v_a_7041_: *mut crate::leanh::LeanObject,
    mut v_a_7042_: *mut crate::leanh::LeanObject,
    mut v_a_7043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7045_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(
        v_eval_7034_,
        v_config_7035_,
        v_item_7036_,
        v_logExceptions_7037_,
        v_a_7038_,
        v_a_7039_,
        v_a_7040_,
        v_a_7041_,
        v_a_7042_,
        v_a_7043_,
    );
    return v___x_7045_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___boxed(
    mut v_00_u03b1_7046_: *mut crate::leanh::LeanObject,
    mut v_eval_7047_: *mut crate::leanh::LeanObject,
    mut v_config_7048_: *mut crate::leanh::LeanObject,
    mut v_item_7049_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7050_: *mut crate::leanh::LeanObject,
    mut v_a_7051_: *mut crate::leanh::LeanObject,
    mut v_a_7052_: *mut crate::leanh::LeanObject,
    mut v_a_7053_: *mut crate::leanh::LeanObject,
    mut v_a_7054_: *mut crate::leanh::LeanObject,
    mut v_a_7055_: *mut crate::leanh::LeanObject,
    mut v_a_7056_: *mut crate::leanh::LeanObject,
    mut v_a_7057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_7058_: u8 = 0;
    let mut v_res_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7058_ = (crate::leanh::lean_unbox(v_logExceptions_7050_) as u8);
    v_res_7059_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(
        v_00_u03b1_7046_,
        v_eval_7047_,
        v_config_7048_,
        v_item_7049_,
        v_logExceptions_boxed_7058_,
        v_a_7051_,
        v_a_7052_,
        v_a_7053_,
        v_a_7054_,
        v_a_7055_,
        v_a_7056_,
    );
    crate::leanh::lean_dec(v_a_7056_);
    crate::leanh::lean_dec_ref(v_a_7055_);
    crate::leanh::lean_dec(v_a_7054_);
    crate::leanh::lean_dec_ref(v_a_7053_);
    crate::leanh::lean_dec(v_a_7052_);
    crate::leanh::lean_dec_ref(v_a_7051_);
    return v_res_7059_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(
    mut v_ref_7060_: *mut crate::leanh::LeanObject,
    mut v_msgData_7061_: *mut crate::leanh::LeanObject,
    mut v_severity_7062_: u8,
    mut v_isSilent_7063_: u8,
    mut v___y_7064_: *mut crate::leanh::LeanObject,
    mut v___y_7065_: *mut crate::leanh::LeanObject,
    mut v___y_7066_: *mut crate::leanh::LeanObject,
    mut v___y_7067_: *mut crate::leanh::LeanObject,
    mut v___y_7068_: *mut crate::leanh::LeanObject,
    mut v___y_7069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7071_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_7060_, v_msgData_7061_, v_severity_7062_, v_isSilent_7063_, v___y_7066_, v___y_7067_, v___y_7068_, v___y_7069_);
    return v___x_7071_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___boxed(
    mut v_ref_7072_: *mut crate::leanh::LeanObject,
    mut v_msgData_7073_: *mut crate::leanh::LeanObject,
    mut v_severity_7074_: *mut crate::leanh::LeanObject,
    mut v_isSilent_7075_: *mut crate::leanh::LeanObject,
    mut v___y_7076_: *mut crate::leanh::LeanObject,
    mut v___y_7077_: *mut crate::leanh::LeanObject,
    mut v___y_7078_: *mut crate::leanh::LeanObject,
    mut v___y_7079_: *mut crate::leanh::LeanObject,
    mut v___y_7080_: *mut crate::leanh::LeanObject,
    mut v___y_7081_: *mut crate::leanh::LeanObject,
    mut v___y_7082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_7083_: u8 = 0;
    let mut v_isSilent_boxed_7084_: u8 = 0;
    let mut v_res_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_7083_ = (crate::leanh::lean_unbox(v_severity_7074_) as u8);
    v_isSilent_boxed_7084_ = (crate::leanh::lean_unbox(v_isSilent_7075_) as u8);
    v_res_7085_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(v_ref_7072_, v_msgData_7073_, v_severity_boxed_7083_, v_isSilent_boxed_7084_, v___y_7076_, v___y_7077_, v___y_7078_, v___y_7079_, v___y_7080_, v___y_7081_);
    crate::leanh::lean_dec(v___y_7081_);
    crate::leanh::lean_dec_ref(v___y_7080_);
    crate::leanh::lean_dec(v___y_7079_);
    crate::leanh::lean_dec_ref(v___y_7078_);
    crate::leanh::lean_dec(v___y_7077_);
    crate::leanh::lean_dec_ref(v___y_7076_);
    crate::leanh::lean_dec(v_ref_7072_);
    return v_res_7085_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7086_ = crate::leanh::lean_box(0);
    v___x_7087_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_7088_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7088_, 0, v___x_7087_);
    crate::leanh::lean_ctor_set(v___x_7088_, 1, v___x_7086_);
    return v___x_7088_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7090_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0);
    v___x_7091_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7091_, 0, v___x_7090_);
    return v___x_7091_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___boxed(
    mut v___y_7092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7093_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
    return v_res_7093_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(
    mut v_00_u03b1_7094_: *mut crate::leanh::LeanObject,
    mut v___y_7095_: *mut crate::leanh::LeanObject,
    mut v___y_7096_: *mut crate::leanh::LeanObject,
    mut v___y_7097_: *mut crate::leanh::LeanObject,
    mut v___y_7098_: *mut crate::leanh::LeanObject,
    mut v___y_7099_: *mut crate::leanh::LeanObject,
    mut v___y_7100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7102_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
    return v___x_7102_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___boxed(
    mut v_00_u03b1_7103_: *mut crate::leanh::LeanObject,
    mut v___y_7104_: *mut crate::leanh::LeanObject,
    mut v___y_7105_: *mut crate::leanh::LeanObject,
    mut v___y_7106_: *mut crate::leanh::LeanObject,
    mut v___y_7107_: *mut crate::leanh::LeanObject,
    mut v___y_7108_: *mut crate::leanh::LeanObject,
    mut v___y_7109_: *mut crate::leanh::LeanObject,
    mut v___y_7110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7111_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(v_00_u03b1_7103_, v___y_7104_, v___y_7105_, v___y_7106_, v___y_7107_, v___y_7108_, v___y_7109_);
    crate::leanh::lean_dec(v___y_7109_);
    crate::leanh::lean_dec_ref(v___y_7108_);
    crate::leanh::lean_dec(v___y_7107_);
    crate::leanh::lean_dec_ref(v___y_7106_);
    crate::leanh::lean_dec(v___y_7105_);
    crate::leanh::lean_dec_ref(v___y_7104_);
    return v_res_7111_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7115_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_7116_ = l_Lean_Level_ofNat(v___x_7115_);
    return v___x_7116_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7117_ = crate::leanh::lean_box(0);
    v___x_7118_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2,
    );
    v___x_7119_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7119_, 0, v___x_7118_);
    crate::leanh::lean_ctor_set(v___x_7119_, 1, v___x_7117_);
    return v___x_7119_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7120_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3,
    );
    v___x_7121_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1;
    v___x_7122_ = l_Lean_Expr_const___override(v___x_7121_, v___x_7120_);
    return v___x_7122_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7126_ = crate::leanh::lean_box(0);
    v___x_7127_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6;
    v___x_7128_ = l_Lean_Expr_const___override(v___x_7127_, v___x_7126_);
    return v___x_7128_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(
    mut v_cfg_7132_: *mut crate::leanh::LeanObject,
    mut v_cfgItem_7133_: *mut crate::leanh::LeanObject,
    mut v_cfgType_x3f_7134_: *mut crate::leanh::LeanObject,
    mut v_a_7135_: *mut crate::leanh::LeanObject,
    mut v_a_7136_: *mut crate::leanh::LeanObject,
    mut v_a_7137_: *mut crate::leanh::LeanObject,
    mut v_a_7138_: *mut crate::leanh::LeanObject,
    mut v_a_7139_: *mut crate::leanh::LeanObject,
    mut v_a_7140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: u8 = 0;
    let mut v___x_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_7155_: u8 = 0;
    let mut v___x_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7159_: u8 = 0;
    let mut v___x_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: u8 = 0;
    let mut v___x_7168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: u8 = 0;
    let mut v___x_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_cfgType_x3f_7134_) == 1 {
                    v_val_7152_ = crate::leanh::lean_ctor_get(v_cfgType_x3f_7134_, 0);
                    crate::leanh::lean_inc(v_val_7152_);
                    crate::leanh::lean_dec_ref_known(v_cfgType_x3f_7134_, 1);
                    v___x_7153_ = lean_st_ref_get(v_a_7140_);
                    v_infoState_7154_ = crate::leanh::lean_ctor_get(v___x_7153_, 7);
                    crate::leanh::lean_inc_ref(v_infoState_7154_);
                    crate::leanh::lean_dec(v___x_7153_);
                    v_enabled_7155_ = crate::leanh::lean_ctor_get_uint8(
                        v_infoState_7154_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    crate::leanh::lean_dec_ref(v_infoState_7154_);
                    if v_enabled_7155_ == 0 {
                        crate::leanh::lean_dec(v_val_7152_);
                        v___y_7143_ = v_a_7135_;
                        v___y_7144_ = v_a_7136_;
                        v___y_7145_ = v_a_7137_;
                        v___y_7146_ = v_a_7138_;
                        v___y_7147_ = v_a_7139_;
                        v___y_7148_ = v_a_7140_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7156_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_7157_ = l_Lean_Syntax_getArg(v_cfgItem_7133_, v___x_7156_);
                        v___x_7171_ = l_Lean_Syntax_isAtom(v___x_7157_);
                        if v___x_7171_ == 0 {
                            v___y_7159_ = v___x_7171_;
                            state = 2;
                            continue;
                        } else {
                            v___x_7172_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_7173_ = l_Lean_Syntax_getArg(v_cfgItem_7133_, v___x_7172_);
                            v___x_7174_ = l_Lean_Syntax_isMissing(v___x_7173_);
                            crate::leanh::lean_dec(v___x_7173_);
                            v___y_7159_ = v___x_7174_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_cfgType_x3f_7134_);
                    v___y_7143_ = v_a_7135_;
                    v___y_7144_ = v_a_7136_;
                    v___y_7145_ = v_a_7137_;
                    v___y_7146_ = v_a_7138_;
                    v___y_7147_ = v_a_7139_;
                    v___y_7148_ = v_a_7140_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7149_ = l_Lean_Syntax_hasMissing(v_cfgItem_7133_);
                if v___x_7149_ == 0 {
                    crate::leanh::lean_dec(v_cfg_7132_);
                    v___x_7150_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
                    return v___x_7150_;
                } else {
                    v___x_7151_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7151_, 0, v_cfg_7132_);
                    return v___x_7151_;
                }
            }
            2 => {
                if v___y_7159_ == 0 {
                    crate::leanh::lean_dec(v___x_7157_);
                    crate::leanh::lean_dec(v_val_7152_);
                    v___y_7143_ = v_a_7135_;
                    v___y_7144_ = v_a_7136_;
                    v___y_7145_ = v_a_7137_;
                    v___y_7146_ = v_a_7138_;
                    v___y_7147_ = v_a_7139_;
                    v___y_7148_ = v_a_7140_;
                    state = 1;
                    continue;
                } else {
                    v___x_7160_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once), _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4);
                    v___x_7161_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once), _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7);
                    v___x_7162_ = l_Lean_mkAppB(v___x_7160_, v_val_7152_, v___x_7161_);
                    v___x_7163_ =
                        l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9;
                    v___x_7164_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7164_, 0, v___x_7163_);
                    crate::leanh::lean_ctor_set(v___x_7164_, 1, v___x_7157_);
                    v___x_7165_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2,
                    );
                    v___x_7166_ = crate::leanh::lean_box(0);
                    v___x_7167_ = 0;
                    v___x_7168_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_7168_, 0, v___x_7164_);
                    crate::leanh::lean_ctor_set(v___x_7168_, 1, v___x_7165_);
                    crate::leanh::lean_ctor_set(v___x_7168_, 2, v___x_7166_);
                    crate::leanh::lean_ctor_set(v___x_7168_, 3, v___x_7162_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_7168_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v___x_7167_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_7168_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v___x_7167_,
                    );
                    v___x_7169_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7169_, 0, v___x_7168_);
                    crate::leanh::lean_ctor_set(v___x_7169_, 1, v___x_7166_);
                    v___x_7170_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_7169_, v_a_7135_, v_a_7136_, v_a_7137_, v_a_7138_, v_a_7139_, v_a_7140_);
                    crate::leanh::lean_dec_ref(v___x_7170_);
                    v___y_7143_ = v_a_7135_;
                    v___y_7144_ = v_a_7136_;
                    v___y_7145_ = v_a_7137_;
                    v___y_7146_ = v_a_7138_;
                    v___y_7147_ = v_a_7139_;
                    v___y_7148_ = v_a_7140_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___boxed(
    mut v_cfg_7175_: *mut crate::leanh::LeanObject,
    mut v_cfgItem_7176_: *mut crate::leanh::LeanObject,
    mut v_cfgType_x3f_7177_: *mut crate::leanh::LeanObject,
    mut v_a_7178_: *mut crate::leanh::LeanObject,
    mut v_a_7179_: *mut crate::leanh::LeanObject,
    mut v_a_7180_: *mut crate::leanh::LeanObject,
    mut v_a_7181_: *mut crate::leanh::LeanObject,
    mut v_a_7182_: *mut crate::leanh::LeanObject,
    mut v_a_7183_: *mut crate::leanh::LeanObject,
    mut v_a_7184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7185_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(
        v_cfg_7175_,
        v_cfgItem_7176_,
        v_cfgType_x3f_7177_,
        v_a_7178_,
        v_a_7179_,
        v_a_7180_,
        v_a_7181_,
        v_a_7182_,
        v_a_7183_,
    );
    crate::leanh::lean_dec(v_a_7183_);
    crate::leanh::lean_dec_ref(v_a_7182_);
    crate::leanh::lean_dec(v_a_7181_);
    crate::leanh::lean_dec_ref(v_a_7180_);
    crate::leanh::lean_dec(v_a_7179_);
    crate::leanh::lean_dec_ref(v_a_7178_);
    crate::leanh::lean_dec(v_cfgItem_7176_);
    return v_res_7185_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(
    mut v_00_u03b1_7186_: *mut crate::leanh::LeanObject,
    mut v_cfg_7187_: *mut crate::leanh::LeanObject,
    mut v_cfgItem_7188_: *mut crate::leanh::LeanObject,
    mut v_cfgType_x3f_7189_: *mut crate::leanh::LeanObject,
    mut v_a_7190_: *mut crate::leanh::LeanObject,
    mut v_a_7191_: *mut crate::leanh::LeanObject,
    mut v_a_7192_: *mut crate::leanh::LeanObject,
    mut v_a_7193_: *mut crate::leanh::LeanObject,
    mut v_a_7194_: *mut crate::leanh::LeanObject,
    mut v_a_7195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7197_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(
        v_cfg_7187_,
        v_cfgItem_7188_,
        v_cfgType_x3f_7189_,
        v_a_7190_,
        v_a_7191_,
        v_a_7192_,
        v_a_7193_,
        v_a_7194_,
        v_a_7195_,
    );
    return v___x_7197_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___boxed(
    mut v_00_u03b1_7198_: *mut crate::leanh::LeanObject,
    mut v_cfg_7199_: *mut crate::leanh::LeanObject,
    mut v_cfgItem_7200_: *mut crate::leanh::LeanObject,
    mut v_cfgType_x3f_7201_: *mut crate::leanh::LeanObject,
    mut v_a_7202_: *mut crate::leanh::LeanObject,
    mut v_a_7203_: *mut crate::leanh::LeanObject,
    mut v_a_7204_: *mut crate::leanh::LeanObject,
    mut v_a_7205_: *mut crate::leanh::LeanObject,
    mut v_a_7206_: *mut crate::leanh::LeanObject,
    mut v_a_7207_: *mut crate::leanh::LeanObject,
    mut v_a_7208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7209_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(
        v_00_u03b1_7198_,
        v_cfg_7199_,
        v_cfgItem_7200_,
        v_cfgType_x3f_7201_,
        v_a_7202_,
        v_a_7203_,
        v_a_7204_,
        v_a_7205_,
        v_a_7206_,
        v_a_7207_,
    );
    crate::leanh::lean_dec(v_a_7207_);
    crate::leanh::lean_dec_ref(v_a_7206_);
    crate::leanh::lean_dec(v_a_7205_);
    crate::leanh::lean_dec_ref(v_a_7204_);
    crate::leanh::lean_dec(v_a_7203_);
    crate::leanh::lean_dec_ref(v_a_7202_);
    crate::leanh::lean_dec(v_cfgItem_7200_);
    return v_res_7209_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(
    mut v_s_7210_: *mut crate::leanh::LeanObject,
    mut v_a_7211_: *mut crate::leanh::LeanObject,
    mut v_b_7212_: u8,
) -> u8 {
    let mut v_str_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: u8 = 0;
    let mut v___x_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: u32 = 0;
    let mut v___x_7220_: u32 = 0;
    let mut v___x_7221_: u8 = 0;
    let mut v___x_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_7213_ = crate::leanh::lean_ctor_get(v_s_7210_, 0);
                v_startInclusive_7214_ = crate::leanh::lean_ctor_get(v_s_7210_, 1);
                v_endExclusive_7215_ = crate::leanh::lean_ctor_get(v_s_7210_, 2);
                v___x_7216_ = lean_nat_sub(v_endExclusive_7215_, v_startInclusive_7214_);
                v___x_7217_ = lean_nat_dec_eq(v_a_7211_, v___x_7216_);
                crate::leanh::lean_dec(v___x_7216_);
                if v___x_7217_ == 0 {
                    v___x_7218_ = lean_nat_add(v_startInclusive_7214_, v_a_7211_);
                    crate::leanh::lean_dec(v_a_7211_);
                    v___x_7219_ = lean_string_utf8_get_fast(v_str_7213_, v___x_7218_);
                    v___x_7220_ = 46;
                    v___x_7221_ = lean_uint32_dec_eq(v___x_7219_, v___x_7220_);
                    if v___x_7221_ == 0 {
                        v___x_7222_ = lean_string_utf8_next_fast(v_str_7213_, v___x_7218_);
                        crate::leanh::lean_dec(v___x_7218_);
                        v___x_7223_ = lean_nat_sub(v___x_7222_, v_startInclusive_7214_);
                        v_a_7211_ = v___x_7223_;
                        v_b_7212_ = v___x_7221_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_7218_);
                        return v___x_7221_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7211_);
                    return v_b_7212_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_s_7225_: *mut crate::leanh::LeanObject,
    mut v_a_7226_: *mut crate::leanh::LeanObject,
    mut v_b_7227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_7228_: u8 = 0;
    let mut v_res_7229_: u8 = 0;
    let mut v_r_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_7228_ = (crate::leanh::lean_unbox(v_b_7227_) as u8);
    v_res_7229_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_7225_, v_a_7226_, v_b_boxed_7228_);
    crate::leanh::lean_dec_ref(v_s_7225_);
    v_r_7230_ = crate::leanh::lean_box((v_res_7229_) as usize);
    return v_r_7230_;
}
pub unsafe fn l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(
    mut v_s_7231_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_searcher_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: u8 = 0;
    let mut v___x_7234_: u8 = 0;
    v_searcher_7232_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7233_ = 0;
    v___x_7234_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_7231_, v_searcher_7232_, v___x_7233_);
    return v___x_7234_;
}
pub unsafe fn l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0___boxed(
    mut v_s_7235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7236_: u8 = 0;
    let mut v_r_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7236_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v_s_7235_);
    crate::leanh::lean_dec_ref(v_s_7235_);
    v_r_7237_ = crate::leanh::lean_box((v_res_7236_) as usize);
    return v_r_7237_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(
    mut v_si_7238_: *mut crate::leanh::LeanObject,
    mut v_val_7239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: u8 = 0;
    let mut v___x_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7247_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7248_ = lean_string_utf8_byte_size(v_val_7239_);
                crate::leanh::lean_inc_ref(v_val_7239_);
                v___x_7249_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7249_, 0, v_val_7239_);
                crate::leanh::lean_ctor_set(v___x_7249_, 1, v___x_7247_);
                crate::leanh::lean_ctor_set(v___x_7249_, 2, v___x_7248_);
                v___x_7250_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v___x_7249_);
                crate::leanh::lean_dec_ref_known(v___x_7249_, 3);
                if v___x_7250_ == 0 {
                    v___x_7251_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_val_7239_);
                    v___x_7252_ = l_Lean_Name_str___override(v___x_7251_, v_val_7239_);
                    v___y_7241_ = v___x_7252_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_val_7239_);
                    v___x_7253_ = l_String_toName(v_val_7239_);
                    v___y_7241_ = v___x_7253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7242_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7243_ = lean_string_utf8_byte_size(v_val_7239_);
                v___x_7244_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7244_, 0, v_val_7239_);
                crate::leanh::lean_ctor_set(v___x_7244_, 1, v___x_7242_);
                crate::leanh::lean_ctor_set(v___x_7244_, 2, v___x_7243_);
                v___x_7245_ = crate::leanh::lean_box(0);
                v___x_7246_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7246_, 0, v_si_7238_);
                crate::leanh::lean_ctor_set(v___x_7246_, 1, v___x_7244_);
                crate::leanh::lean_ctor_set(v___x_7246_, 2, v___y_7241_);
                crate::leanh::lean_ctor_set(v___x_7246_, 3, v___x_7245_);
                return v___x_7246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(
    mut v_eval_7255_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7256_: u8,
    mut v_onErr_7257_: *mut crate::leanh::LeanObject,
    mut v_init_7258_: *mut crate::leanh::LeanObject,
    mut v_cfgs_7259_: *mut crate::leanh::LeanObject,
    mut v___y_7260_: *mut crate::leanh::LeanObject,
    mut v___y_7261_: *mut crate::leanh::LeanObject,
    mut v___y_7262_: *mut crate::leanh::LeanObject,
    mut v___y_7263_: *mut crate::leanh::LeanObject,
    mut v___y_7264_: *mut crate::leanh::LeanObject,
    mut v___y_7265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: u8 = 0;
    v___x_7267_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7268_ = lean_array_get_size(v_cfgs_7259_);
    v___x_7269_ = lean_nat_dec_lt(v___x_7267_, v___x_7268_);
    if v___x_7269_ == 0 {
        let mut v___x_7270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_onErr_7257_);
        crate::leanh::lean_dec_ref(v_eval_7255_);
        v___x_7270_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7270_, 0, v_init_7258_);
        return v___x_7270_;
    } else {
        let mut v___x_7271_: u8 = 0;
        v___x_7271_ = lean_nat_dec_le(v___x_7268_, v___x_7268_);
        if v___x_7271_ == 0 {
            if v___x_7269_ == 0 {
                let mut v___x_7272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_onErr_7257_);
                crate::leanh::lean_dec_ref(v_eval_7255_);
                v___x_7272_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7272_, 0, v_init_7258_);
                return v___x_7272_;
            } else {
                let mut v___x_7273_: usize = 0;
                let mut v___x_7274_: usize = 0;
                let mut v___x_7275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_7273_ = 0usize;
                v___x_7274_ = lean_usize_of_nat(v___x_7268_);
                v___x_7275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_7255_, v_logExceptions_7256_, v_onErr_7257_, v_cfgs_7259_, v___x_7273_, v___x_7274_, v_init_7258_, v___y_7260_, v___y_7261_, v___y_7262_, v___y_7263_, v___y_7264_, v___y_7265_);
                return v___x_7275_;
            }
        } else {
            let mut v___x_7276_: usize = 0;
            let mut v___x_7277_: usize = 0;
            let mut v___x_7278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_7276_ = 0usize;
            v___x_7277_ = lean_usize_of_nat(v___x_7268_);
            v___x_7278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_7255_, v_logExceptions_7256_, v_onErr_7257_, v_cfgs_7259_, v___x_7276_, v___x_7277_, v_init_7258_, v___y_7260_, v___y_7261_, v___y_7262_, v___y_7263_, v___y_7264_, v___y_7265_);
            return v___x_7278_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(
    mut v_eval_7279_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7280_: u8,
    mut v_onErr_7281_: *mut crate::leanh::LeanObject,
    mut v_init_7282_: *mut crate::leanh::LeanObject,
    mut v_cfg_7283_: *mut crate::leanh::LeanObject,
    mut v___y_7284_: *mut crate::leanh::LeanObject,
    mut v___y_7285_: *mut crate::leanh::LeanObject,
    mut v___y_7286_: *mut crate::leanh::LeanObject,
    mut v___y_7287_: *mut crate::leanh::LeanObject,
    mut v___y_7288_: *mut crate::leanh::LeanObject,
    mut v___y_7289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_7303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7315_: u8 = 0;
    let mut v_cancelTk_x3f_7316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7317_: u8 = 0;
    let mut v_inheritedTraceOptions_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: u8 = 0;
    let mut v___x_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7326_: u8 = 0;
    let mut v_atomAsIdent_7327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7328_: u8 = 0;
    let mut v_info_7329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7347_: u8 = 0;
    let mut v___x_7348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7349_: u8 = 0;
    let mut v___x_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: u8 = 0;
    let mut v___x_7360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: u8 = 0;
    let mut v___x_7362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: u8 = 0;
    let mut v___x_7364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7365_: u8 = 0;
    let mut v___x_7366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7322_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1;
                crate::leanh::lean_inc(v_cfg_7283_);
                v___x_7323_ = l_Lean_Syntax_isOfKind(v_cfg_7283_, v___x_7322_);
                if v___x_7323_ == 0 {
                    v___x_7324_ = l_Lean_Syntax_getNumArgs(v_cfg_7283_);
                    v___x_7325_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7326_ = lean_nat_dec_eq(v___x_7324_, v___x_7325_);
                    if v___x_7326_ == 0 {
                        v_atomAsIdent_7327_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0;
                        v___x_7328_ = lean_nat_dec_le(v___x_7325_, v___x_7324_);
                        if v___x_7328_ == 0 {
                            crate::leanh::lean_dec(v___x_7324_);
                            if crate::leanh::lean_obj_tag(v_cfg_7283_) == 2 {
                                crate::leanh::lean_dec_ref(v_onErr_7281_);
                                v_info_7329_ = crate::leanh::lean_ctor_get(v_cfg_7283_, 0);
                                v_val_7330_ = crate::leanh::lean_ctor_get(v_cfg_7283_, 1);
                                crate::leanh::lean_inc_ref(v_val_7330_);
                                crate::leanh::lean_inc(v_info_7329_);
                                v___x_7331_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(v_info_7329_, v_val_7330_);
                                v___x_7332_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7;
                                v___x_7333_ =
                                    l_Lean_mkCIdentFrom(v_cfg_7283_, v___x_7332_, v___x_7326_);
                                v___x_7334_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8;
                                v___x_7335_ = l_Lean_TSyntax_getId(v___x_7331_);
                                v___x_7336_ = lean_erase_macro_scopes(v___x_7335_);
                                v___x_7337_ = crate::leanh::lean_box(0);
                                crate::leanh::lean_inc(v___x_7331_);
                                v___x_7338_ =
                                    l_Lean_Syntax_identComponents(v___x_7331_, v___x_7337_);
                                v___x_7339_ = crate::leanh::lean_box(0);
                                v___x_7340_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7340_, 0, v_cfg_7283_);
                                crate::leanh::lean_ctor_set(v___x_7340_, 1, v___x_7331_);
                                crate::leanh::lean_ctor_set(v___x_7340_, 2, v___x_7333_);
                                crate::leanh::lean_ctor_set(v___x_7340_, 3, v___x_7334_);
                                crate::leanh::lean_ctor_set(v___x_7340_, 4, v___x_7336_);
                                crate::leanh::lean_ctor_set(v___x_7340_, 5, v___x_7338_);
                                crate::leanh::lean_ctor_set(v___x_7340_, 6, v___x_7339_);
                                v___x_7341_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(
                                    v_eval_7279_,
                                    v_init_7282_,
                                    v___x_7340_,
                                    v_logExceptions_7280_,
                                    v___y_7284_,
                                    v___y_7285_,
                                    v___y_7286_,
                                    v___y_7287_,
                                    v___y_7288_,
                                    v___y_7289_,
                                );
                                return v___x_7341_;
                            } else {
                                crate::leanh::lean_dec_ref(v_eval_7279_);
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_7342_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_7343_ = l_Lean_Syntax_getArg(v_cfg_7283_, v___x_7342_);
                            if crate::leanh::lean_obj_tag(v___x_7343_) == 2 {
                                v_val_7344_ = crate::leanh::lean_ctor_get(v___x_7343_, 1);
                                crate::leanh::lean_inc_ref(v_val_7344_);
                                v___x_7358_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11;
                                v___x_7359_ = lean_string_dec_eq(v_val_7344_, v___x_7358_);
                                if v___x_7359_ == 0 {
                                    v___x_7360_ =
                                        l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12;
                                    v___x_7361_ = lean_string_dec_eq(v_val_7344_, v___x_7360_);
                                    if v___x_7361_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_7343_, 2);
                                        v___x_7362_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13;
                                        v___x_7363_ = lean_string_dec_eq(v_val_7344_, v___x_7362_);
                                        crate::leanh::lean_dec_ref(v_val_7344_);
                                        if v___x_7363_ == 0 {
                                            crate::leanh::lean_dec(v___x_7324_);
                                            crate::leanh::lean_dec_ref(v_eval_7279_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_7364_ = crate::leanh::lean_unsigned_to_nat(5);
                                            v___x_7365_ = lean_nat_dec_le(v___x_7324_, v___x_7364_);
                                            crate::leanh::lean_dec(v___x_7324_);
                                            if v___x_7365_ == 0 {
                                                crate::leanh::lean_dec_ref(v_eval_7279_);
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_7366_ =
                                                    l_Lean_Syntax_getArg(v_cfg_7283_, v___x_7325_);
                                                v___x_7367_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_7327_, v___x_7366_);
                                                if crate::leanh::lean_obj_tag(v___x_7367_) == 1 {
                                                    crate::leanh::lean_dec_ref(v_onErr_7281_);
                                                    v_val_7368_ =
                                                        crate::leanh::lean_ctor_get(v___x_7367_, 0);
                                                    crate::leanh::lean_inc_n(v_val_7368_, 2);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_7367_,
                                                        1,
                                                    );
                                                    v___x_7369_ =
                                                        crate::leanh::lean_unsigned_to_nat(3);
                                                    v___x_7370_ = l_Lean_Syntax_getArg(
                                                        v_cfg_7283_,
                                                        v___x_7369_,
                                                    );
                                                    v___x_7371_ = crate::leanh::lean_box(0);
                                                    v___x_7372_ = l_Lean_TSyntax_getId(v_val_7368_);
                                                    v___x_7373_ =
                                                        lean_erase_macro_scopes(v___x_7372_);
                                                    v___x_7374_ = l_Lean_Syntax_identComponents(
                                                        v_val_7368_,
                                                        v___x_7371_,
                                                    );
                                                    v___x_7375_ = crate::leanh::lean_box(0);
                                                    v___x_7376_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        7,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        0,
                                                        v_cfg_7283_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        1,
                                                        v_val_7368_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        2,
                                                        v___x_7370_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        3,
                                                        v___x_7371_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        4,
                                                        v___x_7373_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        5,
                                                        v___x_7374_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        6,
                                                        v___x_7375_,
                                                    );
                                                    v___x_7377_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_7279_, v_init_7282_, v___x_7376_, v_logExceptions_7280_, v___y_7284_, v___y_7285_, v___y_7286_, v___y_7287_, v___y_7288_, v___y_7289_);
                                                    return v___x_7377_;
                                                } else {
                                                    crate::leanh::lean_dec(v___x_7367_);
                                                    crate::leanh::lean_dec_ref(v_eval_7279_);
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_val_7344_);
                                        v___x_7378_ =
                                            crate::leanh::lean_box((v___x_7326_) as usize);
                                        v___x_7379_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_7379_, 0, v___x_7378_);
                                        v___y_7346_ = v___x_7379_;
                                        v_val_7347_ = v___x_7326_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_val_7344_);
                                    v___x_7380_ = crate::leanh::lean_box((v___x_7359_) as usize);
                                    v___x_7381_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_7381_, 0, v___x_7380_);
                                    v___y_7346_ = v___x_7381_;
                                    v_val_7347_ = v___x_7359_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_7343_);
                                crate::leanh::lean_dec(v___x_7324_);
                                crate::leanh::lean_dec_ref(v_eval_7279_);
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_7324_);
                        v___x_7382_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_7383_ = l_Lean_Syntax_getArg(v_cfg_7283_, v___x_7382_);
                        crate::leanh::lean_dec(v_cfg_7283_);
                        v_cfg_7283_ = v___x_7383_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_7385_ = l_Lean_Syntax_getArgs(v_cfg_7283_);
                    crate::leanh::lean_dec(v_cfg_7283_);
                    v___x_7386_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7279_, v_logExceptions_7280_, v_onErr_7281_, v_init_7282_, v___x_7385_, v___y_7284_, v___y_7285_, v___y_7286_, v___y_7287_, v___y_7288_, v___y_7289_);
                    crate::leanh::lean_dec_ref(v___x_7385_);
                    return v___x_7386_;
                }
            }
            1 => {
                v___x_7295_ = l_Lean_TSyntax_getId(v___y_7292_);
                v___x_7296_ = lean_erase_macro_scopes(v___x_7295_);
                v___x_7297_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_7292_);
                v___x_7298_ = l_Lean_Syntax_identComponents(v___y_7292_, v___x_7297_);
                v___x_7299_ = crate::leanh::lean_box(0);
                v___x_7300_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7300_, 0, v_cfg_7283_);
                crate::leanh::lean_ctor_set(v___x_7300_, 1, v___y_7292_);
                crate::leanh::lean_ctor_set(v___x_7300_, 2, v___y_7294_);
                crate::leanh::lean_ctor_set(v___x_7300_, 3, v___y_7293_);
                crate::leanh::lean_ctor_set(v___x_7300_, 4, v___x_7296_);
                crate::leanh::lean_ctor_set(v___x_7300_, 5, v___x_7298_);
                crate::leanh::lean_ctor_set(v___x_7300_, 6, v___x_7299_);
                v___x_7301_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(
                    v_eval_7279_,
                    v_init_7282_,
                    v___x_7300_,
                    v_logExceptions_7280_,
                    v___y_7284_,
                    v___y_7285_,
                    v___y_7286_,
                    v___y_7287_,
                    v___y_7288_,
                    v___y_7289_,
                );
                return v___x_7301_;
            }
            2 => {
                v_fileName_7303_ = crate::leanh::lean_ctor_get(v___y_7288_, 0);
                v_fileMap_7304_ = crate::leanh::lean_ctor_get(v___y_7288_, 1);
                v_options_7305_ = crate::leanh::lean_ctor_get(v___y_7288_, 2);
                v_currRecDepth_7306_ = crate::leanh::lean_ctor_get(v___y_7288_, 3);
                v_maxRecDepth_7307_ = crate::leanh::lean_ctor_get(v___y_7288_, 4);
                v_ref_7308_ = crate::leanh::lean_ctor_get(v___y_7288_, 5);
                v_currNamespace_7309_ = crate::leanh::lean_ctor_get(v___y_7288_, 6);
                v_openDecls_7310_ = crate::leanh::lean_ctor_get(v___y_7288_, 7);
                v_initHeartbeats_7311_ = crate::leanh::lean_ctor_get(v___y_7288_, 8);
                v_maxHeartbeats_7312_ = crate::leanh::lean_ctor_get(v___y_7288_, 9);
                v_quotContext_7313_ = crate::leanh::lean_ctor_get(v___y_7288_, 10);
                v_currMacroScope_7314_ = crate::leanh::lean_ctor_get(v___y_7288_, 11);
                v_diag_7315_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7288_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7316_ = crate::leanh::lean_ctor_get(v___y_7288_, 12);
                v_suppressElabErrors_7317_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7288_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7318_ = crate::leanh::lean_ctor_get(v___y_7288_, 13);
                v_ref_7319_ = l_Lean_replaceRef(v_cfg_7283_, v_ref_7308_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_7318_);
                crate::leanh::lean_inc(v_cancelTk_x3f_7316_);
                crate::leanh::lean_inc(v_currMacroScope_7314_);
                crate::leanh::lean_inc(v_quotContext_7313_);
                crate::leanh::lean_inc(v_maxHeartbeats_7312_);
                crate::leanh::lean_inc(v_initHeartbeats_7311_);
                crate::leanh::lean_inc(v_openDecls_7310_);
                crate::leanh::lean_inc(v_currNamespace_7309_);
                crate::leanh::lean_inc(v_maxRecDepth_7307_);
                crate::leanh::lean_inc(v_currRecDepth_7306_);
                crate::leanh::lean_inc_ref(v_options_7305_);
                crate::leanh::lean_inc_ref(v_fileMap_7304_);
                crate::leanh::lean_inc_ref(v_fileName_7303_);
                v___x_7320_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_7320_, 0, v_fileName_7303_);
                crate::leanh::lean_ctor_set(v___x_7320_, 1, v_fileMap_7304_);
                crate::leanh::lean_ctor_set(v___x_7320_, 2, v_options_7305_);
                crate::leanh::lean_ctor_set(v___x_7320_, 3, v_currRecDepth_7306_);
                crate::leanh::lean_ctor_set(v___x_7320_, 4, v_maxRecDepth_7307_);
                crate::leanh::lean_ctor_set(v___x_7320_, 5, v_ref_7319_);
                crate::leanh::lean_ctor_set(v___x_7320_, 6, v_currNamespace_7309_);
                crate::leanh::lean_ctor_set(v___x_7320_, 7, v_openDecls_7310_);
                crate::leanh::lean_ctor_set(v___x_7320_, 8, v_initHeartbeats_7311_);
                crate::leanh::lean_ctor_set(v___x_7320_, 9, v_maxHeartbeats_7312_);
                crate::leanh::lean_ctor_set(v___x_7320_, 10, v_quotContext_7313_);
                crate::leanh::lean_ctor_set(v___x_7320_, 11, v_currMacroScope_7314_);
                crate::leanh::lean_ctor_set(v___x_7320_, 12, v_cancelTk_x3f_7316_);
                crate::leanh::lean_ctor_set(v___x_7320_, 13, v_inheritedTraceOptions_7318_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7320_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_7315_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7320_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7317_,
                );
                crate::leanh::lean_inc(v___y_7289_);
                crate::leanh::lean_inc(v___y_7287_);
                crate::leanh::lean_inc_ref(v___y_7286_);
                crate::leanh::lean_inc(v___y_7285_);
                crate::leanh::lean_inc_ref(v___y_7284_);
                v___x_7321_ = crate::leanh::lean_apply_9(
                    v_onErr_7281_,
                    v_init_7282_,
                    v_cfg_7283_,
                    v___y_7284_,
                    v___y_7285_,
                    v___y_7286_,
                    v___y_7287_,
                    v___x_7320_,
                    v___y_7289_,
                    crate::leanh::lean_box(0),
                );
                return v___x_7321_;
            }
            3 => {
                v___x_7348_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7349_ = lean_nat_dec_eq(v___x_7324_, v___x_7348_);
                crate::leanh::lean_dec(v___x_7324_);
                if v___x_7349_ == 0 {
                    crate::leanh::lean_dec(v___y_7346_);
                    crate::leanh::lean_dec_ref_known(v___x_7343_, 2);
                    crate::leanh::lean_dec_ref(v_eval_7279_);
                    state = 2;
                    continue;
                } else {
                    v___x_7350_ = l_Lean_Syntax_getArg(v_cfg_7283_, v___x_7325_);
                    v___x_7351_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(
                        v_atomAsIdent_7327_,
                        v___x_7350_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7351_) == 1 {
                        crate::leanh::lean_dec_ref(v_onErr_7281_);
                        if v_val_7347_ == 0 {
                            v_val_7352_ = crate::leanh::lean_ctor_get(v___x_7351_, 0);
                            crate::leanh::lean_inc(v_val_7352_);
                            crate::leanh::lean_dec_ref_known(v___x_7351_, 1);
                            v___x_7353_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10;
                            v___x_7354_ =
                                l_Lean_mkCIdentFrom(v___x_7343_, v___x_7353_, v___x_7326_);
                            crate::leanh::lean_dec_ref_known(v___x_7343_, 2);
                            v___y_7292_ = v_val_7352_;
                            v___y_7293_ = v___y_7346_;
                            v___y_7294_ = v___x_7354_;
                            state = 1;
                            continue;
                        } else {
                            v_val_7355_ = crate::leanh::lean_ctor_get(v___x_7351_, 0);
                            crate::leanh::lean_inc(v_val_7355_);
                            crate::leanh::lean_dec_ref_known(v___x_7351_, 1);
                            v___x_7356_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7;
                            v___x_7357_ =
                                l_Lean_mkCIdentFrom(v___x_7343_, v___x_7356_, v___x_7326_);
                            crate::leanh::lean_dec_ref_known(v___x_7343_, 2);
                            v___y_7292_ = v_val_7355_;
                            v___y_7293_ = v___y_7346_;
                            v___y_7294_ = v___x_7357_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_7351_);
                        crate::leanh::lean_dec(v___y_7346_);
                        crate::leanh::lean_dec_ref_known(v___x_7343_, 2);
                        crate::leanh::lean_dec_ref(v_eval_7279_);
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(
    mut v_eval_7387_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7388_: u8,
    mut v_onErr_7389_: *mut crate::leanh::LeanObject,
    mut v_as_7390_: *mut crate::leanh::LeanObject,
    mut v_i_7391_: usize,
    mut v_stop_7392_: usize,
    mut v_b_7393_: *mut crate::leanh::LeanObject,
    mut v___y_7394_: *mut crate::leanh::LeanObject,
    mut v___y_7395_: *mut crate::leanh::LeanObject,
    mut v___y_7396_: *mut crate::leanh::LeanObject,
    mut v___y_7397_: *mut crate::leanh::LeanObject,
    mut v___y_7398_: *mut crate::leanh::LeanObject,
    mut v___y_7399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7401_: u8 = 0;
    let mut v___x_7402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: usize = 0;
    let mut v___x_7406_: usize = 0;
    let mut v___x_7408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7401_ = lean_usize_dec_eq(v_i_7391_, v_stop_7392_);
                if v___x_7401_ == 0 {
                    v___x_7402_ = lean_array_uget_borrowed(v_as_7390_, v_i_7391_);
                    crate::leanh::lean_inc(v___x_7402_);
                    crate::leanh::lean_inc_ref(v_onErr_7389_);
                    crate::leanh::lean_inc_ref(v_eval_7387_);
                    v___x_7403_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7387_, v_logExceptions_7388_, v_onErr_7389_, v_b_7393_, v___x_7402_, v___y_7394_, v___y_7395_, v___y_7396_, v___y_7397_, v___y_7398_, v___y_7399_);
                    if crate::leanh::lean_obj_tag(v___x_7403_) == 0 {
                        v_a_7404_ = crate::leanh::lean_ctor_get(v___x_7403_, 0);
                        crate::leanh::lean_inc(v_a_7404_);
                        crate::leanh::lean_dec_ref_known(v___x_7403_, 1);
                        v___x_7405_ = 1usize;
                        v___x_7406_ = lean_usize_add(v_i_7391_, v___x_7405_);
                        v_i_7391_ = v___x_7406_;
                        v_b_7393_ = v_a_7404_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_onErr_7389_);
                        crate::leanh::lean_dec_ref(v_eval_7387_);
                        return v___x_7403_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_onErr_7389_);
                    crate::leanh::lean_dec_ref(v_eval_7387_);
                    v___x_7408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7408_, 0, v_b_7393_);
                    return v___x_7408_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_eval_7409_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7410_: *mut crate::leanh::LeanObject,
    mut v_onErr_7411_: *mut crate::leanh::LeanObject,
    mut v_as_7412_: *mut crate::leanh::LeanObject,
    mut v_i_7413_: *mut crate::leanh::LeanObject,
    mut v_stop_7414_: *mut crate::leanh::LeanObject,
    mut v_b_7415_: *mut crate::leanh::LeanObject,
    mut v___y_7416_: *mut crate::leanh::LeanObject,
    mut v___y_7417_: *mut crate::leanh::LeanObject,
    mut v___y_7418_: *mut crate::leanh::LeanObject,
    mut v___y_7419_: *mut crate::leanh::LeanObject,
    mut v___y_7420_: *mut crate::leanh::LeanObject,
    mut v___y_7421_: *mut crate::leanh::LeanObject,
    mut v___y_7422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_7423_: u8 = 0;
    let mut v_i_boxed_7424_: usize = 0;
    let mut v_stop_boxed_7425_: usize = 0;
    let mut v_res_7426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7423_ = (crate::leanh::lean_unbox(v_logExceptions_7410_) as u8);
    v_i_boxed_7424_ = crate::leanh::lean_unbox_usize(v_i_7413_);
    crate::leanh::lean_dec(v_i_7413_);
    v_stop_boxed_7425_ = crate::leanh::lean_unbox_usize(v_stop_7414_);
    crate::leanh::lean_dec(v_stop_7414_);
    v_res_7426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_7409_, v_logExceptions_boxed_7423_, v_onErr_7411_, v_as_7412_, v_i_boxed_7424_, v_stop_boxed_7425_, v_b_7415_, v___y_7416_, v___y_7417_, v___y_7418_, v___y_7419_, v___y_7420_, v___y_7421_);
    crate::leanh::lean_dec(v___y_7421_);
    crate::leanh::lean_dec_ref(v___y_7420_);
    crate::leanh::lean_dec(v___y_7419_);
    crate::leanh::lean_dec_ref(v___y_7418_);
    crate::leanh::lean_dec(v___y_7417_);
    crate::leanh::lean_dec_ref(v___y_7416_);
    crate::leanh::lean_dec_ref(v_as_7412_);
    return v_res_7426_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg___boxed(
    mut v_eval_7427_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7428_: *mut crate::leanh::LeanObject,
    mut v_onErr_7429_: *mut crate::leanh::LeanObject,
    mut v_init_7430_: *mut crate::leanh::LeanObject,
    mut v_cfgs_7431_: *mut crate::leanh::LeanObject,
    mut v___y_7432_: *mut crate::leanh::LeanObject,
    mut v___y_7433_: *mut crate::leanh::LeanObject,
    mut v___y_7434_: *mut crate::leanh::LeanObject,
    mut v___y_7435_: *mut crate::leanh::LeanObject,
    mut v___y_7436_: *mut crate::leanh::LeanObject,
    mut v___y_7437_: *mut crate::leanh::LeanObject,
    mut v___y_7438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_7439_: u8 = 0;
    let mut v_res_7440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7439_ = (crate::leanh::lean_unbox(v_logExceptions_7428_) as u8);
    v_res_7440_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7427_, v_logExceptions_boxed_7439_, v_onErr_7429_, v_init_7430_, v_cfgs_7431_, v___y_7432_, v___y_7433_, v___y_7434_, v___y_7435_, v___y_7436_, v___y_7437_);
    crate::leanh::lean_dec(v___y_7437_);
    crate::leanh::lean_dec_ref(v___y_7436_);
    crate::leanh::lean_dec(v___y_7435_);
    crate::leanh::lean_dec_ref(v___y_7434_);
    crate::leanh::lean_dec(v___y_7433_);
    crate::leanh::lean_dec_ref(v___y_7432_);
    crate::leanh::lean_dec_ref(v_cfgs_7431_);
    return v_res_7440_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___boxed(
    mut v_eval_7441_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7442_: *mut crate::leanh::LeanObject,
    mut v_onErr_7443_: *mut crate::leanh::LeanObject,
    mut v_init_7444_: *mut crate::leanh::LeanObject,
    mut v_cfg_7445_: *mut crate::leanh::LeanObject,
    mut v___y_7446_: *mut crate::leanh::LeanObject,
    mut v___y_7447_: *mut crate::leanh::LeanObject,
    mut v___y_7448_: *mut crate::leanh::LeanObject,
    mut v___y_7449_: *mut crate::leanh::LeanObject,
    mut v___y_7450_: *mut crate::leanh::LeanObject,
    mut v___y_7451_: *mut crate::leanh::LeanObject,
    mut v___y_7452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_7453_: u8 = 0;
    let mut v_res_7454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7453_ = (crate::leanh::lean_unbox(v_logExceptions_7442_) as u8);
    v_res_7454_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7441_, v_logExceptions_boxed_7453_, v_onErr_7443_, v_init_7444_, v_cfg_7445_, v___y_7446_, v___y_7447_, v___y_7448_, v___y_7449_, v___y_7450_, v___y_7451_);
    crate::leanh::lean_dec(v___y_7451_);
    crate::leanh::lean_dec_ref(v___y_7450_);
    crate::leanh::lean_dec(v___y_7449_);
    crate::leanh::lean_dec_ref(v___y_7448_);
    crate::leanh::lean_dec(v___y_7447_);
    crate::leanh::lean_dec_ref(v___y_7446_);
    return v_res_7454_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(
    mut v_eval_7455_: *mut crate::leanh::LeanObject,
    mut v_init_7456_: *mut crate::leanh::LeanObject,
    mut v_cfg_7457_: *mut crate::leanh::LeanObject,
    mut v_onErr_7458_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7459_: u8,
    mut v_a_7460_: *mut crate::leanh::LeanObject,
    mut v_a_7461_: *mut crate::leanh::LeanObject,
    mut v_a_7462_: *mut crate::leanh::LeanObject,
    mut v_a_7463_: *mut crate::leanh::LeanObject,
    mut v_a_7464_: *mut crate::leanh::LeanObject,
    mut v_a_7465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7467_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7455_, v_logExceptions_7459_, v_onErr_7458_, v_init_7456_, v_cfg_7457_, v_a_7460_, v_a_7461_, v_a_7462_, v_a_7463_, v_a_7464_, v_a_7465_);
    return v___x_7467_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg___boxed(
    mut v_eval_7468_: *mut crate::leanh::LeanObject,
    mut v_init_7469_: *mut crate::leanh::LeanObject,
    mut v_cfg_7470_: *mut crate::leanh::LeanObject,
    mut v_onErr_7471_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7472_: *mut crate::leanh::LeanObject,
    mut v_a_7473_: *mut crate::leanh::LeanObject,
    mut v_a_7474_: *mut crate::leanh::LeanObject,
    mut v_a_7475_: *mut crate::leanh::LeanObject,
    mut v_a_7476_: *mut crate::leanh::LeanObject,
    mut v_a_7477_: *mut crate::leanh::LeanObject,
    mut v_a_7478_: *mut crate::leanh::LeanObject,
    mut v_a_7479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_7480_: u8 = 0;
    let mut v_res_7481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7480_ = (crate::leanh::lean_unbox(v_logExceptions_7472_) as u8);
    v_res_7481_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(
        v_eval_7468_,
        v_init_7469_,
        v_cfg_7470_,
        v_onErr_7471_,
        v_logExceptions_boxed_7480_,
        v_a_7473_,
        v_a_7474_,
        v_a_7475_,
        v_a_7476_,
        v_a_7477_,
        v_a_7478_,
    );
    crate::leanh::lean_dec(v_a_7478_);
    crate::leanh::lean_dec_ref(v_a_7477_);
    crate::leanh::lean_dec(v_a_7476_);
    crate::leanh::lean_dec_ref(v_a_7475_);
    crate::leanh::lean_dec(v_a_7474_);
    crate::leanh::lean_dec_ref(v_a_7473_);
    return v_res_7481_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(
    mut v_00_u03b1_7482_: *mut crate::leanh::LeanObject,
    mut v_eval_7483_: *mut crate::leanh::LeanObject,
    mut v_init_7484_: *mut crate::leanh::LeanObject,
    mut v_cfg_7485_: *mut crate::leanh::LeanObject,
    mut v_onErr_7486_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7487_: u8,
    mut v_a_7488_: *mut crate::leanh::LeanObject,
    mut v_a_7489_: *mut crate::leanh::LeanObject,
    mut v_a_7490_: *mut crate::leanh::LeanObject,
    mut v_a_7491_: *mut crate::leanh::LeanObject,
    mut v_a_7492_: *mut crate::leanh::LeanObject,
    mut v_a_7493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7495_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7483_, v_logExceptions_7487_, v_onErr_7486_, v_init_7484_, v_cfg_7485_, v_a_7488_, v_a_7489_, v_a_7490_, v_a_7491_, v_a_7492_, v_a_7493_);
    return v___x_7495_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___boxed(
    mut v_00_u03b1_7496_: *mut crate::leanh::LeanObject,
    mut v_eval_7497_: *mut crate::leanh::LeanObject,
    mut v_init_7498_: *mut crate::leanh::LeanObject,
    mut v_cfg_7499_: *mut crate::leanh::LeanObject,
    mut v_onErr_7500_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7501_: *mut crate::leanh::LeanObject,
    mut v_a_7502_: *mut crate::leanh::LeanObject,
    mut v_a_7503_: *mut crate::leanh::LeanObject,
    mut v_a_7504_: *mut crate::leanh::LeanObject,
    mut v_a_7505_: *mut crate::leanh::LeanObject,
    mut v_a_7506_: *mut crate::leanh::LeanObject,
    mut v_a_7507_: *mut crate::leanh::LeanObject,
    mut v_a_7508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_7509_: u8 = 0;
    let mut v_res_7510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7509_ = (crate::leanh::lean_unbox(v_logExceptions_7501_) as u8);
    v_res_7510_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(
        v_00_u03b1_7496_,
        v_eval_7497_,
        v_init_7498_,
        v_cfg_7499_,
        v_onErr_7500_,
        v_logExceptions_boxed_7509_,
        v_a_7502_,
        v_a_7503_,
        v_a_7504_,
        v_a_7505_,
        v_a_7506_,
        v_a_7507_,
    );
    crate::leanh::lean_dec(v_a_7507_);
    crate::leanh::lean_dec_ref(v_a_7506_);
    crate::leanh::lean_dec(v_a_7505_);
    crate::leanh::lean_dec_ref(v_a_7504_);
    crate::leanh::lean_dec(v_a_7503_);
    crate::leanh::lean_dec_ref(v_a_7502_);
    return v_res_7510_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(
    mut v_00_u03b1_7511_: *mut crate::leanh::LeanObject,
    mut v_eval_7512_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7513_: u8,
    mut v_onErr_7514_: *mut crate::leanh::LeanObject,
    mut v_init_7515_: *mut crate::leanh::LeanObject,
    mut v_cfg_7516_: *mut crate::leanh::LeanObject,
    mut v___y_7517_: *mut crate::leanh::LeanObject,
    mut v___y_7518_: *mut crate::leanh::LeanObject,
    mut v___y_7519_: *mut crate::leanh::LeanObject,
    mut v___y_7520_: *mut crate::leanh::LeanObject,
    mut v___y_7521_: *mut crate::leanh::LeanObject,
    mut v___y_7522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7524_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7512_, v_logExceptions_7513_, v_onErr_7514_, v_init_7515_, v_cfg_7516_, v___y_7517_, v___y_7518_, v___y_7519_, v___y_7520_, v___y_7521_, v___y_7522_);
    return v___x_7524_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___boxed(
    mut v_00_u03b1_7525_: *mut crate::leanh::LeanObject,
    mut v_eval_7526_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7527_: *mut crate::leanh::LeanObject,
    mut v_onErr_7528_: *mut crate::leanh::LeanObject,
    mut v_init_7529_: *mut crate::leanh::LeanObject,
    mut v_cfg_7530_: *mut crate::leanh::LeanObject,
    mut v___y_7531_: *mut crate::leanh::LeanObject,
    mut v___y_7532_: *mut crate::leanh::LeanObject,
    mut v___y_7533_: *mut crate::leanh::LeanObject,
    mut v___y_7534_: *mut crate::leanh::LeanObject,
    mut v___y_7535_: *mut crate::leanh::LeanObject,
    mut v___y_7536_: *mut crate::leanh::LeanObject,
    mut v___y_7537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_7538_: u8 = 0;
    let mut v_res_7539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7538_ = (crate::leanh::lean_unbox(v_logExceptions_7527_) as u8);
    v_res_7539_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(v_00_u03b1_7525_, v_eval_7526_, v_logExceptions_boxed_7538_, v_onErr_7528_, v_init_7529_, v_cfg_7530_, v___y_7531_, v___y_7532_, v___y_7533_, v___y_7534_, v___y_7535_, v___y_7536_);
    crate::leanh::lean_dec(v___y_7536_);
    crate::leanh::lean_dec_ref(v___y_7535_);
    crate::leanh::lean_dec(v___y_7534_);
    crate::leanh::lean_dec_ref(v___y_7533_);
    crate::leanh::lean_dec(v___y_7532_);
    crate::leanh::lean_dec_ref(v___y_7531_);
    return v_res_7539_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(
    mut v_00_u03b1_7540_: *mut crate::leanh::LeanObject,
    mut v_eval_7541_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7542_: u8,
    mut v_onErr_7543_: *mut crate::leanh::LeanObject,
    mut v_init_7544_: *mut crate::leanh::LeanObject,
    mut v_cfgs_7545_: *mut crate::leanh::LeanObject,
    mut v___y_7546_: *mut crate::leanh::LeanObject,
    mut v___y_7547_: *mut crate::leanh::LeanObject,
    mut v___y_7548_: *mut crate::leanh::LeanObject,
    mut v___y_7549_: *mut crate::leanh::LeanObject,
    mut v___y_7550_: *mut crate::leanh::LeanObject,
    mut v___y_7551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7553_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7541_, v_logExceptions_7542_, v_onErr_7543_, v_init_7544_, v_cfgs_7545_, v___y_7546_, v___y_7547_, v___y_7548_, v___y_7549_, v___y_7550_, v___y_7551_);
    return v___x_7553_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___boxed(
    mut v_00_u03b1_7554_: *mut crate::leanh::LeanObject,
    mut v_eval_7555_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7556_: *mut crate::leanh::LeanObject,
    mut v_onErr_7557_: *mut crate::leanh::LeanObject,
    mut v_init_7558_: *mut crate::leanh::LeanObject,
    mut v_cfgs_7559_: *mut crate::leanh::LeanObject,
    mut v___y_7560_: *mut crate::leanh::LeanObject,
    mut v___y_7561_: *mut crate::leanh::LeanObject,
    mut v___y_7562_: *mut crate::leanh::LeanObject,
    mut v___y_7563_: *mut crate::leanh::LeanObject,
    mut v___y_7564_: *mut crate::leanh::LeanObject,
    mut v___y_7565_: *mut crate::leanh::LeanObject,
    mut v___y_7566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_7567_: u8 = 0;
    let mut v_res_7568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7567_ = (crate::leanh::lean_unbox(v_logExceptions_7556_) as u8);
    v_res_7568_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(v_00_u03b1_7554_, v_eval_7555_, v_logExceptions_boxed_7567_, v_onErr_7557_, v_init_7558_, v_cfgs_7559_, v___y_7560_, v___y_7561_, v___y_7562_, v___y_7563_, v___y_7564_, v___y_7565_);
    crate::leanh::lean_dec(v___y_7565_);
    crate::leanh::lean_dec_ref(v___y_7564_);
    crate::leanh::lean_dec(v___y_7563_);
    crate::leanh::lean_dec_ref(v___y_7562_);
    crate::leanh::lean_dec(v___y_7561_);
    crate::leanh::lean_dec_ref(v___y_7560_);
    crate::leanh::lean_dec_ref(v_cfgs_7559_);
    return v_res_7568_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(
    mut v_s_7569_: *mut crate::leanh::LeanObject,
    mut v_inst_7570_: *mut crate::leanh::LeanObject,
    mut v_R_7571_: *mut crate::leanh::LeanObject,
    mut v_a_7572_: *mut crate::leanh::LeanObject,
    mut v_b_7573_: u8,
    mut v_c_7574_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7575_: u8 = 0;
    v___x_7575_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_7569_, v_a_7572_, v_b_7573_);
    return v___x_7575_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___boxed(
    mut v_s_7576_: *mut crate::leanh::LeanObject,
    mut v_inst_7577_: *mut crate::leanh::LeanObject,
    mut v_R_7578_: *mut crate::leanh::LeanObject,
    mut v_a_7579_: *mut crate::leanh::LeanObject,
    mut v_b_7580_: *mut crate::leanh::LeanObject,
    mut v_c_7581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_7582_: u8 = 0;
    let mut v_res_7583_: u8 = 0;
    let mut v_r_7584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_7582_ = (crate::leanh::lean_unbox(v_b_7580_) as u8);
    v_res_7583_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(v_s_7576_, v_inst_7577_, v_R_7578_, v_a_7579_, v_b_boxed_7582_, v_c_7581_);
    crate::leanh::lean_dec_ref(v_s_7576_);
    v_r_7584_ = crate::leanh::lean_box((v_res_7583_) as usize);
    return v_r_7584_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(
    mut v_00_u03b1_7585_: *mut crate::leanh::LeanObject,
    mut v_eval_7586_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7587_: u8,
    mut v_onErr_7588_: *mut crate::leanh::LeanObject,
    mut v_as_7589_: *mut crate::leanh::LeanObject,
    mut v_i_7590_: usize,
    mut v_stop_7591_: usize,
    mut v_b_7592_: *mut crate::leanh::LeanObject,
    mut v___y_7593_: *mut crate::leanh::LeanObject,
    mut v___y_7594_: *mut crate::leanh::LeanObject,
    mut v___y_7595_: *mut crate::leanh::LeanObject,
    mut v___y_7596_: *mut crate::leanh::LeanObject,
    mut v___y_7597_: *mut crate::leanh::LeanObject,
    mut v___y_7598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_7586_, v_logExceptions_7587_, v_onErr_7588_, v_as_7589_, v_i_7590_, v_stop_7591_, v_b_7592_, v___y_7593_, v___y_7594_, v___y_7595_, v___y_7596_, v___y_7597_, v___y_7598_);
    return v___x_7600_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_7601_: *mut crate::leanh::LeanObject,
    mut v_eval_7602_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7603_: *mut crate::leanh::LeanObject,
    mut v_onErr_7604_: *mut crate::leanh::LeanObject,
    mut v_as_7605_: *mut crate::leanh::LeanObject,
    mut v_i_7606_: *mut crate::leanh::LeanObject,
    mut v_stop_7607_: *mut crate::leanh::LeanObject,
    mut v_b_7608_: *mut crate::leanh::LeanObject,
    mut v___y_7609_: *mut crate::leanh::LeanObject,
    mut v___y_7610_: *mut crate::leanh::LeanObject,
    mut v___y_7611_: *mut crate::leanh::LeanObject,
    mut v___y_7612_: *mut crate::leanh::LeanObject,
    mut v___y_7613_: *mut crate::leanh::LeanObject,
    mut v___y_7614_: *mut crate::leanh::LeanObject,
    mut v___y_7615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_7616_: u8 = 0;
    let mut v_i_boxed_7617_: usize = 0;
    let mut v_stop_boxed_7618_: usize = 0;
    let mut v_res_7619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7616_ = (crate::leanh::lean_unbox(v_logExceptions_7603_) as u8);
    v_i_boxed_7617_ = crate::leanh::lean_unbox_usize(v_i_7606_);
    crate::leanh::lean_dec(v_i_7606_);
    v_stop_boxed_7618_ = crate::leanh::lean_unbox_usize(v_stop_7607_);
    crate::leanh::lean_dec(v_stop_7607_);
    v_res_7619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(v_00_u03b1_7601_, v_eval_7602_, v_logExceptions_boxed_7616_, v_onErr_7604_, v_as_7605_, v_i_boxed_7617_, v_stop_boxed_7618_, v_b_7608_, v___y_7609_, v___y_7610_, v___y_7611_, v___y_7612_, v___y_7613_, v___y_7614_);
    crate::leanh::lean_dec(v___y_7614_);
    crate::leanh::lean_dec_ref(v___y_7613_);
    crate::leanh::lean_dec(v___y_7612_);
    crate::leanh::lean_dec_ref(v___y_7611_);
    crate::leanh::lean_dec(v___y_7610_);
    crate::leanh::lean_dec_ref(v___y_7609_);
    crate::leanh::lean_dec_ref(v_as_7605_);
    return v_res_7619_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(
    mut v_eval_7620_: *mut crate::leanh::LeanObject,
    mut v_init_7621_: *mut crate::leanh::LeanObject,
    mut v_cfgs_7622_: *mut crate::leanh::LeanObject,
    mut v_onErr_7623_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7624_: u8,
    mut v_a_7625_: *mut crate::leanh::LeanObject,
    mut v_a_7626_: *mut crate::leanh::LeanObject,
    mut v_a_7627_: *mut crate::leanh::LeanObject,
    mut v_a_7628_: *mut crate::leanh::LeanObject,
    mut v_a_7629_: *mut crate::leanh::LeanObject,
    mut v_a_7630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7632_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7620_, v_logExceptions_7624_, v_onErr_7623_, v_init_7621_, v_cfgs_7622_, v_a_7625_, v_a_7626_, v_a_7627_, v_a_7628_, v_a_7629_, v_a_7630_);
    return v___x_7632_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg___boxed(
    mut v_eval_7633_: *mut crate::leanh::LeanObject,
    mut v_init_7634_: *mut crate::leanh::LeanObject,
    mut v_cfgs_7635_: *mut crate::leanh::LeanObject,
    mut v_onErr_7636_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7637_: *mut crate::leanh::LeanObject,
    mut v_a_7638_: *mut crate::leanh::LeanObject,
    mut v_a_7639_: *mut crate::leanh::LeanObject,
    mut v_a_7640_: *mut crate::leanh::LeanObject,
    mut v_a_7641_: *mut crate::leanh::LeanObject,
    mut v_a_7642_: *mut crate::leanh::LeanObject,
    mut v_a_7643_: *mut crate::leanh::LeanObject,
    mut v_a_7644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_7645_: u8 = 0;
    let mut v_res_7646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7645_ = (crate::leanh::lean_unbox(v_logExceptions_7637_) as u8);
    v_res_7646_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(
        v_eval_7633_,
        v_init_7634_,
        v_cfgs_7635_,
        v_onErr_7636_,
        v_logExceptions_boxed_7645_,
        v_a_7638_,
        v_a_7639_,
        v_a_7640_,
        v_a_7641_,
        v_a_7642_,
        v_a_7643_,
    );
    crate::leanh::lean_dec(v_a_7643_);
    crate::leanh::lean_dec_ref(v_a_7642_);
    crate::leanh::lean_dec(v_a_7641_);
    crate::leanh::lean_dec_ref(v_a_7640_);
    crate::leanh::lean_dec(v_a_7639_);
    crate::leanh::lean_dec_ref(v_a_7638_);
    crate::leanh::lean_dec_ref(v_cfgs_7635_);
    return v_res_7646_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(
    mut v_00_u03b1_7647_: *mut crate::leanh::LeanObject,
    mut v_eval_7648_: *mut crate::leanh::LeanObject,
    mut v_init_7649_: *mut crate::leanh::LeanObject,
    mut v_cfgs_7650_: *mut crate::leanh::LeanObject,
    mut v_onErr_7651_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7652_: u8,
    mut v_a_7653_: *mut crate::leanh::LeanObject,
    mut v_a_7654_: *mut crate::leanh::LeanObject,
    mut v_a_7655_: *mut crate::leanh::LeanObject,
    mut v_a_7656_: *mut crate::leanh::LeanObject,
    mut v_a_7657_: *mut crate::leanh::LeanObject,
    mut v_a_7658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7660_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7648_, v_logExceptions_7652_, v_onErr_7651_, v_init_7649_, v_cfgs_7650_, v_a_7653_, v_a_7654_, v_a_7655_, v_a_7656_, v_a_7657_, v_a_7658_);
    return v___x_7660_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___boxed(
    mut v_00_u03b1_7661_: *mut crate::leanh::LeanObject,
    mut v_eval_7662_: *mut crate::leanh::LeanObject,
    mut v_init_7663_: *mut crate::leanh::LeanObject,
    mut v_cfgs_7664_: *mut crate::leanh::LeanObject,
    mut v_onErr_7665_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_7666_: *mut crate::leanh::LeanObject,
    mut v_a_7667_: *mut crate::leanh::LeanObject,
    mut v_a_7668_: *mut crate::leanh::LeanObject,
    mut v_a_7669_: *mut crate::leanh::LeanObject,
    mut v_a_7670_: *mut crate::leanh::LeanObject,
    mut v_a_7671_: *mut crate::leanh::LeanObject,
    mut v_a_7672_: *mut crate::leanh::LeanObject,
    mut v_a_7673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_7674_: u8 = 0;
    let mut v_res_7675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7674_ = (crate::leanh::lean_unbox(v_logExceptions_7666_) as u8);
    v_res_7675_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(
        v_00_u03b1_7661_,
        v_eval_7662_,
        v_init_7663_,
        v_cfgs_7664_,
        v_onErr_7665_,
        v_logExceptions_boxed_7674_,
        v_a_7667_,
        v_a_7668_,
        v_a_7669_,
        v_a_7670_,
        v_a_7671_,
        v_a_7672_,
    );
    crate::leanh::lean_dec(v_a_7672_);
    crate::leanh::lean_dec_ref(v_a_7671_);
    crate::leanh::lean_dec(v_a_7670_);
    crate::leanh::lean_dec_ref(v_a_7669_);
    crate::leanh::lean_dec(v_a_7668_);
    crate::leanh::lean_dec_ref(v_a_7667_);
    crate::leanh::lean_dec_ref(v_cfgs_7664_);
    return v_res_7675_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(
    mut v_x_7676_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7677_: u8 = 0;
    v___x_7677_ = 0;
    return v___x_7677_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed(
    mut v_x_7678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7679_: u8 = 0;
    let mut v_r_7680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7679_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(v_x_7678_);
    crate::leanh::lean_dec(v_x_7678_);
    v_r_7680_ = crate::leanh::lean_box((v_res_7679_) as usize);
    return v_r_7680_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(
    mut v___x_7681_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_7682_: *mut crate::leanh::LeanObject,
    mut v_sz_7683_: usize,
    mut v_i_7684_: usize,
    mut v_bs_7685_: *mut crate::leanh::LeanObject,
    mut v___y_7686_: *mut crate::leanh::LeanObject,
    mut v___y_7687_: *mut crate::leanh::LeanObject,
    mut v___y_7688_: *mut crate::leanh::LeanObject,
    mut v___y_7689_: *mut crate::leanh::LeanObject,
    mut v___y_7690_: *mut crate::leanh::LeanObject,
    mut v___y_7691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7693_: u8 = 0;
    let mut v___x_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_7695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: usize = 0;
    let mut v___x_7704_: usize = 0;
    let mut v___x_7705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_7707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7713_: u8 = 0;
    let mut v___x_7715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7693_ = lean_usize_dec_lt(v_i_7684_, v_sz_7683_);
                if v___x_7693_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_x3f_7682_);
                    v___x_7694_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7694_, 0, v_bs_7685_);
                    return v___x_7694_;
                } else {
                    v_assignment_7695_ = crate::leanh::lean_ctor_get(v___x_7681_, 0);
                    crate::leanh::lean_inc_ref(v_ctx_x3f_7682_);
                    crate::leanh::lean_inc(v___y_7691_);
                    crate::leanh::lean_inc_ref(v___y_7690_);
                    crate::leanh::lean_inc(v___y_7689_);
                    crate::leanh::lean_inc_ref(v___y_7688_);
                    crate::leanh::lean_inc(v___y_7687_);
                    crate::leanh::lean_inc_ref(v___y_7686_);
                    v___x_7696_ = crate::leanh::lean_apply_7(
                        v_ctx_x3f_7682_,
                        v___y_7686_,
                        v___y_7687_,
                        v___y_7688_,
                        v___y_7689_,
                        v___y_7690_,
                        v___y_7691_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_7696_) == 0 {
                        v_a_7697_ = crate::leanh::lean_ctor_get(v___x_7696_, 0);
                        crate::leanh::lean_inc(v_a_7697_);
                        crate::leanh::lean_dec_ref_known(v___x_7696_, 1);
                        v_v_7698_ = lean_array_uget(v_bs_7685_, v_i_7684_);
                        v___x_7699_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_7700_ = lean_array_uset(v_bs_7685_, v_i_7684_, v___x_7699_);
                        v_tree_7707_ =
                            l_Lean_Elab_InfoTree_substitute(v_v_7698_, v_assignment_7695_);
                        if crate::leanh::lean_obj_tag(v_a_7697_) == 0 {
                            v_a_7702_ = v_tree_7707_;
                            state = 1;
                            continue;
                        } else {
                            v_val_7708_ = crate::leanh::lean_ctor_get(v_a_7697_, 0);
                            crate::leanh::lean_inc(v_val_7708_);
                            crate::leanh::lean_dec_ref_known(v_a_7697_, 1);
                            v___x_7709_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7709_, 0, v_val_7708_);
                            crate::leanh::lean_ctor_set(v___x_7709_, 1, v_tree_7707_);
                            v_a_7702_ = v___x_7709_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_7685_);
                        crate::leanh::lean_dec_ref(v_ctx_x3f_7682_);
                        v_a_7710_ = crate::leanh::lean_ctor_get(v___x_7696_, 0);
                        v_isSharedCheck_7717_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7696_)) as u8;
                        if v_isSharedCheck_7717_ == 0 {
                            v___x_7712_ = v___x_7696_;
                            v_isShared_7713_ = v_isSharedCheck_7717_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7710_);
                            crate::leanh::lean_dec(v___x_7696_);
                            v___x_7712_ = crate::leanh::lean_box(0);
                            v_isShared_7713_ = v_isSharedCheck_7717_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7703_ = 1usize;
                v___x_7704_ = lean_usize_add(v_i_7684_, v___x_7703_);
                v___x_7705_ = lean_array_uset(v_bs_x27_7700_, v_i_7684_, v_a_7702_);
                v_i_7684_ = v___x_7704_;
                v_bs_7685_ = v___x_7705_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_7713_ == 0 {
                    v___x_7715_ = v___x_7712_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7716_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 0, v_a_7710_);
                    v___x_7715_ = v_reuseFailAlloc_7716_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7715_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v___x_7718_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_7719_: *mut crate::leanh::LeanObject,
    mut v_sz_7720_: *mut crate::leanh::LeanObject,
    mut v_i_7721_: *mut crate::leanh::LeanObject,
    mut v_bs_7722_: *mut crate::leanh::LeanObject,
    mut v___y_7723_: *mut crate::leanh::LeanObject,
    mut v___y_7724_: *mut crate::leanh::LeanObject,
    mut v___y_7725_: *mut crate::leanh::LeanObject,
    mut v___y_7726_: *mut crate::leanh::LeanObject,
    mut v___y_7727_: *mut crate::leanh::LeanObject,
    mut v___y_7728_: *mut crate::leanh::LeanObject,
    mut v___y_7729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7730_: usize = 0;
    let mut v_i_boxed_7731_: usize = 0;
    let mut v_res_7732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7730_ = crate::leanh::lean_unbox_usize(v_sz_7720_);
    crate::leanh::lean_dec(v_sz_7720_);
    v_i_boxed_7731_ = crate::leanh::lean_unbox_usize(v_i_7721_);
    crate::leanh::lean_dec(v_i_7721_);
    v_res_7732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_7718_, v_ctx_x3f_7719_, v_sz_boxed_7730_, v_i_boxed_7731_, v_bs_7722_, v___y_7723_, v___y_7724_, v___y_7725_, v___y_7726_, v___y_7727_, v___y_7728_);
    crate::leanh::lean_dec(v___y_7728_);
    crate::leanh::lean_dec_ref(v___y_7727_);
    crate::leanh::lean_dec(v___y_7726_);
    crate::leanh::lean_dec_ref(v___y_7725_);
    crate::leanh::lean_dec(v___y_7724_);
    crate::leanh::lean_dec_ref(v___y_7723_);
    crate::leanh::lean_dec_ref(v___x_7718_);
    return v_res_7732_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(
    mut v___x_7733_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_7734_: *mut crate::leanh::LeanObject,
    mut v_x_7735_: *mut crate::leanh::LeanObject,
    mut v___y_7736_: *mut crate::leanh::LeanObject,
    mut v___y_7737_: *mut crate::leanh::LeanObject,
    mut v___y_7738_: *mut crate::leanh::LeanObject,
    mut v___y_7739_: *mut crate::leanh::LeanObject,
    mut v___y_7740_: *mut crate::leanh::LeanObject,
    mut v___y_7741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_7743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7746_: u8 = 0;
    let mut v_sz_7747_: usize = 0;
    let mut v___x_7748_: usize = 0;
    let mut v___x_7749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7753_: u8 = 0;
    let mut v___x_7755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7760_: u8 = 0;
    let mut v_a_7761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7764_: u8 = 0;
    let mut v___x_7766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7768_: u8 = 0;
    let mut v_isSharedCheck_7769_: u8 = 0;
    let mut v_vs_7770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7773_: u8 = 0;
    let mut v_sz_7774_: usize = 0;
    let mut v___x_7775_: usize = 0;
    let mut v___x_7776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7780_: u8 = 0;
    let mut v___x_7782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7787_: u8 = 0;
    let mut v_a_7788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7791_: u8 = 0;
    let mut v___x_7793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7795_: u8 = 0;
    let mut v_isSharedCheck_7796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7735_) == 0 {
                    v_cs_7743_ = crate::leanh::lean_ctor_get(v_x_7735_, 0);
                    v_isSharedCheck_7769_ = (!crate::leanh::lean_is_exclusive(v_x_7735_)) as u8;
                    if v_isSharedCheck_7769_ == 0 {
                        v___x_7745_ = v_x_7735_;
                        v_isShared_7746_ = v_isSharedCheck_7769_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cs_7743_);
                        crate::leanh::lean_dec(v_x_7735_);
                        v___x_7745_ = crate::leanh::lean_box(0);
                        v_isShared_7746_ = v_isSharedCheck_7769_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_7770_ = crate::leanh::lean_ctor_get(v_x_7735_, 0);
                    v_isSharedCheck_7796_ = (!crate::leanh::lean_is_exclusive(v_x_7735_)) as u8;
                    if v_isSharedCheck_7796_ == 0 {
                        v___x_7772_ = v_x_7735_;
                        v_isShared_7773_ = v_isSharedCheck_7796_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_7770_);
                        crate::leanh::lean_dec(v_x_7735_);
                        v___x_7772_ = crate::leanh::lean_box(0);
                        v_isShared_7773_ = v_isSharedCheck_7796_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_7747_ = lean_array_size(v_cs_7743_);
                v___x_7748_ = 0usize;
                v___x_7749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_7733_, v_ctx_x3f_7734_, v_sz_7747_, v___x_7748_, v_cs_7743_, v___y_7736_, v___y_7737_, v___y_7738_, v___y_7739_, v___y_7740_, v___y_7741_);
                if crate::leanh::lean_obj_tag(v___x_7749_) == 0 {
                    v_a_7750_ = crate::leanh::lean_ctor_get(v___x_7749_, 0);
                    v_isSharedCheck_7760_ = (!crate::leanh::lean_is_exclusive(v___x_7749_)) as u8;
                    if v_isSharedCheck_7760_ == 0 {
                        v___x_7752_ = v___x_7749_;
                        v_isShared_7753_ = v_isSharedCheck_7760_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7750_);
                        crate::leanh::lean_dec(v___x_7749_);
                        v___x_7752_ = crate::leanh::lean_box(0);
                        v_isShared_7753_ = v_isSharedCheck_7760_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7745_);
                    v_a_7761_ = crate::leanh::lean_ctor_get(v___x_7749_, 0);
                    v_isSharedCheck_7768_ = (!crate::leanh::lean_is_exclusive(v___x_7749_)) as u8;
                    if v_isSharedCheck_7768_ == 0 {
                        v___x_7763_ = v___x_7749_;
                        v_isShared_7764_ = v_isSharedCheck_7768_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7761_);
                        crate::leanh::lean_dec(v___x_7749_);
                        v___x_7763_ = crate::leanh::lean_box(0);
                        v_isShared_7764_ = v_isSharedCheck_7768_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7746_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7745_, 0, v_a_7750_);
                    v___x_7755_ = v___x_7745_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7759_, 0, v_a_7750_);
                    v___x_7755_ = v_reuseFailAlloc_7759_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7753_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7752_, 0, v___x_7755_);
                    v___x_7757_ = v___x_7752_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7758_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7758_, 0, v___x_7755_);
                    v___x_7757_ = v_reuseFailAlloc_7758_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7757_;
            }
            5 => {
                if v_isShared_7764_ == 0 {
                    v___x_7766_ = v___x_7763_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7767_, 0, v_a_7761_);
                    v___x_7766_ = v_reuseFailAlloc_7767_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7766_;
            }
            7 => {
                v_sz_7774_ = lean_array_size(v_vs_7770_);
                v___x_7775_ = 0usize;
                v___x_7776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_7733_, v_ctx_x3f_7734_, v_sz_7774_, v___x_7775_, v_vs_7770_, v___y_7736_, v___y_7737_, v___y_7738_, v___y_7739_, v___y_7740_, v___y_7741_);
                if crate::leanh::lean_obj_tag(v___x_7776_) == 0 {
                    v_a_7777_ = crate::leanh::lean_ctor_get(v___x_7776_, 0);
                    v_isSharedCheck_7787_ = (!crate::leanh::lean_is_exclusive(v___x_7776_)) as u8;
                    if v_isSharedCheck_7787_ == 0 {
                        v___x_7779_ = v___x_7776_;
                        v_isShared_7780_ = v_isSharedCheck_7787_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7777_);
                        crate::leanh::lean_dec(v___x_7776_);
                        v___x_7779_ = crate::leanh::lean_box(0);
                        v_isShared_7780_ = v_isSharedCheck_7787_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7772_);
                    v_a_7788_ = crate::leanh::lean_ctor_get(v___x_7776_, 0);
                    v_isSharedCheck_7795_ = (!crate::leanh::lean_is_exclusive(v___x_7776_)) as u8;
                    if v_isSharedCheck_7795_ == 0 {
                        v___x_7790_ = v___x_7776_;
                        v_isShared_7791_ = v_isSharedCheck_7795_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7788_);
                        crate::leanh::lean_dec(v___x_7776_);
                        v___x_7790_ = crate::leanh::lean_box(0);
                        v_isShared_7791_ = v_isSharedCheck_7795_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_7773_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7772_, 0, v_a_7777_);
                    v___x_7782_ = v___x_7772_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7786_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7786_, 0, v_a_7777_);
                    v___x_7782_ = v_reuseFailAlloc_7786_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_7780_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7779_, 0, v___x_7782_);
                    v___x_7784_ = v___x_7779_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7785_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7785_, 0, v___x_7782_);
                    v___x_7784_ = v_reuseFailAlloc_7785_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7784_;
            }
            11 => {
                if v_isShared_7791_ == 0 {
                    v___x_7793_ = v___x_7790_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7794_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7794_, 0, v_a_7788_);
                    v___x_7793_ = v_reuseFailAlloc_7794_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(
    mut v___x_7797_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_7798_: *mut crate::leanh::LeanObject,
    mut v_sz_7799_: usize,
    mut v_i_7800_: usize,
    mut v_bs_7801_: *mut crate::leanh::LeanObject,
    mut v___y_7802_: *mut crate::leanh::LeanObject,
    mut v___y_7803_: *mut crate::leanh::LeanObject,
    mut v___y_7804_: *mut crate::leanh::LeanObject,
    mut v___y_7805_: *mut crate::leanh::LeanObject,
    mut v___y_7806_: *mut crate::leanh::LeanObject,
    mut v___y_7807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7809_: u8 = 0;
    let mut v___x_7810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7816_: usize = 0;
    let mut v___x_7817_: usize = 0;
    let mut v___x_7818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7823_: u8 = 0;
    let mut v___x_7825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7809_ = lean_usize_dec_lt(v_i_7800_, v_sz_7799_);
                if v___x_7809_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_x3f_7798_);
                    v___x_7810_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7810_, 0, v_bs_7801_);
                    return v___x_7810_;
                } else {
                    v_v_7811_ = lean_array_uget_borrowed(v_bs_7801_, v_i_7800_);
                    crate::leanh::lean_inc(v_v_7811_);
                    crate::leanh::lean_inc_ref(v_ctx_x3f_7798_);
                    v___x_7812_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_7797_, v_ctx_x3f_7798_, v_v_7811_, v___y_7802_, v___y_7803_, v___y_7804_, v___y_7805_, v___y_7806_, v___y_7807_);
                    if crate::leanh::lean_obj_tag(v___x_7812_) == 0 {
                        v_a_7813_ = crate::leanh::lean_ctor_get(v___x_7812_, 0);
                        crate::leanh::lean_inc(v_a_7813_);
                        crate::leanh::lean_dec_ref_known(v___x_7812_, 1);
                        v___x_7814_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_7815_ = lean_array_uset(v_bs_7801_, v_i_7800_, v___x_7814_);
                        v___x_7816_ = 1usize;
                        v___x_7817_ = lean_usize_add(v_i_7800_, v___x_7816_);
                        v___x_7818_ = lean_array_uset(v_bs_x27_7815_, v_i_7800_, v_a_7813_);
                        v_i_7800_ = v___x_7817_;
                        v_bs_7801_ = v___x_7818_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_7801_);
                        crate::leanh::lean_dec_ref(v_ctx_x3f_7798_);
                        v_a_7820_ = crate::leanh::lean_ctor_get(v___x_7812_, 0);
                        v_isSharedCheck_7827_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7812_)) as u8;
                        if v_isSharedCheck_7827_ == 0 {
                            v___x_7822_ = v___x_7812_;
                            v_isShared_7823_ = v_isSharedCheck_7827_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7820_);
                            crate::leanh::lean_dec(v___x_7812_);
                            v___x_7822_ = crate::leanh::lean_box(0);
                            v_isShared_7823_ = v_isSharedCheck_7827_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7823_ == 0 {
                    v___x_7825_ = v___x_7822_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7826_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7826_, 0, v_a_7820_);
                    v___x_7825_ = v_reuseFailAlloc_7826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(
    mut v___x_7828_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_7829_: *mut crate::leanh::LeanObject,
    mut v_sz_7830_: *mut crate::leanh::LeanObject,
    mut v_i_7831_: *mut crate::leanh::LeanObject,
    mut v_bs_7832_: *mut crate::leanh::LeanObject,
    mut v___y_7833_: *mut crate::leanh::LeanObject,
    mut v___y_7834_: *mut crate::leanh::LeanObject,
    mut v___y_7835_: *mut crate::leanh::LeanObject,
    mut v___y_7836_: *mut crate::leanh::LeanObject,
    mut v___y_7837_: *mut crate::leanh::LeanObject,
    mut v___y_7838_: *mut crate::leanh::LeanObject,
    mut v___y_7839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7840_: usize = 0;
    let mut v_i_boxed_7841_: usize = 0;
    let mut v_res_7842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7840_ = crate::leanh::lean_unbox_usize(v_sz_7830_);
    crate::leanh::lean_dec(v_sz_7830_);
    v_i_boxed_7841_ = crate::leanh::lean_unbox_usize(v_i_7831_);
    crate::leanh::lean_dec(v_i_7831_);
    v_res_7842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_7828_, v_ctx_x3f_7829_, v_sz_boxed_7840_, v_i_boxed_7841_, v_bs_7832_, v___y_7833_, v___y_7834_, v___y_7835_, v___y_7836_, v___y_7837_, v___y_7838_);
    crate::leanh::lean_dec(v___y_7838_);
    crate::leanh::lean_dec_ref(v___y_7837_);
    crate::leanh::lean_dec(v___y_7836_);
    crate::leanh::lean_dec_ref(v___y_7835_);
    crate::leanh::lean_dec(v___y_7834_);
    crate::leanh::lean_dec_ref(v___y_7833_);
    crate::leanh::lean_dec_ref(v___x_7828_);
    return v_res_7842_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5___boxed(
    mut v___x_7843_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_7844_: *mut crate::leanh::LeanObject,
    mut v_x_7845_: *mut crate::leanh::LeanObject,
    mut v___y_7846_: *mut crate::leanh::LeanObject,
    mut v___y_7847_: *mut crate::leanh::LeanObject,
    mut v___y_7848_: *mut crate::leanh::LeanObject,
    mut v___y_7849_: *mut crate::leanh::LeanObject,
    mut v___y_7850_: *mut crate::leanh::LeanObject,
    mut v___y_7851_: *mut crate::leanh::LeanObject,
    mut v___y_7852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7853_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_7843_, v_ctx_x3f_7844_, v_x_7845_, v___y_7846_, v___y_7847_, v___y_7848_, v___y_7849_, v___y_7850_, v___y_7851_);
    crate::leanh::lean_dec(v___y_7851_);
    crate::leanh::lean_dec_ref(v___y_7850_);
    crate::leanh::lean_dec(v___y_7849_);
    crate::leanh::lean_dec_ref(v___y_7848_);
    crate::leanh::lean_dec(v___y_7847_);
    crate::leanh::lean_dec_ref(v___y_7846_);
    crate::leanh::lean_dec_ref(v___x_7843_);
    return v_res_7853_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(
    mut v___x_7854_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_7855_: *mut crate::leanh::LeanObject,
    mut v_t_7856_: *mut crate::leanh::LeanObject,
    mut v___y_7857_: *mut crate::leanh::LeanObject,
    mut v___y_7858_: *mut crate::leanh::LeanObject,
    mut v___y_7859_: *mut crate::leanh::LeanObject,
    mut v___y_7860_: *mut crate::leanh::LeanObject,
    mut v___y_7861_: *mut crate::leanh::LeanObject,
    mut v___y_7862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_7864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_7867_: usize = 0;
    let mut v_tailOff_7868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7871_: u8 = 0;
    let mut v___x_7872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7874_: usize = 0;
    let mut v___x_7875_: usize = 0;
    let mut v___x_7876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7880_: u8 = 0;
    let mut v___x_7882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7887_: u8 = 0;
    let mut v_a_7888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7891_: u8 = 0;
    let mut v___x_7893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7895_: u8 = 0;
    let mut v_a_7896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7899_: u8 = 0;
    let mut v___x_7901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7903_: u8 = 0;
    let mut v_isSharedCheck_7904_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_7864_ = crate::leanh::lean_ctor_get(v_t_7856_, 0);
                v_tail_7865_ = crate::leanh::lean_ctor_get(v_t_7856_, 1);
                v_size_7866_ = crate::leanh::lean_ctor_get(v_t_7856_, 2);
                v_shift_7867_ = crate::leanh::lean_ctor_get_usize(v_t_7856_, 4);
                v_tailOff_7868_ = crate::leanh::lean_ctor_get(v_t_7856_, 3);
                v_isSharedCheck_7904_ = (!crate::leanh::lean_is_exclusive(v_t_7856_)) as u8;
                if v_isSharedCheck_7904_ == 0 {
                    v___x_7870_ = v_t_7856_;
                    v_isShared_7871_ = v_isSharedCheck_7904_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tailOff_7868_);
                    crate::leanh::lean_inc(v_size_7866_);
                    crate::leanh::lean_inc(v_tail_7865_);
                    crate::leanh::lean_inc(v_root_7864_);
                    crate::leanh::lean_dec(v_t_7856_);
                    v___x_7870_ = crate::leanh::lean_box(0);
                    v_isShared_7871_ = v_isSharedCheck_7904_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_ctx_x3f_7855_);
                v___x_7872_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_7854_, v_ctx_x3f_7855_, v_root_7864_, v___y_7857_, v___y_7858_, v___y_7859_, v___y_7860_, v___y_7861_, v___y_7862_);
                if crate::leanh::lean_obj_tag(v___x_7872_) == 0 {
                    v_a_7873_ = crate::leanh::lean_ctor_get(v___x_7872_, 0);
                    crate::leanh::lean_inc(v_a_7873_);
                    crate::leanh::lean_dec_ref_known(v___x_7872_, 1);
                    v_sz_7874_ = lean_array_size(v_tail_7865_);
                    v___x_7875_ = 0usize;
                    v___x_7876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_7854_, v_ctx_x3f_7855_, v_sz_7874_, v___x_7875_, v_tail_7865_, v___y_7857_, v___y_7858_, v___y_7859_, v___y_7860_, v___y_7861_, v___y_7862_);
                    if crate::leanh::lean_obj_tag(v___x_7876_) == 0 {
                        v_a_7877_ = crate::leanh::lean_ctor_get(v___x_7876_, 0);
                        v_isSharedCheck_7887_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7876_)) as u8;
                        if v_isSharedCheck_7887_ == 0 {
                            v___x_7879_ = v___x_7876_;
                            v_isShared_7880_ = v_isSharedCheck_7887_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7877_);
                            crate::leanh::lean_dec(v___x_7876_);
                            v___x_7879_ = crate::leanh::lean_box(0);
                            v_isShared_7880_ = v_isSharedCheck_7887_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7873_);
                        crate::leanh::lean_del_object(v___x_7870_);
                        crate::leanh::lean_dec(v_tailOff_7868_);
                        crate::leanh::lean_dec(v_size_7866_);
                        v_a_7888_ = crate::leanh::lean_ctor_get(v___x_7876_, 0);
                        v_isSharedCheck_7895_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7876_)) as u8;
                        if v_isSharedCheck_7895_ == 0 {
                            v___x_7890_ = v___x_7876_;
                            v_isShared_7891_ = v_isSharedCheck_7895_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7888_);
                            crate::leanh::lean_dec(v___x_7876_);
                            v___x_7890_ = crate::leanh::lean_box(0);
                            v_isShared_7891_ = v_isSharedCheck_7895_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7870_);
                    crate::leanh::lean_dec(v_tailOff_7868_);
                    crate::leanh::lean_dec(v_size_7866_);
                    crate::leanh::lean_dec_ref(v_tail_7865_);
                    crate::leanh::lean_dec_ref(v_ctx_x3f_7855_);
                    v_a_7896_ = crate::leanh::lean_ctor_get(v___x_7872_, 0);
                    v_isSharedCheck_7903_ = (!crate::leanh::lean_is_exclusive(v___x_7872_)) as u8;
                    if v_isSharedCheck_7903_ == 0 {
                        v___x_7898_ = v___x_7872_;
                        v_isShared_7899_ = v_isSharedCheck_7903_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7896_);
                        crate::leanh::lean_dec(v___x_7872_);
                        v___x_7898_ = crate::leanh::lean_box(0);
                        v_isShared_7899_ = v_isSharedCheck_7903_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7871_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7870_, 1, v_a_7877_);
                    crate::leanh::lean_ctor_set(v___x_7870_, 0, v_a_7873_);
                    v___x_7882_ = v___x_7870_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7886_ = crate::leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7886_, 0, v_a_7873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7886_, 1, v_a_7877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7886_, 2, v_size_7866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7886_, 3, v_tailOff_7868_);
                    crate::leanh::lean_ctor_set_usize(v_reuseFailAlloc_7886_, 4, v_shift_7867_);
                    v___x_7882_ = v_reuseFailAlloc_7886_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7880_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7879_, 0, v___x_7882_);
                    v___x_7884_ = v___x_7879_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7885_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7885_, 0, v___x_7882_);
                    v___x_7884_ = v_reuseFailAlloc_7885_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7884_;
            }
            5 => {
                if v_isShared_7891_ == 0 {
                    v___x_7893_ = v___x_7890_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7894_, 0, v_a_7888_);
                    v___x_7893_ = v_reuseFailAlloc_7894_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7893_;
            }
            7 => {
                if v_isShared_7899_ == 0 {
                    v___x_7901_ = v___x_7898_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7902_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7902_, 0, v_a_7896_);
                    v___x_7901_ = v_reuseFailAlloc_7902_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4___boxed(
    mut v___x_7905_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_7906_: *mut crate::leanh::LeanObject,
    mut v_t_7907_: *mut crate::leanh::LeanObject,
    mut v___y_7908_: *mut crate::leanh::LeanObject,
    mut v___y_7909_: *mut crate::leanh::LeanObject,
    mut v___y_7910_: *mut crate::leanh::LeanObject,
    mut v___y_7911_: *mut crate::leanh::LeanObject,
    mut v___y_7912_: *mut crate::leanh::LeanObject,
    mut v___y_7913_: *mut crate::leanh::LeanObject,
    mut v___y_7914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7915_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v___x_7905_, v_ctx_x3f_7906_, v_t_7907_, v___y_7908_, v___y_7909_, v___y_7910_, v___y_7911_, v___y_7912_, v___y_7913_);
    crate::leanh::lean_dec(v___y_7913_);
    crate::leanh::lean_dec_ref(v___y_7912_);
    crate::leanh::lean_dec(v___y_7911_);
    crate::leanh::lean_dec_ref(v___y_7910_);
    crate::leanh::lean_dec(v___y_7909_);
    crate::leanh::lean_dec_ref(v___y_7908_);
    crate::leanh::lean_dec_ref(v___x_7905_);
    return v_res_7915_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(
    mut v___y_7916_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_7917_: *mut crate::leanh::LeanObject,
    mut v___y_7918_: *mut crate::leanh::LeanObject,
    mut v___y_7919_: *mut crate::leanh::LeanObject,
    mut v___y_7920_: *mut crate::leanh::LeanObject,
    mut v___y_7921_: *mut crate::leanh::LeanObject,
    mut v___y_7922_: *mut crate::leanh::LeanObject,
    mut v_a_7923_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_7924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_7928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7933_: u8 = 0;
    let mut v___x_7934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7946_: u8 = 0;
    let mut v_enabled_7947_: u8 = 0;
    let mut v_assignment_7948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_7949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7952_: u8 = 0;
    let mut v___x_7953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7965_: u8 = 0;
    let mut v_unused_7966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7967_: u8 = 0;
    let mut v_isSharedCheck_7968_: u8 = 0;
    let mut v_a_7969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7972_: u8 = 0;
    let mut v___x_7974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7926_ = lean_st_ref_get(v___y_7916_);
                v_infoState_7927_ = crate::leanh::lean_ctor_get(v___x_7926_, 7);
                crate::leanh::lean_inc_ref(v_infoState_7927_);
                crate::leanh::lean_dec(v___x_7926_);
                v_trees_7928_ = crate::leanh::lean_ctor_get(v_infoState_7927_, 2);
                crate::leanh::lean_inc_ref(v_trees_7928_);
                v___x_7929_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v_infoState_7927_, v_ctx_x3f_7917_, v_trees_7928_, v___y_7918_, v___y_7919_, v___y_7920_, v___y_7921_, v___y_7922_, v___y_7916_);
                crate::leanh::lean_dec_ref(v_infoState_7927_);
                if crate::leanh::lean_obj_tag(v___x_7929_) == 0 {
                    v_a_7930_ = crate::leanh::lean_ctor_get(v___x_7929_, 0);
                    v_isSharedCheck_7968_ = (!crate::leanh::lean_is_exclusive(v___x_7929_)) as u8;
                    if v_isSharedCheck_7968_ == 0 {
                        v___x_7932_ = v___x_7929_;
                        v_isShared_7933_ = v_isSharedCheck_7968_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7930_);
                        crate::leanh::lean_dec(v___x_7929_);
                        v___x_7932_ = crate::leanh::lean_box(0);
                        v_isShared_7933_ = v_isSharedCheck_7968_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_7923_);
                    v_a_7969_ = crate::leanh::lean_ctor_get(v___x_7929_, 0);
                    v_isSharedCheck_7976_ = (!crate::leanh::lean_is_exclusive(v___x_7929_)) as u8;
                    if v_isSharedCheck_7976_ == 0 {
                        v___x_7971_ = v___x_7929_;
                        v_isShared_7972_ = v_isSharedCheck_7976_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7969_);
                        crate::leanh::lean_dec(v___x_7929_);
                        v___x_7971_ = crate::leanh::lean_box(0);
                        v_isShared_7972_ = v_isSharedCheck_7976_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7934_ = lean_st_ref_take(v___y_7916_);
                v_infoState_7935_ = crate::leanh::lean_ctor_get(v___x_7934_, 7);
                v_env_7936_ = crate::leanh::lean_ctor_get(v___x_7934_, 0);
                v_nextMacroScope_7937_ = crate::leanh::lean_ctor_get(v___x_7934_, 1);
                v_ngen_7938_ = crate::leanh::lean_ctor_get(v___x_7934_, 2);
                v_auxDeclNGen_7939_ = crate::leanh::lean_ctor_get(v___x_7934_, 3);
                v_traceState_7940_ = crate::leanh::lean_ctor_get(v___x_7934_, 4);
                v_cache_7941_ = crate::leanh::lean_ctor_get(v___x_7934_, 5);
                v_messages_7942_ = crate::leanh::lean_ctor_get(v___x_7934_, 6);
                v_snapshotTasks_7943_ = crate::leanh::lean_ctor_get(v___x_7934_, 8);
                v_isSharedCheck_7967_ = (!crate::leanh::lean_is_exclusive(v___x_7934_)) as u8;
                if v_isSharedCheck_7967_ == 0 {
                    v___x_7945_ = v___x_7934_;
                    v_isShared_7946_ = v_isSharedCheck_7967_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_7943_);
                    crate::leanh::lean_inc(v_infoState_7935_);
                    crate::leanh::lean_inc(v_messages_7942_);
                    crate::leanh::lean_inc(v_cache_7941_);
                    crate::leanh::lean_inc(v_traceState_7940_);
                    crate::leanh::lean_inc(v_auxDeclNGen_7939_);
                    crate::leanh::lean_inc(v_ngen_7938_);
                    crate::leanh::lean_inc(v_nextMacroScope_7937_);
                    crate::leanh::lean_inc(v_env_7936_);
                    crate::leanh::lean_dec(v___x_7934_);
                    v___x_7945_ = crate::leanh::lean_box(0);
                    v_isShared_7946_ = v_isSharedCheck_7967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_7947_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_7935_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_7948_ = crate::leanh::lean_ctor_get(v_infoState_7935_, 0);
                v_lazyAssignment_7949_ = crate::leanh::lean_ctor_get(v_infoState_7935_, 1);
                v_isSharedCheck_7965_ = (!crate::leanh::lean_is_exclusive(v_infoState_7935_)) as u8;
                if v_isSharedCheck_7965_ == 0 {
                    v_unused_7966_ = crate::leanh::lean_ctor_get(v_infoState_7935_, 2);
                    crate::leanh::lean_dec(v_unused_7966_);
                    v___x_7951_ = v_infoState_7935_;
                    v_isShared_7952_ = v_isSharedCheck_7965_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_7949_);
                    crate::leanh::lean_inc(v_assignment_7948_);
                    crate::leanh::lean_dec(v_infoState_7935_);
                    v___x_7951_ = crate::leanh::lean_box(0);
                    v_isShared_7952_ = v_isSharedCheck_7965_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7953_ = l_Lean_PersistentArray_append___redArg(v_a_7923_, v_a_7930_);
                crate::leanh::lean_dec(v_a_7930_);
                if v_isShared_7952_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7951_, 2, v___x_7953_);
                    v___x_7955_ = v___x_7951_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7964_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7964_, 0, v_assignment_7948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7964_, 1, v_lazyAssignment_7949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7964_, 2, v___x_7953_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7964_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_7947_,
                    );
                    v___x_7955_ = v_reuseFailAlloc_7964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7946_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7945_, 7, v___x_7955_);
                    v___x_7957_ = v___x_7945_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7963_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 0, v_env_7936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 1, v_nextMacroScope_7937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 2, v_ngen_7938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 3, v_auxDeclNGen_7939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 4, v_traceState_7940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 5, v_cache_7941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 6, v_messages_7942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 7, v___x_7955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 8, v_snapshotTasks_7943_);
                    v___x_7957_ = v_reuseFailAlloc_7963_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7958_ = lean_st_ref_set(v___y_7916_, v___x_7957_);
                v___x_7959_ = crate::leanh::lean_box(0);
                if v_isShared_7933_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7932_, 0, v___x_7959_);
                    v___x_7961_ = v___x_7932_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7962_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7962_, 0, v___x_7959_);
                    v___x_7961_ = v_reuseFailAlloc_7962_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7961_;
            }
            7 => {
                if v_isShared_7972_ == 0 {
                    v___x_7974_ = v___x_7971_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7975_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7975_, 0, v_a_7969_);
                    v___x_7974_ = v_reuseFailAlloc_7975_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0___boxed(
    mut v___y_7977_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_7978_: *mut crate::leanh::LeanObject,
    mut v___y_7979_: *mut crate::leanh::LeanObject,
    mut v___y_7980_: *mut crate::leanh::LeanObject,
    mut v___y_7981_: *mut crate::leanh::LeanObject,
    mut v___y_7982_: *mut crate::leanh::LeanObject,
    mut v___y_7983_: *mut crate::leanh::LeanObject,
    mut v_a_7984_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_7985_: *mut crate::leanh::LeanObject,
    mut v___y_7986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7987_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_7977_, v_ctx_x3f_7978_, v___y_7979_, v___y_7980_, v___y_7981_, v___y_7982_, v___y_7983_, v_a_7984_, v_a_x3f_7985_);
    crate::leanh::lean_dec(v_a_x3f_7985_);
    crate::leanh::lean_dec_ref(v___y_7983_);
    crate::leanh::lean_dec(v___y_7982_);
    crate::leanh::lean_dec_ref(v___y_7981_);
    crate::leanh::lean_dec(v___y_7980_);
    crate::leanh::lean_dec_ref(v___y_7979_);
    crate::leanh::lean_dec(v___y_7977_);
    return v_res_7987_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(
    mut v___y_7988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_7992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_8001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_8002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8005_: u8 = 0;
    let mut v_enabled_8006_: u8 = 0;
    let mut v_assignment_8007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_8008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8011_: u8 = 0;
    let mut v___x_8012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8023_: u8 = 0;
    let mut v_unused_8024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7990_ = lean_st_ref_get(v___y_7988_);
                v_infoState_7991_ = crate::leanh::lean_ctor_get(v___x_7990_, 7);
                crate::leanh::lean_inc_ref(v_infoState_7991_);
                crate::leanh::lean_dec(v___x_7990_);
                v_trees_7992_ = crate::leanh::lean_ctor_get(v_infoState_7991_, 2);
                crate::leanh::lean_inc_ref(v_trees_7992_);
                crate::leanh::lean_dec_ref(v_infoState_7991_);
                v___x_7993_ = lean_st_ref_take(v___y_7988_);
                v_infoState_7994_ = crate::leanh::lean_ctor_get(v___x_7993_, 7);
                v_env_7995_ = crate::leanh::lean_ctor_get(v___x_7993_, 0);
                v_nextMacroScope_7996_ = crate::leanh::lean_ctor_get(v___x_7993_, 1);
                v_ngen_7997_ = crate::leanh::lean_ctor_get(v___x_7993_, 2);
                v_auxDeclNGen_7998_ = crate::leanh::lean_ctor_get(v___x_7993_, 3);
                v_traceState_7999_ = crate::leanh::lean_ctor_get(v___x_7993_, 4);
                v_cache_8000_ = crate::leanh::lean_ctor_get(v___x_7993_, 5);
                v_messages_8001_ = crate::leanh::lean_ctor_get(v___x_7993_, 6);
                v_snapshotTasks_8002_ = crate::leanh::lean_ctor_get(v___x_7993_, 8);
                v_isSharedCheck_8025_ = (!crate::leanh::lean_is_exclusive(v___x_7993_)) as u8;
                if v_isSharedCheck_8025_ == 0 {
                    v___x_8004_ = v___x_7993_;
                    v_isShared_8005_ = v_isSharedCheck_8025_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_8002_);
                    crate::leanh::lean_inc(v_infoState_7994_);
                    crate::leanh::lean_inc(v_messages_8001_);
                    crate::leanh::lean_inc(v_cache_8000_);
                    crate::leanh::lean_inc(v_traceState_7999_);
                    crate::leanh::lean_inc(v_auxDeclNGen_7998_);
                    crate::leanh::lean_inc(v_ngen_7997_);
                    crate::leanh::lean_inc(v_nextMacroScope_7996_);
                    crate::leanh::lean_inc(v_env_7995_);
                    crate::leanh::lean_dec(v___x_7993_);
                    v___x_8004_ = crate::leanh::lean_box(0);
                    v_isShared_8005_ = v_isSharedCheck_8025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_8006_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_7994_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_8007_ = crate::leanh::lean_ctor_get(v_infoState_7994_, 0);
                v_lazyAssignment_8008_ = crate::leanh::lean_ctor_get(v_infoState_7994_, 1);
                v_isSharedCheck_8023_ = (!crate::leanh::lean_is_exclusive(v_infoState_7994_)) as u8;
                if v_isSharedCheck_8023_ == 0 {
                    v_unused_8024_ = crate::leanh::lean_ctor_get(v_infoState_7994_, 2);
                    crate::leanh::lean_dec(v_unused_8024_);
                    v___x_8010_ = v_infoState_7994_;
                    v_isShared_8011_ = v_isSharedCheck_8023_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_8008_);
                    crate::leanh::lean_inc(v_assignment_8007_);
                    crate::leanh::lean_dec(v_infoState_7994_);
                    v___x_8010_ = crate::leanh::lean_box(0);
                    v_isShared_8011_ = v_isSharedCheck_8023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8012_ = crate::leanh::lean_unsigned_to_nat(32);
                v___x_8013_ = lean_mk_empty_array_with_capacity(v___x_8012_);
                crate::leanh::lean_dec_ref(v___x_8013_);
                v___x_8014_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
                if v_isShared_8011_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8010_, 2, v___x_8014_);
                    v___x_8016_ = v___x_8010_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8022_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8022_, 0, v_assignment_8007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8022_, 1, v_lazyAssignment_8008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8022_, 2, v___x_8014_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8022_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_8006_,
                    );
                    v___x_8016_ = v_reuseFailAlloc_8022_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8005_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8004_, 7, v___x_8016_);
                    v___x_8018_ = v___x_8004_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8021_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 0, v_env_7995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 1, v_nextMacroScope_7996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 2, v_ngen_7997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 3, v_auxDeclNGen_7998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 4, v_traceState_7999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 5, v_cache_8000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 6, v_messages_8001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 7, v___x_8016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 8, v_snapshotTasks_8002_);
                    v___x_8018_ = v_reuseFailAlloc_8021_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8019_ = lean_st_ref_set(v___y_7988_, v___x_8018_);
                v___x_8020_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8020_, 0, v_trees_7992_);
                return v___x_8020_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg___boxed(
    mut v___y_8026_: *mut crate::leanh::LeanObject,
    mut v___y_8027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8028_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_8026_);
    crate::leanh::lean_dec(v___y_8026_);
    return v_res_8028_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(
    mut v_x_8029_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_8030_: *mut crate::leanh::LeanObject,
    mut v___y_8031_: *mut crate::leanh::LeanObject,
    mut v___y_8032_: *mut crate::leanh::LeanObject,
    mut v___y_8033_: *mut crate::leanh::LeanObject,
    mut v___y_8034_: *mut crate::leanh::LeanObject,
    mut v___y_8035_: *mut crate::leanh::LeanObject,
    mut v___y_8036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_8039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_8040_: u8 = 0;
    let mut v___x_8041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8048_: u8 = 0;
    let mut v___x_8050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8054_: u8 = 0;
    let mut v___x_8056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8058_: u8 = 0;
    let mut v_unused_8059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8063_: u8 = 0;
    let mut v___x_8065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8067_: u8 = 0;
    let mut v_reuseFailAlloc_8068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8069_: u8 = 0;
    let mut v_a_8070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8075_: u8 = 0;
    let mut v___x_8077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8079_: u8 = 0;
    let mut v_unused_8080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8084_: u8 = 0;
    let mut v___x_8086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8038_ = lean_st_ref_get(v___y_8036_);
                v_infoState_8039_ = crate::leanh::lean_ctor_get(v___x_8038_, 7);
                crate::leanh::lean_inc_ref(v_infoState_8039_);
                crate::leanh::lean_dec(v___x_8038_);
                v_enabled_8040_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_8039_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_8039_);
                if v_enabled_8040_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_x3f_8030_);
                    crate::leanh::lean_inc(v___y_8036_);
                    crate::leanh::lean_inc_ref(v___y_8035_);
                    crate::leanh::lean_inc(v___y_8034_);
                    crate::leanh::lean_inc_ref(v___y_8033_);
                    crate::leanh::lean_inc(v___y_8032_);
                    crate::leanh::lean_inc_ref(v___y_8031_);
                    v___x_8041_ = crate::leanh::lean_apply_7(
                        v_x_8029_,
                        v___y_8031_,
                        v___y_8032_,
                        v___y_8033_,
                        v___y_8034_,
                        v___y_8035_,
                        v___y_8036_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_8041_;
                } else {
                    v___x_8042_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_8036_);
                    v_a_8043_ = crate::leanh::lean_ctor_get(v___x_8042_, 0);
                    crate::leanh::lean_inc(v_a_8043_);
                    crate::leanh::lean_dec_ref(v___x_8042_);
                    crate::leanh::lean_inc(v___y_8036_);
                    crate::leanh::lean_inc_ref(v___y_8035_);
                    crate::leanh::lean_inc(v___y_8034_);
                    crate::leanh::lean_inc_ref(v___y_8033_);
                    crate::leanh::lean_inc(v___y_8032_);
                    crate::leanh::lean_inc_ref(v___y_8031_);
                    v_r_8044_ = crate::leanh::lean_apply_7(
                        v_x_8029_,
                        v___y_8031_,
                        v___y_8032_,
                        v___y_8033_,
                        v___y_8034_,
                        v___y_8035_,
                        v___y_8036_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_8044_) == 0 {
                        v_a_8045_ = crate::leanh::lean_ctor_get(v_r_8044_, 0);
                        v_isSharedCheck_8069_ = (!crate::leanh::lean_is_exclusive(v_r_8044_)) as u8;
                        if v_isSharedCheck_8069_ == 0 {
                            v___x_8047_ = v_r_8044_;
                            v_isShared_8048_ = v_isSharedCheck_8069_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8045_);
                            crate::leanh::lean_dec(v_r_8044_);
                            v___x_8047_ = crate::leanh::lean_box(0);
                            v_isShared_8048_ = v_isSharedCheck_8069_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_8070_ = crate::leanh::lean_ctor_get(v_r_8044_, 0);
                        crate::leanh::lean_inc(v_a_8070_);
                        crate::leanh::lean_dec_ref_known(v_r_8044_, 1);
                        v___x_8071_ = crate::leanh::lean_box(0);
                        v___x_8072_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_8036_, v_ctx_x3f_8030_, v___y_8031_, v___y_8032_, v___y_8033_, v___y_8034_, v___y_8035_, v_a_8043_, v___x_8071_);
                        if crate::leanh::lean_obj_tag(v___x_8072_) == 0 {
                            v_isSharedCheck_8079_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8072_)) as u8;
                            if v_isSharedCheck_8079_ == 0 {
                                v_unused_8080_ = crate::leanh::lean_ctor_get(v___x_8072_, 0);
                                crate::leanh::lean_dec(v_unused_8080_);
                                v___x_8074_ = v___x_8072_;
                                v_isShared_8075_ = v_isSharedCheck_8079_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_8072_);
                                v___x_8074_ = crate::leanh::lean_box(0);
                                v_isShared_8075_ = v_isSharedCheck_8079_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_8070_);
                            v_a_8081_ = crate::leanh::lean_ctor_get(v___x_8072_, 0);
                            v_isSharedCheck_8088_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8072_)) as u8;
                            if v_isSharedCheck_8088_ == 0 {
                                v___x_8083_ = v___x_8072_;
                                v_isShared_8084_ = v_isSharedCheck_8088_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8081_);
                                crate::leanh::lean_dec(v___x_8072_);
                                v___x_8083_ = crate::leanh::lean_box(0);
                                v_isShared_8084_ = v_isSharedCheck_8088_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_8045_);
                if v_isShared_8048_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_8047_, 1);
                    v___x_8050_ = v___x_8047_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8068_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8068_, 0, v_a_8045_);
                    v___x_8050_ = v_reuseFailAlloc_8068_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8051_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_8036_, v_ctx_x3f_8030_, v___y_8031_, v___y_8032_, v___y_8033_, v___y_8034_, v___y_8035_, v_a_8043_, v___x_8050_);
                crate::leanh::lean_dec_ref(v___x_8050_);
                if crate::leanh::lean_obj_tag(v___x_8051_) == 0 {
                    v_isSharedCheck_8058_ = (!crate::leanh::lean_is_exclusive(v___x_8051_)) as u8;
                    if v_isSharedCheck_8058_ == 0 {
                        v_unused_8059_ = crate::leanh::lean_ctor_get(v___x_8051_, 0);
                        crate::leanh::lean_dec(v_unused_8059_);
                        v___x_8053_ = v___x_8051_;
                        v_isShared_8054_ = v_isSharedCheck_8058_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_8051_);
                        v___x_8053_ = crate::leanh::lean_box(0);
                        v_isShared_8054_ = v_isSharedCheck_8058_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_8045_);
                    v_a_8060_ = crate::leanh::lean_ctor_get(v___x_8051_, 0);
                    v_isSharedCheck_8067_ = (!crate::leanh::lean_is_exclusive(v___x_8051_)) as u8;
                    if v_isSharedCheck_8067_ == 0 {
                        v___x_8062_ = v___x_8051_;
                        v_isShared_8063_ = v_isSharedCheck_8067_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8060_);
                        crate::leanh::lean_dec(v___x_8051_);
                        v___x_8062_ = crate::leanh::lean_box(0);
                        v_isShared_8063_ = v_isSharedCheck_8067_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_8054_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8053_, 0, v_a_8045_);
                    v___x_8056_ = v___x_8053_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8057_, 0, v_a_8045_);
                    v___x_8056_ = v_reuseFailAlloc_8057_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8056_;
            }
            5 => {
                if v_isShared_8063_ == 0 {
                    v___x_8065_ = v___x_8062_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8066_, 0, v_a_8060_);
                    v___x_8065_ = v_reuseFailAlloc_8066_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8065_;
            }
            7 => {
                if v_isShared_8075_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_8074_, 1);
                    crate::leanh::lean_ctor_set(v___x_8074_, 0, v_a_8070_);
                    v___x_8077_ = v___x_8074_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8078_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8078_, 0, v_a_8070_);
                    v___x_8077_ = v_reuseFailAlloc_8078_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8077_;
            }
            9 => {
                if v_isShared_8084_ == 0 {
                    v___x_8086_ = v___x_8083_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8087_, 0, v_a_8081_);
                    v___x_8086_ = v_reuseFailAlloc_8087_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___boxed(
    mut v_x_8089_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_8090_: *mut crate::leanh::LeanObject,
    mut v___y_8091_: *mut crate::leanh::LeanObject,
    mut v___y_8092_: *mut crate::leanh::LeanObject,
    mut v___y_8093_: *mut crate::leanh::LeanObject,
    mut v___y_8094_: *mut crate::leanh::LeanObject,
    mut v___y_8095_: *mut crate::leanh::LeanObject,
    mut v___y_8096_: *mut crate::leanh::LeanObject,
    mut v___y_8097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8098_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_8089_, v_ctx_x3f_8090_, v___y_8091_, v___y_8092_, v___y_8093_, v___y_8094_, v___y_8095_, v___y_8096_);
    crate::leanh::lean_dec(v___y_8096_);
    crate::leanh::lean_dec_ref(v___y_8095_);
    crate::leanh::lean_dec(v___y_8094_);
    crate::leanh::lean_dec_ref(v___y_8093_);
    crate::leanh::lean_dec(v___y_8092_);
    crate::leanh::lean_dec_ref(v___y_8091_);
    return v_res_8098_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(
    mut v___y_8099_: *mut crate::leanh::LeanObject,
    mut v___y_8100_: *mut crate::leanh::LeanObject,
    mut v___y_8101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_8104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_8106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_8107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_8108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_8109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_8111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8103_ = lean_st_ref_get(v___y_8101_);
    v_env_8104_ = crate::leanh::lean_ctor_get(v___x_8103_, 0);
    crate::leanh::lean_inc_ref(v_env_8104_);
    crate::leanh::lean_dec(v___x_8103_);
    v___x_8105_ = lean_st_ref_get(v___y_8099_);
    v_mctx_8106_ = crate::leanh::lean_ctor_get(v___x_8105_, 0);
    crate::leanh::lean_inc_ref(v_mctx_8106_);
    crate::leanh::lean_dec(v___x_8105_);
    v_options_8107_ = crate::leanh::lean_ctor_get(v___y_8100_, 2);
    v_currNamespace_8108_ = crate::leanh::lean_ctor_get(v___y_8100_, 6);
    v_openDecls_8109_ = crate::leanh::lean_ctor_get(v___y_8100_, 7);
    v___x_8110_ = lean_st_ref_get(v___y_8101_);
    v_ngen_8111_ = crate::leanh::lean_ctor_get(v___x_8110_, 2);
    crate::leanh::lean_inc_ref(v_ngen_8111_);
    crate::leanh::lean_dec(v___x_8110_);
    v___x_8112_ = crate::leanh::lean_box(0);
    v___x_8113_ = l_Lean_instInhabitedFileMap_default;
    crate::leanh::lean_inc(v_openDecls_8109_);
    crate::leanh::lean_inc(v_currNamespace_8108_);
    crate::leanh::lean_inc_ref(v_options_8107_);
    v___x_8114_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8114_, 0, v_env_8104_);
    crate::leanh::lean_ctor_set(v___x_8114_, 1, v___x_8112_);
    crate::leanh::lean_ctor_set(v___x_8114_, 2, v___x_8113_);
    crate::leanh::lean_ctor_set(v___x_8114_, 3, v_mctx_8106_);
    crate::leanh::lean_ctor_set(v___x_8114_, 4, v_options_8107_);
    crate::leanh::lean_ctor_set(v___x_8114_, 5, v_currNamespace_8108_);
    crate::leanh::lean_ctor_set(v___x_8114_, 6, v_openDecls_8109_);
    crate::leanh::lean_ctor_set(v___x_8114_, 7, v_ngen_8111_);
    v___x_8115_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8115_, 0, v___x_8114_);
    return v___x_8115_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg___boxed(
    mut v___y_8116_: *mut crate::leanh::LeanObject,
    mut v___y_8117_: *mut crate::leanh::LeanObject,
    mut v___y_8118_: *mut crate::leanh::LeanObject,
    mut v___y_8119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8120_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_8116_, v___y_8117_, v___y_8118_);
    crate::leanh::lean_dec(v___y_8118_);
    crate::leanh::lean_dec_ref(v___y_8117_);
    crate::leanh::lean_dec(v___y_8116_);
    return v_res_8120_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(
    mut v___y_8121_: *mut crate::leanh::LeanObject,
    mut v___y_8122_: *mut crate::leanh::LeanObject,
    mut v___y_8123_: *mut crate::leanh::LeanObject,
    mut v___y_8124_: *mut crate::leanh::LeanObject,
    mut v___y_8125_: *mut crate::leanh::LeanObject,
    mut v___y_8126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8132_: u8 = 0;
    let mut v_fileMap_8133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_8134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_8135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_8136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_8137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_8138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_8139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8142_: u8 = 0;
    let mut v___x_8143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8150_: u8 = 0;
    let mut v_unused_8151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8128_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_8124_, v___y_8125_, v___y_8126_);
                v_a_8129_ = crate::leanh::lean_ctor_get(v___x_8128_, 0);
                v_isSharedCheck_8153_ = (!crate::leanh::lean_is_exclusive(v___x_8128_)) as u8;
                if v_isSharedCheck_8153_ == 0 {
                    v___x_8131_ = v___x_8128_;
                    v_isShared_8132_ = v_isSharedCheck_8153_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_8129_);
                    crate::leanh::lean_dec(v___x_8128_);
                    v___x_8131_ = crate::leanh::lean_box(0);
                    v_isShared_8132_ = v_isSharedCheck_8153_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_8133_ = crate::leanh::lean_ctor_get(v___y_8125_, 1);
                v_env_8134_ = crate::leanh::lean_ctor_get(v_a_8129_, 0);
                v_mctx_8135_ = crate::leanh::lean_ctor_get(v_a_8129_, 3);
                v_options_8136_ = crate::leanh::lean_ctor_get(v_a_8129_, 4);
                v_currNamespace_8137_ = crate::leanh::lean_ctor_get(v_a_8129_, 5);
                v_openDecls_8138_ = crate::leanh::lean_ctor_get(v_a_8129_, 6);
                v_ngen_8139_ = crate::leanh::lean_ctor_get(v_a_8129_, 7);
                v_isSharedCheck_8150_ = (!crate::leanh::lean_is_exclusive(v_a_8129_)) as u8;
                if v_isSharedCheck_8150_ == 0 {
                    v_unused_8151_ = crate::leanh::lean_ctor_get(v_a_8129_, 2);
                    crate::leanh::lean_dec(v_unused_8151_);
                    v_unused_8152_ = crate::leanh::lean_ctor_get(v_a_8129_, 1);
                    crate::leanh::lean_dec(v_unused_8152_);
                    v___x_8141_ = v_a_8129_;
                    v_isShared_8142_ = v_isSharedCheck_8150_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ngen_8139_);
                    crate::leanh::lean_inc(v_openDecls_8138_);
                    crate::leanh::lean_inc(v_currNamespace_8137_);
                    crate::leanh::lean_inc(v_options_8136_);
                    crate::leanh::lean_inc(v_mctx_8135_);
                    crate::leanh::lean_inc(v_env_8134_);
                    crate::leanh::lean_dec(v_a_8129_);
                    v___x_8141_ = crate::leanh::lean_box(0);
                    v_isShared_8142_ = v_isSharedCheck_8150_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8143_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_fileMap_8133_);
                if v_isShared_8142_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8141_, 2, v_fileMap_8133_);
                    crate::leanh::lean_ctor_set(v___x_8141_, 1, v___x_8143_);
                    v___x_8145_ = v___x_8141_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8149_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 0, v_env_8134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 1, v___x_8143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 2, v_fileMap_8133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 3, v_mctx_8135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 4, v_options_8136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 5, v_currNamespace_8137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 6, v_openDecls_8138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 7, v_ngen_8139_);
                    v___x_8145_ = v_reuseFailAlloc_8149_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8132_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8131_, 0, v___x_8145_);
                    v___x_8147_ = v___x_8131_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8148_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8148_, 0, v___x_8145_);
                    v___x_8147_ = v_reuseFailAlloc_8148_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0___boxed(
    mut v___y_8154_: *mut crate::leanh::LeanObject,
    mut v___y_8155_: *mut crate::leanh::LeanObject,
    mut v___y_8156_: *mut crate::leanh::LeanObject,
    mut v___y_8157_: *mut crate::leanh::LeanObject,
    mut v___y_8158_: *mut crate::leanh::LeanObject,
    mut v___y_8159_: *mut crate::leanh::LeanObject,
    mut v___y_8160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8161_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_8154_, v___y_8155_, v___y_8156_, v___y_8157_, v___y_8158_, v___y_8159_);
    crate::leanh::lean_dec(v___y_8159_);
    crate::leanh::lean_dec_ref(v___y_8158_);
    crate::leanh::lean_dec(v___y_8157_);
    crate::leanh::lean_dec_ref(v___y_8156_);
    crate::leanh::lean_dec(v___y_8155_);
    crate::leanh::lean_dec_ref(v___y_8154_);
    return v_res_8161_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(
    mut v___y_8162_: *mut crate::leanh::LeanObject,
    mut v___y_8163_: *mut crate::leanh::LeanObject,
    mut v___y_8164_: *mut crate::leanh::LeanObject,
    mut v___y_8165_: *mut crate::leanh::LeanObject,
    mut v___y_8166_: *mut crate::leanh::LeanObject,
    mut v___y_8167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8173_: u8 = 0;
    let mut v___x_8174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8169_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_8162_, v___y_8163_, v___y_8164_, v___y_8165_, v___y_8166_, v___y_8167_);
                v_a_8170_ = crate::leanh::lean_ctor_get(v___x_8169_, 0);
                v_isSharedCheck_8179_ = (!crate::leanh::lean_is_exclusive(v___x_8169_)) as u8;
                if v_isSharedCheck_8179_ == 0 {
                    v___x_8172_ = v___x_8169_;
                    v_isShared_8173_ = v_isSharedCheck_8179_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_8170_);
                    crate::leanh::lean_dec(v___x_8169_);
                    v___x_8172_ = crate::leanh::lean_box(0);
                    v_isShared_8173_ = v_isSharedCheck_8179_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8174_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8174_, 0, v_a_8170_);
                v___x_8175_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8175_, 0, v___x_8174_);
                if v_isShared_8173_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8172_, 0, v___x_8175_);
                    v___x_8177_ = v___x_8172_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8178_, 0, v___x_8175_);
                    v___x_8177_ = v_reuseFailAlloc_8178_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8177_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed(
    mut v___y_8180_: *mut crate::leanh::LeanObject,
    mut v___y_8181_: *mut crate::leanh::LeanObject,
    mut v___y_8182_: *mut crate::leanh::LeanObject,
    mut v___y_8183_: *mut crate::leanh::LeanObject,
    mut v___y_8184_: *mut crate::leanh::LeanObject,
    mut v___y_8185_: *mut crate::leanh::LeanObject,
    mut v___y_8186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8187_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(v___y_8180_, v___y_8181_, v___y_8182_, v___y_8183_, v___y_8184_, v___y_8185_);
    crate::leanh::lean_dec(v___y_8185_);
    crate::leanh::lean_dec_ref(v___y_8184_);
    crate::leanh::lean_dec(v___y_8183_);
    crate::leanh::lean_dec_ref(v___y_8182_);
    crate::leanh::lean_dec(v___y_8181_);
    crate::leanh::lean_dec_ref(v___y_8180_);
    return v_res_8187_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(
    mut v_x_8189_: *mut crate::leanh::LeanObject,
    mut v___y_8190_: *mut crate::leanh::LeanObject,
    mut v___y_8191_: *mut crate::leanh::LeanObject,
    mut v___y_8192_: *mut crate::leanh::LeanObject,
    mut v___y_8193_: *mut crate::leanh::LeanObject,
    mut v___y_8194_: *mut crate::leanh::LeanObject,
    mut v___y_8195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_8197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_8197_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0;
    v___x_8198_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_8189_, v___f_8197_, v___y_8190_, v___y_8191_, v___y_8192_, v___y_8193_, v___y_8194_, v___y_8195_);
    return v___x_8198_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___boxed(
    mut v_x_8199_: *mut crate::leanh::LeanObject,
    mut v___y_8200_: *mut crate::leanh::LeanObject,
    mut v___y_8201_: *mut crate::leanh::LeanObject,
    mut v___y_8202_: *mut crate::leanh::LeanObject,
    mut v___y_8203_: *mut crate::leanh::LeanObject,
    mut v___y_8204_: *mut crate::leanh::LeanObject,
    mut v___y_8205_: *mut crate::leanh::LeanObject,
    mut v___y_8206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8207_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_8199_, v___y_8200_, v___y_8201_, v___y_8202_, v___y_8203_, v___y_8204_, v___y_8205_);
    crate::leanh::lean_dec(v___y_8205_);
    crate::leanh::lean_dec_ref(v___y_8204_);
    crate::leanh::lean_dec(v___y_8203_);
    crate::leanh::lean_dec_ref(v___y_8202_);
    crate::leanh::lean_dec(v___y_8201_);
    crate::leanh::lean_dec_ref(v___y_8200_);
    return v_res_8207_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(
    mut v_00_u03b1_8208_: *mut crate::leanh::LeanObject,
    mut v_x_8209_: *mut crate::leanh::LeanObject,
    mut v___y_8210_: *mut crate::leanh::LeanObject,
    mut v___y_8211_: *mut crate::leanh::LeanObject,
    mut v___y_8212_: *mut crate::leanh::LeanObject,
    mut v___y_8213_: *mut crate::leanh::LeanObject,
    mut v___y_8214_: *mut crate::leanh::LeanObject,
    mut v___y_8215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8217_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_8209_, v___y_8210_, v___y_8211_, v___y_8212_, v___y_8213_, v___y_8214_, v___y_8215_);
    return v___x_8217_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed(
    mut v_00_u03b1_8218_: *mut crate::leanh::LeanObject,
    mut v_x_8219_: *mut crate::leanh::LeanObject,
    mut v___y_8220_: *mut crate::leanh::LeanObject,
    mut v___y_8221_: *mut crate::leanh::LeanObject,
    mut v___y_8222_: *mut crate::leanh::LeanObject,
    mut v___y_8223_: *mut crate::leanh::LeanObject,
    mut v___y_8224_: *mut crate::leanh::LeanObject,
    mut v___y_8225_: *mut crate::leanh::LeanObject,
    mut v___y_8226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8227_ =
        l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(
            v_00_u03b1_8218_,
            v_x_8219_,
            v___y_8220_,
            v___y_8221_,
            v___y_8222_,
            v___y_8223_,
            v___y_8224_,
            v___y_8225_,
        );
    crate::leanh::lean_dec(v___y_8225_);
    crate::leanh::lean_dec_ref(v___y_8224_);
    crate::leanh::lean_dec(v___y_8223_);
    crate::leanh::lean_dec_ref(v___y_8222_);
    crate::leanh::lean_dec(v___y_8221_);
    crate::leanh::lean_dec_ref(v___y_8220_);
    return v_res_8227_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4() -> u64 {
    let mut v___x_8245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8246_: u64 = 0;
    v___x_8245_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3;
    v___x_8246_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_8245_);
    return v___x_8246_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8247_: u64 = 0;
    let mut v___x_8248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8247_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4,
    );
    v___x_8248_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3;
    v___x_8249_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_8249_, 0, v___x_8248_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_8249_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_8247_,
    );
    return v___x_8249_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8250_: u8 = 0;
    let mut v___x_8251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8256_: u8 = 0;
    let mut v___x_8257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8250_ = 1;
    v___x_8251_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_8252_ = crate::leanh::lean_box(0);
    v___x_8253_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1;
    v___x_8254_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2,
    );
    v___x_8255_ = crate::leanh::lean_box(1);
    v___x_8256_ = 0;
    v___x_8257_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5,
    );
    v___x_8258_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
    crate::leanh::lean_ctor_set(v___x_8258_, 0, v___x_8257_);
    crate::leanh::lean_ctor_set(v___x_8258_, 1, v___x_8255_);
    crate::leanh::lean_ctor_set(v___x_8258_, 2, v___x_8254_);
    crate::leanh::lean_ctor_set(v___x_8258_, 3, v___x_8253_);
    crate::leanh::lean_ctor_set(v___x_8258_, 4, v___x_8252_);
    crate::leanh::lean_ctor_set(v___x_8258_, 5, v___x_8251_);
    crate::leanh::lean_ctor_set(v___x_8258_, 6, v___x_8252_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_8258_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v___x_8256_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_8258_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
        v___x_8256_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_8258_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
        v___x_8256_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_8258_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
        v___x_8250_,
    );
    return v___x_8258_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8259_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1,
    );
    v___x_8260_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_8261_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8261_, 0, v___x_8260_);
    crate::leanh::lean_ctor_set(v___x_8261_, 1, v___x_8260_);
    crate::leanh::lean_ctor_set(v___x_8261_, 2, v___x_8260_);
    crate::leanh::lean_ctor_set(v___x_8261_, 3, v___x_8260_);
    crate::leanh::lean_ctor_set(v___x_8261_, 4, v___x_8259_);
    crate::leanh::lean_ctor_set(v___x_8261_, 5, v___x_8259_);
    crate::leanh::lean_ctor_set(v___x_8261_, 6, v___x_8259_);
    crate::leanh::lean_ctor_set(v___x_8261_, 7, v___x_8259_);
    crate::leanh::lean_ctor_set(v___x_8261_, 8, v___x_8259_);
    crate::leanh::lean_ctor_set(v___x_8261_, 9, v___x_8259_);
    return v___x_8261_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8262_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1,
    );
    v___x_8263_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8263_, 0, v___x_8262_);
    crate::leanh::lean_ctor_set(v___x_8263_, 1, v___x_8262_);
    crate::leanh::lean_ctor_set(v___x_8263_, 2, v___x_8262_);
    crate::leanh::lean_ctor_set(v___x_8263_, 3, v___x_8262_);
    crate::leanh::lean_ctor_set(v___x_8263_, 4, v___x_8262_);
    crate::leanh::lean_ctor_set(v___x_8263_, 5, v___x_8262_);
    return v___x_8263_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8264_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1,
    );
    v___x_8265_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8265_, 0, v___x_8264_);
    crate::leanh::lean_ctor_set(v___x_8265_, 1, v___x_8264_);
    crate::leanh::lean_ctor_set(v___x_8265_, 2, v___x_8264_);
    crate::leanh::lean_ctor_set(v___x_8265_, 3, v___x_8264_);
    crate::leanh::lean_ctor_set(v___x_8265_, 4, v___x_8264_);
    return v___x_8265_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8266_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9,
    );
    v___x_8267_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_8268_ = crate::leanh::lean_box(1);
    v___x_8269_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8,
    );
    v___x_8270_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7,
    );
    v___x_8271_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8271_, 0, v___x_8270_);
    crate::leanh::lean_ctor_set(v___x_8271_, 1, v___x_8269_);
    crate::leanh::lean_ctor_set(v___x_8271_, 2, v___x_8268_);
    crate::leanh::lean_ctor_set(v___x_8271_, 3, v___x_8267_);
    crate::leanh::lean_ctor_set(v___x_8271_, 4, v___x_8266_);
    return v___x_8271_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___redArg(
    mut v_mx_8275_: *mut crate::leanh::LeanObject,
    mut v_a_8276_: *mut crate::leanh::LeanObject,
    mut v_a_8277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8289_: u8 = 0;
    let mut v___x_8290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8295_: u8 = 0;
    let mut v_a_8296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8299_: u8 = 0;
    let mut v___x_8301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8279_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2;
                v___x_8280_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6,
                );
                v___x_8281_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10,
                );
                v___x_8282_ = lean_st_mk_ref(v___x_8281_);
                v___x_8283_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed as *mut core::ffi::c_void, 9, 2);
                crate::leanh::lean_closure_set(v___x_8283_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_8283_, 1, v_mx_8275_);
                v___x_8284_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11;
                v___x_8285_ = l_Lean_Elab_Term_TermElabM_run___redArg(
                    v___x_8283_,
                    v___x_8279_,
                    v___x_8284_,
                    v___x_8280_,
                    v___x_8282_,
                    v_a_8276_,
                    v_a_8277_,
                );
                if crate::leanh::lean_obj_tag(v___x_8285_) == 0 {
                    v_a_8286_ = crate::leanh::lean_ctor_get(v___x_8285_, 0);
                    v_isSharedCheck_8295_ = (!crate::leanh::lean_is_exclusive(v___x_8285_)) as u8;
                    if v_isSharedCheck_8295_ == 0 {
                        v___x_8288_ = v___x_8285_;
                        v_isShared_8289_ = v_isSharedCheck_8295_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8286_);
                        crate::leanh::lean_dec(v___x_8285_);
                        v___x_8288_ = crate::leanh::lean_box(0);
                        v_isShared_8289_ = v_isSharedCheck_8295_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_8282_);
                    v_a_8296_ = crate::leanh::lean_ctor_get(v___x_8285_, 0);
                    v_isSharedCheck_8303_ = (!crate::leanh::lean_is_exclusive(v___x_8285_)) as u8;
                    if v_isSharedCheck_8303_ == 0 {
                        v___x_8298_ = v___x_8285_;
                        v_isShared_8299_ = v_isSharedCheck_8303_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8296_);
                        crate::leanh::lean_dec(v___x_8285_);
                        v___x_8298_ = crate::leanh::lean_box(0);
                        v_isShared_8299_ = v_isSharedCheck_8303_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8290_ = lean_st_ref_get(v___x_8282_);
                crate::leanh::lean_dec(v___x_8282_);
                crate::leanh::lean_dec(v___x_8290_);
                v_fst_8291_ = crate::leanh::lean_ctor_get(v_a_8286_, 0);
                crate::leanh::lean_inc(v_fst_8291_);
                crate::leanh::lean_dec(v_a_8286_);
                if v_isShared_8289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8288_, 0, v_fst_8291_);
                    v___x_8293_ = v___x_8288_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8294_, 0, v_fst_8291_);
                    v___x_8293_ = v_reuseFailAlloc_8294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8293_;
            }
            3 => {
                if v_isShared_8299_ == 0 {
                    v___x_8301_ = v___x_8298_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8302_, 0, v_a_8296_);
                    v___x_8301_ = v_reuseFailAlloc_8302_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8301_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___redArg___boxed(
    mut v_mx_8304_: *mut crate::leanh::LeanObject,
    mut v_a_8305_: *mut crate::leanh::LeanObject,
    mut v_a_8306_: *mut crate::leanh::LeanObject,
    mut v_a_8307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8308_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_8304_, v_a_8305_, v_a_8306_);
    crate::leanh::lean_dec(v_a_8306_);
    crate::leanh::lean_dec_ref(v_a_8305_);
    return v_res_8308_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab(
    mut v_00_u03b1_8309_: *mut crate::leanh::LeanObject,
    mut v_mx_8310_: *mut crate::leanh::LeanObject,
    mut v_a_8311_: *mut crate::leanh::LeanObject,
    mut v_a_8312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8314_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_8310_, v_a_8311_, v_a_8312_);
    return v___x_8314_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___boxed(
    mut v_00_u03b1_8315_: *mut crate::leanh::LeanObject,
    mut v_mx_8316_: *mut crate::leanh::LeanObject,
    mut v_a_8317_: *mut crate::leanh::LeanObject,
    mut v_a_8318_: *mut crate::leanh::LeanObject,
    mut v_a_8319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8320_ =
        l_Lean_Elab_ConfigEval_runConfigElab(v_00_u03b1_8315_, v_mx_8316_, v_a_8317_, v_a_8318_);
    crate::leanh::lean_dec(v_a_8318_);
    crate::leanh::lean_dec_ref(v_a_8317_);
    return v_res_8320_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(
    mut v___y_8321_: *mut crate::leanh::LeanObject,
    mut v___y_8322_: *mut crate::leanh::LeanObject,
    mut v___y_8323_: *mut crate::leanh::LeanObject,
    mut v___y_8324_: *mut crate::leanh::LeanObject,
    mut v___y_8325_: *mut crate::leanh::LeanObject,
    mut v___y_8326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8328_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_8324_, v___y_8325_, v___y_8326_);
    return v___x_8328_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___boxed(
    mut v___y_8329_: *mut crate::leanh::LeanObject,
    mut v___y_8330_: *mut crate::leanh::LeanObject,
    mut v___y_8331_: *mut crate::leanh::LeanObject,
    mut v___y_8332_: *mut crate::leanh::LeanObject,
    mut v___y_8333_: *mut crate::leanh::LeanObject,
    mut v___y_8334_: *mut crate::leanh::LeanObject,
    mut v___y_8335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8336_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(v___y_8329_, v___y_8330_, v___y_8331_, v___y_8332_, v___y_8333_, v___y_8334_);
    crate::leanh::lean_dec(v___y_8334_);
    crate::leanh::lean_dec_ref(v___y_8333_);
    crate::leanh::lean_dec(v___y_8332_);
    crate::leanh::lean_dec_ref(v___y_8331_);
    crate::leanh::lean_dec(v___y_8330_);
    crate::leanh::lean_dec_ref(v___y_8329_);
    return v_res_8336_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(
    mut v___y_8337_: *mut crate::leanh::LeanObject,
    mut v___y_8338_: *mut crate::leanh::LeanObject,
    mut v___y_8339_: *mut crate::leanh::LeanObject,
    mut v___y_8340_: *mut crate::leanh::LeanObject,
    mut v___y_8341_: *mut crate::leanh::LeanObject,
    mut v___y_8342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8344_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_8342_);
    return v___x_8344_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___boxed(
    mut v___y_8345_: *mut crate::leanh::LeanObject,
    mut v___y_8346_: *mut crate::leanh::LeanObject,
    mut v___y_8347_: *mut crate::leanh::LeanObject,
    mut v___y_8348_: *mut crate::leanh::LeanObject,
    mut v___y_8349_: *mut crate::leanh::LeanObject,
    mut v___y_8350_: *mut crate::leanh::LeanObject,
    mut v___y_8351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8352_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(v___y_8345_, v___y_8346_, v___y_8347_, v___y_8348_, v___y_8349_, v___y_8350_);
    crate::leanh::lean_dec(v___y_8350_);
    crate::leanh::lean_dec_ref(v___y_8349_);
    crate::leanh::lean_dec(v___y_8348_);
    crate::leanh::lean_dec_ref(v___y_8347_);
    crate::leanh::lean_dec(v___y_8346_);
    crate::leanh::lean_dec_ref(v___y_8345_);
    return v_res_8352_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(
    mut v_00_u03b1_8353_: *mut crate::leanh::LeanObject,
    mut v_x_8354_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_8355_: *mut crate::leanh::LeanObject,
    mut v___y_8356_: *mut crate::leanh::LeanObject,
    mut v___y_8357_: *mut crate::leanh::LeanObject,
    mut v___y_8358_: *mut crate::leanh::LeanObject,
    mut v___y_8359_: *mut crate::leanh::LeanObject,
    mut v___y_8360_: *mut crate::leanh::LeanObject,
    mut v___y_8361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8363_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_8354_, v_ctx_x3f_8355_, v___y_8356_, v___y_8357_, v___y_8358_, v___y_8359_, v___y_8360_, v___y_8361_);
    return v___x_8363_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___boxed(
    mut v_00_u03b1_8364_: *mut crate::leanh::LeanObject,
    mut v_x_8365_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_8366_: *mut crate::leanh::LeanObject,
    mut v___y_8367_: *mut crate::leanh::LeanObject,
    mut v___y_8368_: *mut crate::leanh::LeanObject,
    mut v___y_8369_: *mut crate::leanh::LeanObject,
    mut v___y_8370_: *mut crate::leanh::LeanObject,
    mut v___y_8371_: *mut crate::leanh::LeanObject,
    mut v___y_8372_: *mut crate::leanh::LeanObject,
    mut v___y_8373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8374_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(v_00_u03b1_8364_, v_x_8365_, v_ctx_x3f_8366_, v___y_8367_, v___y_8368_, v___y_8369_, v___y_8370_, v___y_8371_, v___y_8372_);
    crate::leanh::lean_dec(v___y_8372_);
    crate::leanh::lean_dec_ref(v___y_8371_);
    crate::leanh::lean_dec(v___y_8370_);
    crate::leanh::lean_dec_ref(v___y_8369_);
    crate::leanh::lean_dec(v___y_8368_);
    crate::leanh::lean_dec_ref(v___y_8367_);
    return v_res_8374_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(
    mut v_eval_8375_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_8376_: u8,
    mut v_onErr_8377_: *mut crate::leanh::LeanObject,
    mut v_init_8378_: *mut crate::leanh::LeanObject,
    mut v_cfg_8379_: *mut crate::leanh::LeanObject,
    mut v___y_8380_: *mut crate::leanh::LeanObject,
    mut v___y_8381_: *mut crate::leanh::LeanObject,
    mut v___y_8382_: *mut crate::leanh::LeanObject,
    mut v___y_8383_: *mut crate::leanh::LeanObject,
    mut v___y_8384_: *mut crate::leanh::LeanObject,
    mut v___y_8385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8387_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_8375_, v_logExceptions_8376_, v_onErr_8377_, v_init_8378_, v_cfg_8379_, v___y_8380_, v___y_8381_, v___y_8382_, v___y_8383_, v___y_8384_, v___y_8385_);
    return v___x_8387_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed(
    mut v_eval_8388_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_8389_: *mut crate::leanh::LeanObject,
    mut v_onErr_8390_: *mut crate::leanh::LeanObject,
    mut v_init_8391_: *mut crate::leanh::LeanObject,
    mut v_cfg_8392_: *mut crate::leanh::LeanObject,
    mut v___y_8393_: *mut crate::leanh::LeanObject,
    mut v___y_8394_: *mut crate::leanh::LeanObject,
    mut v___y_8395_: *mut crate::leanh::LeanObject,
    mut v___y_8396_: *mut crate::leanh::LeanObject,
    mut v___y_8397_: *mut crate::leanh::LeanObject,
    mut v___y_8398_: *mut crate::leanh::LeanObject,
    mut v___y_8399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_8400_: u8 = 0;
    let mut v_res_8401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8400_ = (crate::leanh::lean_unbox(v_logExceptions_8389_) as u8);
    v_res_8401_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(
        v_eval_8388_,
        v_logExceptions_boxed_8400_,
        v_onErr_8390_,
        v_init_8391_,
        v_cfg_8392_,
        v___y_8393_,
        v___y_8394_,
        v___y_8395_,
        v___y_8396_,
        v___y_8397_,
        v___y_8398_,
    );
    crate::leanh::lean_dec(v___y_8398_);
    crate::leanh::lean_dec_ref(v___y_8397_);
    crate::leanh::lean_dec(v___y_8396_);
    crate::leanh::lean_dec_ref(v___y_8395_);
    crate::leanh::lean_dec(v___y_8394_);
    crate::leanh::lean_dec_ref(v___y_8393_);
    return v_res_8401_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
    mut v_eval_8402_: *mut crate::leanh::LeanObject,
    mut v_init_8403_: *mut crate::leanh::LeanObject,
    mut v_cfg_8404_: *mut crate::leanh::LeanObject,
    mut v_onErr_8405_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_8406_: u8,
    mut v_a_8407_: *mut crate::leanh::LeanObject,
    mut v_a_8408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8413_: u8 = 0;
    let mut v___x_8414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8417_: u8 = 0;
    let mut v___x_8418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8420_: u8 = 0;
    let mut v___x_8421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8410_ = crate::leanh::lean_box((v_logExceptions_8406_) as usize);
                crate::leanh::lean_inc_n(v_cfg_8404_, 2);
                crate::leanh::lean_inc(v_init_8403_);
                v___f_8411_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_8411_, 0, v_eval_8402_);
                crate::leanh::lean_closure_set(v___f_8411_, 1, v___x_8410_);
                crate::leanh::lean_closure_set(v___f_8411_, 2, v_onErr_8405_);
                crate::leanh::lean_closure_set(v___f_8411_, 3, v_init_8403_);
                crate::leanh::lean_closure_set(v___f_8411_, 4, v_cfg_8404_);
                v___x_8416_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_8417_ = l_Lean_Syntax_matchesNull(v_cfg_8404_, v___x_8416_);
                if v___x_8417_ == 0 {
                    v___x_8418_ = l_Lean_Syntax_getNumArgs(v_cfg_8404_);
                    v___x_8419_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_8420_ = lean_nat_dec_eq(v___x_8418_, v___x_8419_);
                    crate::leanh::lean_dec(v___x_8418_);
                    if v___x_8420_ == 0 {
                        crate::leanh::lean_dec(v_cfg_8404_);
                        v___y_8413_ = v___x_8420_;
                        state = 1;
                        continue;
                    } else {
                        v___x_8421_ = l_Lean_Syntax_getArg(v_cfg_8404_, v___x_8416_);
                        crate::leanh::lean_dec(v_cfg_8404_);
                        v___x_8422_ = l_Lean_Syntax_matchesNull(v___x_8421_, v___x_8416_);
                        v___y_8413_ = v___x_8422_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_cfg_8404_);
                    v___y_8413_ = v___x_8417_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_8413_ == 0 {
                    crate::leanh::lean_dec(v_init_8403_);
                    v___x_8414_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(
                        v___f_8411_,
                        v_a_8407_,
                        v_a_8408_,
                    );
                    return v___x_8414_;
                } else {
                    crate::leanh::lean_dec_ref(v___f_8411_);
                    v___x_8415_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8415_, 0, v_init_8403_);
                    return v___x_8415_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___boxed(
    mut v_eval_8423_: *mut crate::leanh::LeanObject,
    mut v_init_8424_: *mut crate::leanh::LeanObject,
    mut v_cfg_8425_: *mut crate::leanh::LeanObject,
    mut v_onErr_8426_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_8427_: *mut crate::leanh::LeanObject,
    mut v_a_8428_: *mut crate::leanh::LeanObject,
    mut v_a_8429_: *mut crate::leanh::LeanObject,
    mut v_a_8430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_8431_: u8 = 0;
    let mut v_res_8432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8431_ = (crate::leanh::lean_unbox(v_logExceptions_8427_) as u8);
    v_res_8432_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
        v_eval_8423_,
        v_init_8424_,
        v_cfg_8425_,
        v_onErr_8426_,
        v_logExceptions_boxed_8431_,
        v_a_8428_,
        v_a_8429_,
    );
    crate::leanh::lean_dec(v_a_8429_);
    crate::leanh::lean_dec_ref(v_a_8428_);
    return v_res_8432_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(
    mut v_00_u03b1_8433_: *mut crate::leanh::LeanObject,
    mut v_eval_8434_: *mut crate::leanh::LeanObject,
    mut v_init_8435_: *mut crate::leanh::LeanObject,
    mut v_cfg_8436_: *mut crate::leanh::LeanObject,
    mut v_onErr_8437_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_8438_: u8,
    mut v_a_8439_: *mut crate::leanh::LeanObject,
    mut v_a_8440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8442_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
        v_eval_8434_,
        v_init_8435_,
        v_cfg_8436_,
        v_onErr_8437_,
        v_logExceptions_8438_,
        v_a_8439_,
        v_a_8440_,
    );
    return v___x_8442_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___boxed(
    mut v_00_u03b1_8443_: *mut crate::leanh::LeanObject,
    mut v_eval_8444_: *mut crate::leanh::LeanObject,
    mut v_init_8445_: *mut crate::leanh::LeanObject,
    mut v_cfg_8446_: *mut crate::leanh::LeanObject,
    mut v_onErr_8447_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_8448_: *mut crate::leanh::LeanObject,
    mut v_a_8449_: *mut crate::leanh::LeanObject,
    mut v_a_8450_: *mut crate::leanh::LeanObject,
    mut v_a_8451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_8452_: u8 = 0;
    let mut v_res_8453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8452_ = (crate::leanh::lean_unbox(v_logExceptions_8448_) as u8);
    v_res_8453_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(
        v_00_u03b1_8443_,
        v_eval_8444_,
        v_init_8445_,
        v_cfg_8446_,
        v_onErr_8447_,
        v_logExceptions_boxed_8452_,
        v_a_8449_,
        v_a_8450_,
    );
    crate::leanh::lean_dec(v_a_8450_);
    crate::leanh::lean_dec_ref(v_a_8449_);
    return v_res_8453_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(
    mut v_eval_8454_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_8455_: u8,
    mut v_onErr_8456_: *mut crate::leanh::LeanObject,
    mut v_init_8457_: *mut crate::leanh::LeanObject,
    mut v_cfgs_8458_: *mut crate::leanh::LeanObject,
    mut v___y_8459_: *mut crate::leanh::LeanObject,
    mut v___y_8460_: *mut crate::leanh::LeanObject,
    mut v___y_8461_: *mut crate::leanh::LeanObject,
    mut v___y_8462_: *mut crate::leanh::LeanObject,
    mut v___y_8463_: *mut crate::leanh::LeanObject,
    mut v___y_8464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8466_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_8454_, v_logExceptions_8455_, v_onErr_8456_, v_init_8457_, v_cfgs_8458_, v___y_8459_, v___y_8460_, v___y_8461_, v___y_8462_, v___y_8463_, v___y_8464_);
    return v___x_8466_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed(
    mut v_eval_8467_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_8468_: *mut crate::leanh::LeanObject,
    mut v_onErr_8469_: *mut crate::leanh::LeanObject,
    mut v_init_8470_: *mut crate::leanh::LeanObject,
    mut v_cfgs_8471_: *mut crate::leanh::LeanObject,
    mut v___y_8472_: *mut crate::leanh::LeanObject,
    mut v___y_8473_: *mut crate::leanh::LeanObject,
    mut v___y_8474_: *mut crate::leanh::LeanObject,
    mut v___y_8475_: *mut crate::leanh::LeanObject,
    mut v___y_8476_: *mut crate::leanh::LeanObject,
    mut v___y_8477_: *mut crate::leanh::LeanObject,
    mut v___y_8478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_8479_: u8 = 0;
    let mut v_res_8480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8479_ = (crate::leanh::lean_unbox(v_logExceptions_8468_) as u8);
    v_res_8480_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(
        v_eval_8467_,
        v_logExceptions_boxed_8479_,
        v_onErr_8469_,
        v_init_8470_,
        v_cfgs_8471_,
        v___y_8472_,
        v___y_8473_,
        v___y_8474_,
        v___y_8475_,
        v___y_8476_,
        v___y_8477_,
    );
    crate::leanh::lean_dec(v___y_8477_);
    crate::leanh::lean_dec_ref(v___y_8476_);
    crate::leanh::lean_dec(v___y_8475_);
    crate::leanh::lean_dec_ref(v___y_8474_);
    crate::leanh::lean_dec(v___y_8473_);
    crate::leanh::lean_dec_ref(v___y_8472_);
    crate::leanh::lean_dec_ref(v_cfgs_8471_);
    return v_res_8480_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(
    mut v_eval_8481_: *mut crate::leanh::LeanObject,
    mut v_init_8482_: *mut crate::leanh::LeanObject,
    mut v_cfgs_8483_: *mut crate::leanh::LeanObject,
    mut v_onErr_8484_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_8485_: u8,
    mut v_a_8486_: *mut crate::leanh::LeanObject,
    mut v_a_8487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8491_: u8 = 0;
    v___x_8489_ = lean_array_get_size(v_cfgs_8483_);
    v___x_8490_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_8491_ = lean_nat_dec_eq(v___x_8489_, v___x_8490_);
    if v___x_8491_ == 0 {
        let mut v___x_8492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_8493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_8492_ = crate::leanh::lean_box((v_logExceptions_8485_) as usize);
        v___f_8493_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            12,
            5,
        );
        crate::leanh::lean_closure_set(v___f_8493_, 0, v_eval_8481_);
        crate::leanh::lean_closure_set(v___f_8493_, 1, v___x_8492_);
        crate::leanh::lean_closure_set(v___f_8493_, 2, v_onErr_8484_);
        crate::leanh::lean_closure_set(v___f_8493_, 3, v_init_8482_);
        crate::leanh::lean_closure_set(v___f_8493_, 4, v_cfgs_8483_);
        v___x_8494_ =
            l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_8493_, v_a_8486_, v_a_8487_);
        return v___x_8494_;
    } else {
        let mut v___x_8495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_onErr_8484_);
        crate::leanh::lean_dec_ref(v_cfgs_8483_);
        crate::leanh::lean_dec_ref(v_eval_8481_);
        v___x_8495_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_8495_, 0, v_init_8482_);
        return v___x_8495_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___boxed(
    mut v_eval_8496_: *mut crate::leanh::LeanObject,
    mut v_init_8497_: *mut crate::leanh::LeanObject,
    mut v_cfgs_8498_: *mut crate::leanh::LeanObject,
    mut v_onErr_8499_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_8500_: *mut crate::leanh::LeanObject,
    mut v_a_8501_: *mut crate::leanh::LeanObject,
    mut v_a_8502_: *mut crate::leanh::LeanObject,
    mut v_a_8503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_8504_: u8 = 0;
    let mut v_res_8505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8504_ = (crate::leanh::lean_unbox(v_logExceptions_8500_) as u8);
    v_res_8505_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(
        v_eval_8496_,
        v_init_8497_,
        v_cfgs_8498_,
        v_onErr_8499_,
        v_logExceptions_boxed_8504_,
        v_a_8501_,
        v_a_8502_,
    );
    crate::leanh::lean_dec(v_a_8502_);
    crate::leanh::lean_dec_ref(v_a_8501_);
    return v_res_8505_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(
    mut v_00_u03b1_8506_: *mut crate::leanh::LeanObject,
    mut v_eval_8507_: *mut crate::leanh::LeanObject,
    mut v_init_8508_: *mut crate::leanh::LeanObject,
    mut v_cfgs_8509_: *mut crate::leanh::LeanObject,
    mut v_onErr_8510_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_8511_: u8,
    mut v_a_8512_: *mut crate::leanh::LeanObject,
    mut v_a_8513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8515_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(
        v_eval_8507_,
        v_init_8508_,
        v_cfgs_8509_,
        v_onErr_8510_,
        v_logExceptions_8511_,
        v_a_8512_,
        v_a_8513_,
    );
    return v___x_8515_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___boxed(
    mut v_00_u03b1_8516_: *mut crate::leanh::LeanObject,
    mut v_eval_8517_: *mut crate::leanh::LeanObject,
    mut v_init_8518_: *mut crate::leanh::LeanObject,
    mut v_cfgs_8519_: *mut crate::leanh::LeanObject,
    mut v_onErr_8520_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_8521_: *mut crate::leanh::LeanObject,
    mut v_a_8522_: *mut crate::leanh::LeanObject,
    mut v_a_8523_: *mut crate::leanh::LeanObject,
    mut v_a_8524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_8525_: u8 = 0;
    let mut v_res_8526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8525_ = (crate::leanh::lean_unbox(v_logExceptions_8521_) as u8);
    v_res_8526_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(
        v_00_u03b1_8516_,
        v_eval_8517_,
        v_init_8518_,
        v_cfgs_8519_,
        v_onErr_8520_,
        v_logExceptions_boxed_8525_,
        v_a_8522_,
        v_a_8523_,
    );
    crate::leanh::lean_dec(v_a_8523_);
    crate::leanh::lean_dec_ref(v_a_8522_);
    return v_res_8526_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ConfigEval_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ConfigEval_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ConfigEval_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_SyntheticMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval_Basic(builtin);
}
