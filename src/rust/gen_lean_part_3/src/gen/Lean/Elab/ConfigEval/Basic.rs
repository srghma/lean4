// Lean compiler output
// Module: Lean.Elab.ConfigEval.Basic
// Imports: Lean.Elab.ConfigEval.Types Lean.Elab.SyntheticMVars Lean.Elab.ConfigEval.Util
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
    lean_uint32_dec_eq, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
    lean_whnf,
};
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
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 11,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3_value) as *mut leanh::LeanObject,7932075773091973500 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5_value) as *mut leanh::LeanObject,7306243862518720553 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0_value:
    leanh::LeanStringObject<35> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0_value:
    leanh::LeanStringObject<36> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4_value:
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
    m_data: [32, 96, 0],
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2 as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value:
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
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value)
            as *mut leanh::LeanObject,
        12882480457794858234 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6_value)
            as *mut leanh::LeanObject,
        9255189395584251158 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value)
            as *mut leanh::LeanObject,
        12882480457794858234 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        15761733860085307253 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 58, 32, 0]};
static mut l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0_value:
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
    m_data: [105, 100, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0_value
        ) as *mut leanh::LeanObject,
        6041859491766292191 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5_value
        ) as *mut leanh::LeanObject,
        16753651297112092462 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8_value
        ) as *mut leanh::LeanObject,
        17728754291599005030 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2_value:
    leanh::LeanCtorObject<10> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 8
            + 16) as u16,
        other: 8,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        16843009 as *mut leanh::LeanObject,
        65537 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 24) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [
        282574488338432 as *mut leanh::LeanObject,
        72621647814721793 as *mut leanh::LeanObject,
        65793 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4: u64 = 0;
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_value:
    leanh::LeanCtorObject<7> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 7
            + 0) as u16,
        other: 7,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(
    mut v_inst_4264_: *mut leanh::LeanObject,
    mut v_stx_4265_: *mut leanh::LeanObject,
    mut v_a_4266_: *mut leanh::LeanObject,
    mut v_a_4267_: *mut leanh::LeanObject,
    mut v_a_4268_: *mut leanh::LeanObject,
    mut v_a_4269_: *mut leanh::LeanObject,
    mut v_a_4270_: *mut leanh::LeanObject,
    mut v_a_4271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_evalTerm_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4286_: u8 = 0;
    let mut v_cancelTk_x3f_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4288_: u8 = 0;
    let mut v_inheritedTraceOptions_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4296_: u8 = 0;
    let mut v_fst_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v_a_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalTerm_4273_ = leanh::lean_ctor_get(v_inst_4264_, 0);
                leanh::lean_inc_ref(v_evalTerm_4273_);
                leanh::lean_dec_ref(v_inst_4264_);
                v_fileName_4274_ = leanh::lean_ctor_get(v_a_4270_, 0);
                v_fileMap_4275_ = leanh::lean_ctor_get(v_a_4270_, 1);
                v_options_4276_ = leanh::lean_ctor_get(v_a_4270_, 2);
                v_currRecDepth_4277_ = leanh::lean_ctor_get(v_a_4270_, 3);
                v_maxRecDepth_4278_ = leanh::lean_ctor_get(v_a_4270_, 4);
                v_ref_4279_ = leanh::lean_ctor_get(v_a_4270_, 5);
                v_currNamespace_4280_ = leanh::lean_ctor_get(v_a_4270_, 6);
                v_openDecls_4281_ = leanh::lean_ctor_get(v_a_4270_, 7);
                v_initHeartbeats_4282_ = leanh::lean_ctor_get(v_a_4270_, 8);
                v_maxHeartbeats_4283_ = leanh::lean_ctor_get(v_a_4270_, 9);
                v_quotContext_4284_ = leanh::lean_ctor_get(v_a_4270_, 10);
                v_currMacroScope_4285_ = leanh::lean_ctor_get(v_a_4270_, 11);
                v_diag_4286_ = leanh::lean_ctor_get_uint8(
                    v_a_4270_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4287_ = leanh::lean_ctor_get(v_a_4270_, 12);
                v_suppressElabErrors_4288_ = leanh::lean_ctor_get_uint8(
                    v_a_4270_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4289_ = leanh::lean_ctor_get(v_a_4270_, 13);
                v_ref_4290_ = l_Lean_replaceRef(v_stx_4265_, v_ref_4279_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_4289_);
                leanh::lean_inc(v_cancelTk_x3f_4287_);
                leanh::lean_inc(v_currMacroScope_4285_);
                leanh::lean_inc(v_quotContext_4284_);
                leanh::lean_inc(v_maxHeartbeats_4283_);
                leanh::lean_inc(v_initHeartbeats_4282_);
                leanh::lean_inc(v_openDecls_4281_);
                leanh::lean_inc(v_currNamespace_4280_);
                leanh::lean_inc(v_maxRecDepth_4278_);
                leanh::lean_inc(v_currRecDepth_4277_);
                leanh::lean_inc_ref(v_options_4276_);
                leanh::lean_inc_ref(v_fileMap_4275_);
                leanh::lean_inc_ref(v_fileName_4274_);
                v___x_4291_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_4291_, 0, v_fileName_4274_);
                leanh::lean_ctor_set(v___x_4291_, 1, v_fileMap_4275_);
                leanh::lean_ctor_set(v___x_4291_, 2, v_options_4276_);
                leanh::lean_ctor_set(v___x_4291_, 3, v_currRecDepth_4277_);
                leanh::lean_ctor_set(v___x_4291_, 4, v_maxRecDepth_4278_);
                leanh::lean_ctor_set(v___x_4291_, 5, v_ref_4290_);
                leanh::lean_ctor_set(v___x_4291_, 6, v_currNamespace_4280_);
                leanh::lean_ctor_set(v___x_4291_, 7, v_openDecls_4281_);
                leanh::lean_ctor_set(v___x_4291_, 8, v_initHeartbeats_4282_);
                leanh::lean_ctor_set(v___x_4291_, 9, v_maxHeartbeats_4283_);
                leanh::lean_ctor_set(v___x_4291_, 10, v_quotContext_4284_);
                leanh::lean_ctor_set(v___x_4291_, 11, v_currMacroScope_4285_);
                leanh::lean_ctor_set(v___x_4291_, 12, v_cancelTk_x3f_4287_);
                leanh::lean_ctor_set(v___x_4291_, 13, v_inheritedTraceOptions_4289_);
                leanh::lean_ctor_set_uint8(
                    v___x_4291_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_4286_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4291_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4288_,
                );
                leanh::lean_inc(v_a_4271_);
                leanh::lean_inc(v_a_4269_);
                leanh::lean_inc_ref(v_a_4268_);
                leanh::lean_inc(v_a_4267_);
                leanh::lean_inc_ref(v_a_4266_);
                v___x_4292_ = leanh::lean_apply_8(
                    v_evalTerm_4273_,
                    v_stx_4265_,
                    v_a_4266_,
                    v_a_4267_,
                    v_a_4268_,
                    v_a_4269_,
                    v___x_4291_,
                    v_a_4271_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4292_) == 0 {
                    v_a_4293_ = leanh::lean_ctor_get(v___x_4292_, 0);
                    v_isSharedCheck_4301_ = (!leanh::lean_is_exclusive(v___x_4292_)) as u8;
                    if v_isSharedCheck_4301_ == 0 {
                        v___x_4295_ = v___x_4292_;
                        v_isShared_4296_ = v_isSharedCheck_4301_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4293_);
                        leanh::lean_dec(v___x_4292_);
                        v___x_4295_ = leanh::lean_box(0);
                        v_isShared_4296_ = v_isSharedCheck_4301_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4302_ = leanh::lean_ctor_get(v___x_4292_, 0);
                    v_isSharedCheck_4309_ = (!leanh::lean_is_exclusive(v___x_4292_)) as u8;
                    if v_isSharedCheck_4309_ == 0 {
                        v___x_4304_ = v___x_4292_;
                        v_isShared_4305_ = v_isSharedCheck_4309_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4302_);
                        leanh::lean_dec(v___x_4292_);
                        v___x_4304_ = leanh::lean_box(0);
                        v_isShared_4305_ = v_isSharedCheck_4309_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4297_ = leanh::lean_ctor_get(v_a_4293_, 0);
                leanh::lean_inc(v_fst_4297_);
                leanh::lean_dec(v_a_4293_);
                if v_isShared_4296_ == 0 {
                    leanh::lean_ctor_set(v___x_4295_, 0, v_fst_4297_);
                    v___x_4299_ = v___x_4295_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_fst_4297_);
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
                    v_reuseFailAlloc_4308_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
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
    mut v_inst_4310_: *mut leanh::LeanObject,
    mut v_stx_4311_: *mut leanh::LeanObject,
    mut v_a_4312_: *mut leanh::LeanObject,
    mut v_a_4313_: *mut leanh::LeanObject,
    mut v_a_4314_: *mut leanh::LeanObject,
    mut v_a_4315_: *mut leanh::LeanObject,
    mut v_a_4316_: *mut leanh::LeanObject,
    mut v_a_4317_: *mut leanh::LeanObject,
    mut v_a_4318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4317_);
    leanh::lean_dec_ref(v_a_4316_);
    leanh::lean_dec(v_a_4315_);
    leanh::lean_dec_ref(v_a_4314_);
    leanh::lean_dec(v_a_4313_);
    leanh::lean_dec_ref(v_a_4312_);
    return v_res_4319_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermWithRef(
    mut v_00_u03b1_4320_: *mut leanh::LeanObject,
    mut v_inst_4321_: *mut leanh::LeanObject,
    mut v_stx_4322_: *mut leanh::LeanObject,
    mut v_a_4323_: *mut leanh::LeanObject,
    mut v_a_4324_: *mut leanh::LeanObject,
    mut v_a_4325_: *mut leanh::LeanObject,
    mut v_a_4326_: *mut leanh::LeanObject,
    mut v_a_4327_: *mut leanh::LeanObject,
    mut v_a_4328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4331_: *mut leanh::LeanObject,
    mut v_inst_4332_: *mut leanh::LeanObject,
    mut v_stx_4333_: *mut leanh::LeanObject,
    mut v_a_4334_: *mut leanh::LeanObject,
    mut v_a_4335_: *mut leanh::LeanObject,
    mut v_a_4336_: *mut leanh::LeanObject,
    mut v_a_4337_: *mut leanh::LeanObject,
    mut v_a_4338_: *mut leanh::LeanObject,
    mut v_a_4339_: *mut leanh::LeanObject,
    mut v_a_4340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4339_);
    leanh::lean_dec_ref(v_a_4338_);
    leanh::lean_dec(v_a_4337_);
    leanh::lean_dec_ref(v_a_4336_);
    leanh::lean_dec(v_a_4335_);
    leanh::lean_dec_ref(v_a_4334_);
    return v_res_4341_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4342_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_4342_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4343_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0,
    );
    v___x_4344_ = l_StateRefT_x27_instMonad___redArg(v___x_4343_);
    return v___x_4344_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4353_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_4354_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4354_, 0, v___x_4353_);
    return v___f_4354_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4355_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_4356_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_4356_, 0, v___x_4355_);
    return v___f_4356_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___f_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4357_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11,
    );
    v___f_4358_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10,
    );
    v___x_4359_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4359_, 0, v___f_4358_);
    leanh::lean_ctor_set(v___x_4359_, 1, v___f_4357_);
    return v___x_4359_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4360_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12,
    );
    v___f_4361_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4361_, 0, v___x_4360_);
    return v___f_4361_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4362_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12,
    );
    v___f_4363_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_4363_, 0, v___x_4362_);
    return v___f_4363_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___f_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4364_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14,
    );
    v___f_4365_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13,
    );
    v___x_4366_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4366_, 0, v___f_4365_);
    leanh::lean_ctor_set(v___x_4366_, 1, v___f_4364_);
    return v___x_4366_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4367_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15,
    );
    v___f_4368_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4368_, 0, v___x_4367_);
    return v___f_4368_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15,
    );
    v___f_4370_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_4370_, 0, v___x_4369_);
    return v___f_4370_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___f_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4371_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17,
    );
    v___f_4372_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16,
    );
    v___x_4373_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4373_, 0, v___f_4372_);
    leanh::lean_ctor_set(v___x_4373_, 1, v___f_4371_);
    return v___x_4373_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4374_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18,
    );
    v___f_4375_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4375_, 0, v___x_4374_);
    return v___f_4375_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4376_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18,
    );
    v___f_4377_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_4377_, 0, v___x_4376_);
    return v___f_4377_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21()
-> *mut leanh::LeanObject {
    let mut v___f_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4378_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20,
    );
    v___f_4379_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19,
    );
    v___x_4380_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4380_, 0, v___f_4379_);
    leanh::lean_ctor_set(v___x_4380_, 1, v___f_4378_);
    return v___x_4380_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4381_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21,
    );
    v___x_4382_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_4381_);
    return v___x_4382_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4384_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23;
    v___x_4385_ = l_Lean_stringToMessageData(v___x_4384_);
    return v___x_4385_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4387_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25;
    v___x_4388_ = l_Lean_stringToMessageData(v___x_4387_);
    return v___x_4388_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4390_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27;
    v___x_4391_ = l_Lean_stringToMessageData(v___x_4390_);
    return v___x_4391_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4393_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29;
    v___x_4394_ = l_Lean_stringToMessageData(v___x_4393_);
    return v___x_4394_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4396_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31;
    v___x_4397_ = l_Lean_stringToMessageData(v___x_4396_);
    return v___x_4397_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(
    mut v_inst_4398_: *mut leanh::LeanObject,
    mut v_stx_4399_: *mut leanh::LeanObject,
    mut v_a_4400_: *mut leanh::LeanObject,
    mut v_a_4401_: *mut leanh::LeanObject,
    mut v_a_4402_: *mut leanh::LeanObject,
    mut v_a_4403_: *mut leanh::LeanObject,
    mut v_a_4404_: *mut leanh::LeanObject,
    mut v_a_4405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4427_: u8 = 0;
    let mut v_toFunctor_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4434_: u8 = 0;
    let mut v___f_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4451_: u8 = 0;
    let mut v_toFunctor_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4458_: u8 = 0;
    let mut v___f_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadQuotation_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getMCtx_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyMCtx_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalExpr_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4492_: u8 = 0;
    let mut v___x_4493_: u8 = 0;
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4510_: u8 = 0;
    let mut v_cancelTk_x3f_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4512_: u8 = 0;
    let mut v_inheritedTraceOptions_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: u8 = 0;
    let mut v_ref_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751__overap_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802__overap_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4548_: u8 = 0;
    let mut v_id_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4552_: u8 = 0;
    let mut v___x_4553_: u8 = 0;
    let mut v_val_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4563_: u8 = 0;
    let mut v_unused_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: u8 = 0;
    let mut v___x_4576_: u8 = 0;
    let mut v___y_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: u8 = 0;
    let mut v___x_4071__overap_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4594_: u8 = 0;
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4598_: u8 = 0;
    let mut v_a_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4602_: u8 = 0;
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4606_: u8 = 0;
    let mut v_a_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4610_: u8 = 0;
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4614_: u8 = 0;
    let mut v___y_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938__overap_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4630_: u8 = 0;
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4634_: u8 = 0;
    let mut v___x_4635_: u8 = 0;
    let mut v___x_4636_: u8 = 0;
    let mut v___x_3959__overap_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4642_: u8 = 0;
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4646_: u8 = 0;
    let mut v_a_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4650_: u8 = 0;
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4654_: u8 = 0;
    let mut v_a_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4658_: u8 = 0;
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_isSharedCheck_4663_: u8 = 0;
    let mut v_reuseFailAlloc_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4666_: u8 = 0;
    let mut v_unused_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4668_: u8 = 0;
    let mut v_unused_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4672_: u8 = 0;
    let mut v_unused_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4674_: u8 = 0;
    let mut v_unused_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4407_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1,
                );
                v_toApplicative_4408_ = leanh::lean_ctor_get(v___x_4407_, 0);
                v_toFunctor_4409_ = leanh::lean_ctor_get(v_toApplicative_4408_, 0);
                v_toSeq_4410_ = leanh::lean_ctor_get(v_toApplicative_4408_, 2);
                v_toSeqLeft_4411_ = leanh::lean_ctor_get(v_toApplicative_4408_, 3);
                v_toSeqRight_4412_ = leanh::lean_ctor_get(v_toApplicative_4408_, 4);
                v___f_4413_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2;
                v___f_4414_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_4409_, 2);
                v___f_4415_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4415_, 0, v_toFunctor_4409_);
                v___f_4416_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4416_, 0, v_toFunctor_4409_);
                v___x_4417_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4417_, 0, v___f_4415_);
                leanh::lean_ctor_set(v___x_4417_, 1, v___f_4416_);
                leanh::lean_inc(v_toSeqRight_4412_);
                v___f_4418_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4418_, 0, v_toSeqRight_4412_);
                leanh::lean_inc(v_toSeqLeft_4411_);
                v___f_4419_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4419_, 0, v_toSeqLeft_4411_);
                leanh::lean_inc(v_toSeq_4410_);
                v___f_4420_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4420_, 0, v_toSeq_4410_);
                v___x_4421_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_4421_, 0, v___x_4417_);
                leanh::lean_ctor_set(v___x_4421_, 1, v___f_4413_);
                leanh::lean_ctor_set(v___x_4421_, 2, v___f_4420_);
                leanh::lean_ctor_set(v___x_4421_, 3, v___f_4419_);
                leanh::lean_ctor_set(v___x_4421_, 4, v___f_4418_);
                v___x_4422_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4422_, 0, v___x_4421_);
                leanh::lean_ctor_set(v___x_4422_, 1, v___f_4414_);
                v___x_4423_ = l_StateRefT_x27_instMonad___redArg(v___x_4422_);
                v_toApplicative_4424_ = leanh::lean_ctor_get(v___x_4423_, 0);
                v_isSharedCheck_4674_ = (!leanh::lean_is_exclusive(v___x_4423_)) as u8;
                if v_isSharedCheck_4674_ == 0 {
                    v_unused_4675_ = leanh::lean_ctor_get(v___x_4423_, 1);
                    leanh::lean_dec(v_unused_4675_);
                    v___x_4426_ = v___x_4423_;
                    v_isShared_4427_ = v_isSharedCheck_4674_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_4424_);
                    leanh::lean_dec(v___x_4423_);
                    v___x_4426_ = leanh::lean_box(0);
                    v_isShared_4427_ = v_isSharedCheck_4674_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4428_ = leanh::lean_ctor_get(v_toApplicative_4424_, 0);
                v_toSeq_4429_ = leanh::lean_ctor_get(v_toApplicative_4424_, 2);
                v_toSeqLeft_4430_ = leanh::lean_ctor_get(v_toApplicative_4424_, 3);
                v_toSeqRight_4431_ = leanh::lean_ctor_get(v_toApplicative_4424_, 4);
                v_isSharedCheck_4672_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_4424_)) as u8;
                if v_isSharedCheck_4672_ == 0 {
                    v_unused_4673_ = leanh::lean_ctor_get(v_toApplicative_4424_, 1);
                    leanh::lean_dec(v_unused_4673_);
                    v___x_4433_ = v_toApplicative_4424_;
                    v_isShared_4434_ = v_isSharedCheck_4672_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_4431_);
                    leanh::lean_inc(v_toSeqLeft_4430_);
                    leanh::lean_inc(v_toSeq_4429_);
                    leanh::lean_inc(v_toFunctor_4428_);
                    leanh::lean_dec(v_toApplicative_4424_);
                    v___x_4433_ = leanh::lean_box(0);
                    v_isShared_4434_ = v_isSharedCheck_4672_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4435_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4;
                v___f_4436_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_4428_);
                v___f_4437_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4437_, 0, v_toFunctor_4428_);
                v___f_4438_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4438_, 0, v_toFunctor_4428_);
                v___x_4439_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4439_, 0, v___f_4437_);
                leanh::lean_ctor_set(v___x_4439_, 1, v___f_4438_);
                v___f_4440_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4440_, 0, v_toSeqRight_4431_);
                v___f_4441_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4441_, 0, v_toSeqLeft_4430_);
                v___f_4442_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4442_, 0, v_toSeq_4429_);
                if v_isShared_4434_ == 0 {
                    leanh::lean_ctor_set(v___x_4433_, 4, v___f_4440_);
                    leanh::lean_ctor_set(v___x_4433_, 3, v___f_4441_);
                    leanh::lean_ctor_set(v___x_4433_, 2, v___f_4442_);
                    leanh::lean_ctor_set(v___x_4433_, 1, v___f_4435_);
                    leanh::lean_ctor_set(v___x_4433_, 0, v___x_4439_);
                    v___x_4444_ = v___x_4433_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4671_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 0, v___x_4439_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 1, v___f_4435_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 2, v___f_4442_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 3, v___f_4441_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 4, v___f_4440_);
                    v___x_4444_ = v_reuseFailAlloc_4671_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4427_ == 0 {
                    leanh::lean_ctor_set(v___x_4426_, 1, v___f_4436_);
                    leanh::lean_ctor_set(v___x_4426_, 0, v___x_4444_);
                    v___x_4446_ = v___x_4426_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4670_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4444_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4670_, 1, v___f_4436_);
                    v___x_4446_ = v_reuseFailAlloc_4670_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4447_ = l_StateRefT_x27_instMonad___redArg(v___x_4446_);
                v_toApplicative_4448_ = leanh::lean_ctor_get(v___x_4447_, 0);
                v_isSharedCheck_4668_ = (!leanh::lean_is_exclusive(v___x_4447_)) as u8;
                if v_isSharedCheck_4668_ == 0 {
                    v_unused_4669_ = leanh::lean_ctor_get(v___x_4447_, 1);
                    leanh::lean_dec(v_unused_4669_);
                    v___x_4450_ = v___x_4447_;
                    v_isShared_4451_ = v_isSharedCheck_4668_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_4448_);
                    leanh::lean_dec(v___x_4447_);
                    v___x_4450_ = leanh::lean_box(0);
                    v_isShared_4451_ = v_isSharedCheck_4668_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4452_ = leanh::lean_ctor_get(v_toApplicative_4448_, 0);
                v_toSeq_4453_ = leanh::lean_ctor_get(v_toApplicative_4448_, 2);
                v_toSeqLeft_4454_ = leanh::lean_ctor_get(v_toApplicative_4448_, 3);
                v_toSeqRight_4455_ = leanh::lean_ctor_get(v_toApplicative_4448_, 4);
                v_isSharedCheck_4666_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_4448_)) as u8;
                if v_isSharedCheck_4666_ == 0 {
                    v_unused_4667_ = leanh::lean_ctor_get(v_toApplicative_4448_, 1);
                    leanh::lean_dec(v_unused_4667_);
                    v___x_4457_ = v_toApplicative_4448_;
                    v_isShared_4458_ = v_isSharedCheck_4666_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_4455_);
                    leanh::lean_inc(v_toSeqLeft_4454_);
                    leanh::lean_inc(v_toSeq_4453_);
                    leanh::lean_inc(v_toFunctor_4452_);
                    leanh::lean_dec(v_toApplicative_4448_);
                    v___x_4457_ = leanh::lean_box(0);
                    v_isShared_4458_ = v_isSharedCheck_4666_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4459_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6;
                v___f_4460_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7;
                leanh::lean_inc_ref(v_toFunctor_4452_);
                v___f_4461_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4461_, 0, v_toFunctor_4452_);
                v___f_4462_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4462_, 0, v_toFunctor_4452_);
                v___x_4463_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4463_, 0, v___f_4461_);
                leanh::lean_ctor_set(v___x_4463_, 1, v___f_4462_);
                v___f_4464_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4464_, 0, v_toSeqRight_4455_);
                v___f_4465_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4465_, 0, v_toSeqLeft_4454_);
                v___f_4466_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4466_, 0, v_toSeq_4453_);
                if v_isShared_4458_ == 0 {
                    leanh::lean_ctor_set(v___x_4457_, 4, v___f_4464_);
                    leanh::lean_ctor_set(v___x_4457_, 3, v___f_4465_);
                    leanh::lean_ctor_set(v___x_4457_, 2, v___f_4466_);
                    leanh::lean_ctor_set(v___x_4457_, 1, v___f_4459_);
                    leanh::lean_ctor_set(v___x_4457_, 0, v___x_4463_);
                    v___x_4468_ = v___x_4457_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4665_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 1, v___f_4459_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 2, v___f_4466_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 3, v___f_4465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 4, v___f_4464_);
                    v___x_4468_ = v_reuseFailAlloc_4665_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4451_ == 0 {
                    leanh::lean_ctor_set(v___x_4450_, 1, v___f_4460_);
                    leanh::lean_ctor_set(v___x_4450_, 0, v___x_4468_);
                    v___x_4470_ = v___x_4450_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4664_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4468_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4664_, 1, v___f_4460_);
                    v___x_4470_ = v_reuseFailAlloc_4664_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4471_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
                v_toMonadQuotation_4472_ = leanh::lean_ctor_get(v___x_4471_, 0);
                v_toMonadRef_4473_ = leanh::lean_ctor_get(v_toMonadQuotation_4472_, 0);
                v___x_4474_ = l_Lean_Meta_instMonadMCtxMetaM;
                v_getMCtx_4475_ = leanh::lean_ctor_get(v___x_4474_, 0);
                v_modifyMCtx_4476_ = leanh::lean_ctor_get(v___x_4474_, 1);
                v___f_4477_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8;
                v___x_4478_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9;
                leanh::lean_inc(v_modifyMCtx_4476_);
                v___f_4479_ = leanh::lean_alloc_closure(
                    l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_4479_, 0, v_modifyMCtx_4476_);
                leanh::lean_closure_set(v___f_4479_, 1, v___x_4478_);
                leanh::lean_inc(v_getMCtx_4475_);
                v___x_4480_ = leanh::lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___x_4480_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_4480_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_4480_, 2, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_4480_, 3, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_4480_, 4, v_getMCtx_4475_);
                v___f_4481_ = leanh::lean_alloc_closure(
                    l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_4481_, 0, v___f_4479_);
                leanh::lean_closure_set(v___f_4481_, 1, v___f_4477_);
                v___x_4482_ = leanh::lean_alloc_closure(
                    l_ReaderT_instMonadLift___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___x_4482_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_4482_, 1, v___x_4480_);
                v___x_4483_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4483_, 0, v___x_4482_);
                leanh::lean_ctor_set(v___x_4483_, 1, v___f_4481_);
                v___x_4484_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21,
                );
                v___x_4485_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
                leanh::lean_inc_ref(v_toMonadRef_4473_);
                v___x_4486_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4486_, 0, v___x_4484_);
                leanh::lean_ctor_set(v___x_4486_, 1, v_toMonadRef_4473_);
                leanh::lean_ctor_set(v___x_4486_, 2, v___x_4485_);
                v___x_4487_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22,
                );
                v_evalExpr_4488_ = leanh::lean_ctor_get(v_inst_4398_, 0);
                v_expectedType_x3f_4489_ = leanh::lean_ctor_get(v_inst_4398_, 1);
                v_isSharedCheck_4663_ = (!leanh::lean_is_exclusive(v_inst_4398_)) as u8;
                if v_isSharedCheck_4663_ == 0 {
                    v___x_4491_ = v_inst_4398_;
                    v_isShared_4492_ = v_isSharedCheck_4663_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_expectedType_x3f_4489_);
                    leanh::lean_inc(v_evalExpr_4488_);
                    leanh::lean_dec(v_inst_4398_);
                    v___x_4491_ = leanh::lean_box(0);
                    v_isShared_4492_ = v_isSharedCheck_4663_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4493_ = 1;
                v___x_4494_ = leanh::lean_box(0);
                v___x_4495_ = leanh::lean_box((v___x_4493_) as usize);
                v___x_4496_ = leanh::lean_box((v___x_4493_) as usize);
                leanh::lean_inc(v_expectedType_x3f_4489_);
                leanh::lean_inc(v_stx_4399_);
                v___x_4497_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                leanh::lean_closure_set(v___x_4497_, 0, v_stx_4399_);
                leanh::lean_closure_set(v___x_4497_, 1, v_expectedType_x3f_4489_);
                leanh::lean_closure_set(v___x_4497_, 2, v___x_4495_);
                leanh::lean_closure_set(v___x_4497_, 3, v___x_4496_);
                leanh::lean_closure_set(v___x_4497_, 4, v___x_4494_);
                v_fileName_4498_ = leanh::lean_ctor_get(v_a_4404_, 0);
                v_fileMap_4499_ = leanh::lean_ctor_get(v_a_4404_, 1);
                v_options_4500_ = leanh::lean_ctor_get(v_a_4404_, 2);
                v_currRecDepth_4501_ = leanh::lean_ctor_get(v_a_4404_, 3);
                v_maxRecDepth_4502_ = leanh::lean_ctor_get(v_a_4404_, 4);
                v_ref_4503_ = leanh::lean_ctor_get(v_a_4404_, 5);
                v_currNamespace_4504_ = leanh::lean_ctor_get(v_a_4404_, 6);
                v_openDecls_4505_ = leanh::lean_ctor_get(v_a_4404_, 7);
                v_initHeartbeats_4506_ = leanh::lean_ctor_get(v_a_4404_, 8);
                v_maxHeartbeats_4507_ = leanh::lean_ctor_get(v_a_4404_, 9);
                v_quotContext_4508_ = leanh::lean_ctor_get(v_a_4404_, 10);
                v_currMacroScope_4509_ = leanh::lean_ctor_get(v_a_4404_, 11);
                v_diag_4510_ = leanh::lean_ctor_get_uint8(
                    v_a_4404_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4511_ = leanh::lean_ctor_get(v_a_4404_, 12);
                v_suppressElabErrors_4512_ = leanh::lean_ctor_get_uint8(
                    v_a_4404_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4513_ = leanh::lean_ctor_get(v_a_4404_, 13);
                v___x_4514_ = 1;
                v_ref_4515_ = l_Lean_replaceRef(v_stx_4399_, v_ref_4503_);
                leanh::lean_dec(v_stx_4399_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_4513_);
                leanh::lean_inc(v_cancelTk_x3f_4511_);
                leanh::lean_inc(v_currMacroScope_4509_);
                leanh::lean_inc(v_quotContext_4508_);
                leanh::lean_inc(v_maxHeartbeats_4507_);
                leanh::lean_inc(v_initHeartbeats_4506_);
                leanh::lean_inc(v_openDecls_4505_);
                leanh::lean_inc(v_currNamespace_4504_);
                leanh::lean_inc(v_maxRecDepth_4502_);
                leanh::lean_inc(v_currRecDepth_4501_);
                leanh::lean_inc_ref(v_options_4500_);
                leanh::lean_inc_ref(v_fileMap_4499_);
                leanh::lean_inc_ref(v_fileName_4498_);
                v___x_4516_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_4516_, 0, v_fileName_4498_);
                leanh::lean_ctor_set(v___x_4516_, 1, v_fileMap_4499_);
                leanh::lean_ctor_set(v___x_4516_, 2, v_options_4500_);
                leanh::lean_ctor_set(v___x_4516_, 3, v_currRecDepth_4501_);
                leanh::lean_ctor_set(v___x_4516_, 4, v_maxRecDepth_4502_);
                leanh::lean_ctor_set(v___x_4516_, 5, v_ref_4515_);
                leanh::lean_ctor_set(v___x_4516_, 6, v_currNamespace_4504_);
                leanh::lean_ctor_set(v___x_4516_, 7, v_openDecls_4505_);
                leanh::lean_ctor_set(v___x_4516_, 8, v_initHeartbeats_4506_);
                leanh::lean_ctor_set(v___x_4516_, 9, v_maxHeartbeats_4507_);
                leanh::lean_ctor_set(v___x_4516_, 10, v_quotContext_4508_);
                leanh::lean_ctor_set(v___x_4516_, 11, v_currMacroScope_4509_);
                leanh::lean_ctor_set(v___x_4516_, 12, v_cancelTk_x3f_4511_);
                leanh::lean_ctor_set(v___x_4516_, 13, v_inheritedTraceOptions_4513_);
                leanh::lean_ctor_set_uint8(
                    v___x_4516_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_4510_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4516_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4512_,
                );
                v___x_4517_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        leanh::lean_box(0),
                        v___x_4497_,
                        v___x_4514_,
                        v_a_4400_,
                        v_a_4401_,
                        v_a_4402_,
                        v_a_4403_,
                        v___x_4516_,
                        v_a_4405_,
                    );
                if leanh::lean_obj_tag(v___x_4517_) == 0 {
                    v_a_4518_ = leanh::lean_ctor_get(v___x_4517_, 0);
                    leanh::lean_inc(v_a_4518_);
                    leanh::lean_dec_ref_known(v___x_4517_, 1);
                    leanh::lean_inc_ref(v___x_4470_);
                    v___x_3751__overap_4519_ =
                        l_Lean_instantiateMVars___redArg(v___x_4470_, v___x_4483_, v_a_4518_);
                    leanh::lean_inc(v_a_4405_);
                    leanh::lean_inc_ref(v___x_4516_);
                    leanh::lean_inc(v_a_4403_);
                    leanh::lean_inc_ref(v_a_4402_);
                    leanh::lean_inc(v_a_4401_);
                    leanh::lean_inc_ref(v_a_4400_);
                    v___x_4520_ = leanh::lean_apply_7(
                        v___x_3751__overap_4519_,
                        v_a_4400_,
                        v_a_4401_,
                        v_a_4402_,
                        v_a_4403_,
                        v___x_4516_,
                        v_a_4405_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_4520_) == 0 {
                        v_a_4521_ = leanh::lean_ctor_get(v___x_4520_, 0);
                        leanh::lean_inc(v_a_4521_);
                        leanh::lean_dec_ref_known(v___x_4520_, 1);
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
                                leanh::lean_inc(v_a_4405_);
                                leanh::lean_inc_ref(v___x_4516_);
                                leanh::lean_inc(v_a_4403_);
                                leanh::lean_inc_ref(v_a_4402_);
                                leanh::lean_inc(v_a_4401_);
                                leanh::lean_inc_ref(v_a_4400_);
                                v___x_4638_ = leanh::lean_apply_7(
                                    v___x_3959__overap_4637_,
                                    v_a_4400_,
                                    v_a_4401_,
                                    v_a_4402_,
                                    v_a_4403_,
                                    v___x_4516_,
                                    v_a_4405_,
                                    leanh::lean_box(0),
                                );
                                if leanh::lean_obj_tag(v___x_4638_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4638_, 1);
                                    v___y_4616_ = v_a_4400_;
                                    v___y_4617_ = v_a_4401_;
                                    v___y_4618_ = v_a_4402_;
                                    v___y_4619_ = v_a_4403_;
                                    v___y_4620_ = v___x_4516_;
                                    v___y_4621_ = v_a_4405_;
                                    state = 23;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_4521_);
                                    leanh::lean_dec_ref_known(v___x_4516_, 14);
                                    leanh::lean_del_object(v___x_4491_);
                                    leanh::lean_dec(v_expectedType_x3f_4489_);
                                    leanh::lean_dec_ref(v_evalExpr_4488_);
                                    leanh::lean_dec_ref_known(v___x_4486_, 3);
                                    leanh::lean_dec_ref(v___x_4470_);
                                    v_a_4639_ = leanh::lean_ctor_get(v___x_4638_, 0);
                                    v_isSharedCheck_4646_ =
                                        (!leanh::lean_is_exclusive(v___x_4638_)) as u8;
                                    if v_isSharedCheck_4646_ == 0 {
                                        v___x_4641_ = v___x_4638_;
                                        v_isShared_4642_ = v_isSharedCheck_4646_;
                                        state = 26;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4639_);
                                        leanh::lean_dec(v___x_4638_);
                                        v___x_4641_ = leanh::lean_box(0);
                                        v_isShared_4642_ = v_isSharedCheck_4646_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_4516_, 14);
                        leanh::lean_del_object(v___x_4491_);
                        leanh::lean_dec(v_expectedType_x3f_4489_);
                        leanh::lean_dec_ref(v_evalExpr_4488_);
                        leanh::lean_dec_ref_known(v___x_4486_, 3);
                        leanh::lean_dec_ref(v___x_4470_);
                        v_a_4647_ = leanh::lean_ctor_get(v___x_4520_, 0);
                        v_isSharedCheck_4654_ =
                            (!leanh::lean_is_exclusive(v___x_4520_)) as u8;
                        if v_isSharedCheck_4654_ == 0 {
                            v___x_4649_ = v___x_4520_;
                            v_isShared_4650_ = v_isSharedCheck_4654_;
                            state = 28;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4647_);
                            leanh::lean_dec(v___x_4520_);
                            v___x_4649_ = leanh::lean_box(0);
                            v_isShared_4650_ = v_isSharedCheck_4654_;
                            state = 28;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_4516_, 14);
                    leanh::lean_del_object(v___x_4491_);
                    leanh::lean_dec(v_expectedType_x3f_4489_);
                    leanh::lean_dec_ref(v_evalExpr_4488_);
                    leanh::lean_dec_ref_known(v___x_4486_, 3);
                    leanh::lean_dec_ref_known(v___x_4483_, 2);
                    leanh::lean_dec_ref(v___x_4470_);
                    v_a_4655_ = leanh::lean_ctor_get(v___x_4517_, 0);
                    v_isSharedCheck_4662_ = (!leanh::lean_is_exclusive(v___x_4517_)) as u8;
                    if v_isSharedCheck_4662_ == 0 {
                        v___x_4657_ = v___x_4517_;
                        v_isShared_4658_ = v_isSharedCheck_4662_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4655_);
                        leanh::lean_dec(v___x_4517_);
                        v___x_4657_ = leanh::lean_box(0);
                        v_isShared_4658_ = v_isSharedCheck_4662_;
                        state = 30;
                        continue;
                    }
                }
            }
            10 => {
                v___x_4530_ = leanh::lean_obj_once(
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
                    leanh::lean_ctor_set_tag(v___x_4491_, 7);
                    leanh::lean_ctor_set(v___x_4491_, 1, v___x_4531_);
                    leanh::lean_ctor_set(v___x_4491_, 0, v___x_4530_);
                    v___x_4533_ = v___x_4491_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 1, v___x_4531_);
                    v___x_4533_ = v_reuseFailAlloc_4537_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4534_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4534_, 0, v___x_4533_);
                leanh::lean_ctor_set(v___x_4534_, 1, v___y_4529_);
                v___x_3802__overap_4535_ =
                    l_Lean_throwError___redArg(v___x_4470_, v___x_4486_, v___x_4534_);
                leanh::lean_inc(v___y_4525_);
                leanh::lean_inc(v___y_4526_);
                leanh::lean_inc_ref(v___y_4524_);
                leanh::lean_inc(v___y_4528_);
                leanh::lean_inc_ref(v___y_4527_);
                v___x_4536_ = leanh::lean_apply_7(
                    v___x_3802__overap_4535_,
                    v___y_4527_,
                    v___y_4528_,
                    v___y_4524_,
                    v___y_4526_,
                    v___y_4523_,
                    v___y_4525_,
                    leanh::lean_box(0),
                );
                return v___x_4536_;
            }
            12 => {
                if v___y_4548_ == 0 {
                    if leanh::lean_obj_tag(v___y_4539_) == 0 {
                        leanh::lean_dec_ref_known(v___y_4539_, 2);
                        leanh::lean_dec_ref(v___y_4541_);
                        leanh::lean_dec(v_a_4521_);
                        leanh::lean_del_object(v___x_4491_);
                        leanh::lean_dec(v_expectedType_x3f_4489_);
                        leanh::lean_dec_ref_known(v___x_4486_, 3);
                        leanh::lean_dec_ref(v___x_4470_);
                        return v___y_4542_;
                    } else {
                        v_id_4549_ = leanh::lean_ctor_get(v___y_4539_, 0);
                        v_isSharedCheck_4563_ =
                            (!leanh::lean_is_exclusive(v___y_4539_)) as u8;
                        if v_isSharedCheck_4563_ == 0 {
                            v_unused_4564_ = leanh::lean_ctor_get(v___y_4539_, 1);
                            leanh::lean_dec(v_unused_4564_);
                            v___x_4551_ = v___y_4539_;
                            v_isShared_4552_ = v_isSharedCheck_4563_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_id_4549_);
                            leanh::lean_dec(v___y_4539_);
                            v___x_4551_ = leanh::lean_box(0);
                            v_isShared_4552_ = v_isSharedCheck_4563_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4541_);
                    leanh::lean_dec_ref(v___y_4539_);
                    leanh::lean_dec(v_a_4521_);
                    leanh::lean_del_object(v___x_4491_);
                    leanh::lean_dec(v_expectedType_x3f_4489_);
                    leanh::lean_dec_ref_known(v___x_4486_, 3);
                    leanh::lean_dec_ref(v___x_4470_);
                    return v___y_4542_;
                }
            }
            13 => {
                v___x_4553_ = l_Lean_instBEqInternalExceptionId_beq(v___y_4543_, v_id_4549_);
                leanh::lean_dec(v_id_4549_);
                if v___x_4553_ == 0 {
                    leanh::lean_del_object(v___x_4551_);
                    leanh::lean_dec_ref(v___y_4541_);
                    leanh::lean_dec(v_a_4521_);
                    leanh::lean_del_object(v___x_4491_);
                    leanh::lean_dec(v_expectedType_x3f_4489_);
                    leanh::lean_dec_ref_known(v___x_4486_, 3);
                    leanh::lean_dec_ref(v___x_4470_);
                    return v___y_4542_;
                } else {
                    leanh::lean_dec_ref(v___y_4542_);
                    if leanh::lean_obj_tag(v_expectedType_x3f_4489_) == 1 {
                        v_val_4554_ = leanh::lean_ctor_get(v_expectedType_x3f_4489_, 0);
                        leanh::lean_inc(v_val_4554_);
                        leanh::lean_dec_ref_known(v_expectedType_x3f_4489_, 1);
                        v___x_4555_ = leanh::lean_obj_once(
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
                            leanh::lean_ctor_set_tag(v___x_4551_, 7);
                            leanh::lean_ctor_set(v___x_4551_, 1, v___x_4556_);
                            leanh::lean_ctor_set(v___x_4551_, 0, v___x_4555_);
                            v___x_4558_ = v___x_4551_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_4561_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 0, v___x_4555_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 1, v___x_4556_);
                            v___x_4558_ = v_reuseFailAlloc_4561_;
                            state = 14;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4551_);
                        leanh::lean_dec(v_expectedType_x3f_4489_);
                        v___x_4562_ = leanh::lean_obj_once(
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
                v___x_4559_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                );
                v___x_4560_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4560_, 0, v___x_4558_);
                leanh::lean_ctor_set(v___x_4560_, 1, v___x_4559_);
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
                leanh::lean_inc(v___y_4571_);
                leanh::lean_inc_ref(v___y_4570_);
                leanh::lean_inc(v___y_4569_);
                leanh::lean_inc_ref(v___y_4568_);
                leanh::lean_inc(v_a_4521_);
                v___x_4572_ = leanh::lean_apply_6(
                    v_evalExpr_4488_,
                    v_a_4521_,
                    v___y_4568_,
                    v___y_4569_,
                    v___y_4570_,
                    v___y_4571_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4572_) == 0 {
                    leanh::lean_dec_ref(v___y_4570_);
                    leanh::lean_dec(v_a_4521_);
                    leanh::lean_del_object(v___x_4491_);
                    leanh::lean_dec(v_expectedType_x3f_4489_);
                    leanh::lean_dec_ref_known(v___x_4486_, 3);
                    leanh::lean_dec_ref(v___x_4470_);
                    return v___x_4572_;
                } else {
                    v_a_4573_ = leanh::lean_ctor_get(v___x_4572_, 0);
                    leanh::lean_inc(v_a_4573_);
                    v___x_4574_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_4575_ = l_Lean_Exception_isInterrupt(v_a_4573_);
                    if v___x_4575_ == 0 {
                        leanh::lean_inc(v_a_4573_);
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
                leanh::lean_inc(v_a_4521_);
                v___x_4584_ = l_Lean_Meta_getMVars(
                    v_a_4521_,
                    v___y_4580_,
                    v___y_4581_,
                    v___y_4582_,
                    v___y_4583_,
                );
                if leanh::lean_obj_tag(v___x_4584_) == 0 {
                    v_a_4585_ = leanh::lean_ctor_get(v___x_4584_, 0);
                    leanh::lean_inc(v_a_4585_);
                    leanh::lean_dec_ref_known(v___x_4584_, 1);
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
                    leanh::lean_dec(v_a_4585_);
                    if leanh::lean_obj_tag(v___x_4586_) == 0 {
                        v_a_4587_ = leanh::lean_ctor_get(v___x_4586_, 0);
                        leanh::lean_inc(v_a_4587_);
                        leanh::lean_dec_ref_known(v___x_4586_, 1);
                        v___x_4588_ = (leanh::lean_unbox(v_a_4587_) as u8);
                        leanh::lean_dec(v_a_4587_);
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
                            leanh::lean_inc(v___y_4583_);
                            leanh::lean_inc_ref(v___y_4582_);
                            leanh::lean_inc(v___y_4581_);
                            leanh::lean_inc_ref(v___y_4580_);
                            leanh::lean_inc(v___y_4579_);
                            leanh::lean_inc_ref(v___y_4578_);
                            v___x_4590_ = leanh::lean_apply_7(
                                v___x_4071__overap_4589_,
                                v___y_4578_,
                                v___y_4579_,
                                v___y_4580_,
                                v___y_4581_,
                                v___y_4582_,
                                v___y_4583_,
                                leanh::lean_box(0),
                            );
                            if leanh::lean_obj_tag(v___x_4590_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4590_, 1);
                                v___y_4566_ = v___y_4578_;
                                v___y_4567_ = v___y_4579_;
                                v___y_4568_ = v___y_4580_;
                                v___y_4569_ = v___y_4581_;
                                v___y_4570_ = v___y_4582_;
                                v___y_4571_ = v___y_4583_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v___y_4582_);
                                leanh::lean_dec(v_a_4521_);
                                leanh::lean_del_object(v___x_4491_);
                                leanh::lean_dec(v_expectedType_x3f_4489_);
                                leanh::lean_dec_ref(v_evalExpr_4488_);
                                leanh::lean_dec_ref_known(v___x_4486_, 3);
                                leanh::lean_dec_ref(v___x_4470_);
                                v_a_4591_ = leanh::lean_ctor_get(v___x_4590_, 0);
                                v_isSharedCheck_4598_ =
                                    (!leanh::lean_is_exclusive(v___x_4590_)) as u8;
                                if v_isSharedCheck_4598_ == 0 {
                                    v___x_4593_ = v___x_4590_;
                                    v_isShared_4594_ = v_isSharedCheck_4598_;
                                    state = 17;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4591_);
                                    leanh::lean_dec(v___x_4590_);
                                    v___x_4593_ = leanh::lean_box(0);
                                    v_isShared_4594_ = v_isSharedCheck_4598_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_4582_);
                        leanh::lean_dec(v_a_4521_);
                        leanh::lean_del_object(v___x_4491_);
                        leanh::lean_dec(v_expectedType_x3f_4489_);
                        leanh::lean_dec_ref(v_evalExpr_4488_);
                        leanh::lean_dec_ref_known(v___x_4486_, 3);
                        leanh::lean_dec_ref(v___x_4470_);
                        v_a_4599_ = leanh::lean_ctor_get(v___x_4586_, 0);
                        v_isSharedCheck_4606_ =
                            (!leanh::lean_is_exclusive(v___x_4586_)) as u8;
                        if v_isSharedCheck_4606_ == 0 {
                            v___x_4601_ = v___x_4586_;
                            v_isShared_4602_ = v_isSharedCheck_4606_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4599_);
                            leanh::lean_dec(v___x_4586_);
                            v___x_4601_ = leanh::lean_box(0);
                            v_isShared_4602_ = v_isSharedCheck_4606_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4582_);
                    leanh::lean_dec(v_a_4521_);
                    leanh::lean_del_object(v___x_4491_);
                    leanh::lean_dec(v_expectedType_x3f_4489_);
                    leanh::lean_dec_ref(v_evalExpr_4488_);
                    leanh::lean_dec_ref_known(v___x_4486_, 3);
                    leanh::lean_dec_ref(v___x_4470_);
                    v_a_4607_ = leanh::lean_ctor_get(v___x_4584_, 0);
                    v_isSharedCheck_4614_ = (!leanh::lean_is_exclusive(v___x_4584_)) as u8;
                    if v_isSharedCheck_4614_ == 0 {
                        v___x_4609_ = v___x_4584_;
                        v_isShared_4610_ = v_isSharedCheck_4614_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4607_);
                        leanh::lean_dec(v___x_4584_);
                        v___x_4609_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4591_);
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
                    v_reuseFailAlloc_4605_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
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
                    v_reuseFailAlloc_4613_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
                    v___x_4612_ = v_reuseFailAlloc_4613_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4612_;
            }
            23 => {
                v___x_4622_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32,
                );
                leanh::lean_inc(v_a_4521_);
                v___x_4623_ = l_Lean_indentExpr(v_a_4521_);
                v___x_4624_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4624_, 0, v___x_4622_);
                leanh::lean_ctor_set(v___x_4624_, 1, v___x_4623_);
                leanh::lean_inc_ref(v___x_4486_);
                leanh::lean_inc_ref(v___x_4470_);
                v___x_3938__overap_4625_ =
                    l_Lean_throwError___redArg(v___x_4470_, v___x_4486_, v___x_4624_);
                leanh::lean_inc(v___y_4621_);
                leanh::lean_inc_ref(v___y_4620_);
                leanh::lean_inc(v___y_4619_);
                leanh::lean_inc_ref(v___y_4618_);
                leanh::lean_inc(v___y_4617_);
                leanh::lean_inc_ref(v___y_4616_);
                v___x_4626_ = leanh::lean_apply_7(
                    v___x_3938__overap_4625_,
                    v___y_4616_,
                    v___y_4617_,
                    v___y_4618_,
                    v___y_4619_,
                    v___y_4620_,
                    v___y_4621_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4626_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4626_, 1);
                    v___y_4578_ = v___y_4616_;
                    v___y_4579_ = v___y_4617_;
                    v___y_4580_ = v___y_4618_;
                    v___y_4581_ = v___y_4619_;
                    v___y_4582_ = v___y_4620_;
                    v___y_4583_ = v___y_4621_;
                    state = 16;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4620_);
                    leanh::lean_dec(v_a_4521_);
                    leanh::lean_del_object(v___x_4491_);
                    leanh::lean_dec(v_expectedType_x3f_4489_);
                    leanh::lean_dec_ref(v_evalExpr_4488_);
                    leanh::lean_dec_ref_known(v___x_4486_, 3);
                    leanh::lean_dec_ref(v___x_4470_);
                    v_a_4627_ = leanh::lean_ctor_get(v___x_4626_, 0);
                    v_isSharedCheck_4634_ = (!leanh::lean_is_exclusive(v___x_4626_)) as u8;
                    if v_isSharedCheck_4634_ == 0 {
                        v___x_4629_ = v___x_4626_;
                        v_isShared_4630_ = v_isSharedCheck_4634_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4627_);
                        leanh::lean_dec(v___x_4626_);
                        v___x_4629_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4633_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4627_);
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
                    v_reuseFailAlloc_4645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
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
                    v_reuseFailAlloc_4653_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
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
                    v_reuseFailAlloc_4661_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
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
    mut v_inst_4676_: *mut leanh::LeanObject,
    mut v_stx_4677_: *mut leanh::LeanObject,
    mut v_a_4678_: *mut leanh::LeanObject,
    mut v_a_4679_: *mut leanh::LeanObject,
    mut v_a_4680_: *mut leanh::LeanObject,
    mut v_a_4681_: *mut leanh::LeanObject,
    mut v_a_4682_: *mut leanh::LeanObject,
    mut v_a_4683_: *mut leanh::LeanObject,
    mut v_a_4684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4683_);
    leanh::lean_dec_ref(v_a_4682_);
    leanh::lean_dec(v_a_4681_);
    leanh::lean_dec_ref(v_a_4680_);
    leanh::lean_dec(v_a_4679_);
    leanh::lean_dec_ref(v_a_4678_);
    return v_res_4685_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab(
    mut v_00_u03b1_4686_: *mut leanh::LeanObject,
    mut v_inst_4687_: *mut leanh::LeanObject,
    mut v_stx_4688_: *mut leanh::LeanObject,
    mut v_a_4689_: *mut leanh::LeanObject,
    mut v_a_4690_: *mut leanh::LeanObject,
    mut v_a_4691_: *mut leanh::LeanObject,
    mut v_a_4692_: *mut leanh::LeanObject,
    mut v_a_4693_: *mut leanh::LeanObject,
    mut v_a_4694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4697_: *mut leanh::LeanObject,
    mut v_inst_4698_: *mut leanh::LeanObject,
    mut v_stx_4699_: *mut leanh::LeanObject,
    mut v_a_4700_: *mut leanh::LeanObject,
    mut v_a_4701_: *mut leanh::LeanObject,
    mut v_a_4702_: *mut leanh::LeanObject,
    mut v_a_4703_: *mut leanh::LeanObject,
    mut v_a_4704_: *mut leanh::LeanObject,
    mut v_a_4705_: *mut leanh::LeanObject,
    mut v_a_4706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4705_);
    leanh::lean_dec_ref(v_a_4704_);
    leanh::lean_dec(v_a_4703_);
    leanh::lean_dec_ref(v_a_4702_);
    leanh::lean_dec(v_a_4701_);
    leanh::lean_dec_ref(v_a_4700_);
    return v_res_4707_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(
    mut v_inst_4708_: *mut leanh::LeanObject,
    mut v_inst_4709_: *mut leanh::LeanObject,
    mut v_stx_4710_: *mut leanh::LeanObject,
    mut v_a_4711_: *mut leanh::LeanObject,
    mut v_a_4712_: *mut leanh::LeanObject,
    mut v_a_4713_: *mut leanh::LeanObject,
    mut v_a_4714_: *mut leanh::LeanObject,
    mut v_a_4715_: *mut leanh::LeanObject,
    mut v_a_4716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_evalTerm_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4731_: u8 = 0;
    let mut v_cancelTk_x3f_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4733_: u8 = 0;
    let mut v_inheritedTraceOptions_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4741_: u8 = 0;
    let mut v_fst_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4746_: u8 = 0;
    let mut v_a_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4750_: u8 = 0;
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4755_: u8 = 0;
    let mut v_id_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: u8 = 0;
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: u8 = 0;
    let mut v___x_4760_: u8 = 0;
    let mut v_reuseFailAlloc_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalTerm_4718_ = leanh::lean_ctor_get(v_inst_4708_, 0);
                leanh::lean_inc_ref(v_evalTerm_4718_);
                leanh::lean_dec_ref(v_inst_4708_);
                v_fileName_4719_ = leanh::lean_ctor_get(v_a_4715_, 0);
                v_fileMap_4720_ = leanh::lean_ctor_get(v_a_4715_, 1);
                v_options_4721_ = leanh::lean_ctor_get(v_a_4715_, 2);
                v_currRecDepth_4722_ = leanh::lean_ctor_get(v_a_4715_, 3);
                v_maxRecDepth_4723_ = leanh::lean_ctor_get(v_a_4715_, 4);
                v_ref_4724_ = leanh::lean_ctor_get(v_a_4715_, 5);
                v_currNamespace_4725_ = leanh::lean_ctor_get(v_a_4715_, 6);
                v_openDecls_4726_ = leanh::lean_ctor_get(v_a_4715_, 7);
                v_initHeartbeats_4727_ = leanh::lean_ctor_get(v_a_4715_, 8);
                v_maxHeartbeats_4728_ = leanh::lean_ctor_get(v_a_4715_, 9);
                v_quotContext_4729_ = leanh::lean_ctor_get(v_a_4715_, 10);
                v_currMacroScope_4730_ = leanh::lean_ctor_get(v_a_4715_, 11);
                v_diag_4731_ = leanh::lean_ctor_get_uint8(
                    v_a_4715_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4732_ = leanh::lean_ctor_get(v_a_4715_, 12);
                v_suppressElabErrors_4733_ = leanh::lean_ctor_get_uint8(
                    v_a_4715_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4734_ = leanh::lean_ctor_get(v_a_4715_, 13);
                v_ref_4735_ = l_Lean_replaceRef(v_stx_4710_, v_ref_4724_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_4734_);
                leanh::lean_inc(v_cancelTk_x3f_4732_);
                leanh::lean_inc(v_currMacroScope_4730_);
                leanh::lean_inc(v_quotContext_4729_);
                leanh::lean_inc(v_maxHeartbeats_4728_);
                leanh::lean_inc(v_initHeartbeats_4727_);
                leanh::lean_inc(v_openDecls_4726_);
                leanh::lean_inc(v_currNamespace_4725_);
                leanh::lean_inc(v_maxRecDepth_4723_);
                leanh::lean_inc(v_currRecDepth_4722_);
                leanh::lean_inc_ref(v_options_4721_);
                leanh::lean_inc_ref(v_fileMap_4720_);
                leanh::lean_inc_ref(v_fileName_4719_);
                v___x_4736_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_4736_, 0, v_fileName_4719_);
                leanh::lean_ctor_set(v___x_4736_, 1, v_fileMap_4720_);
                leanh::lean_ctor_set(v___x_4736_, 2, v_options_4721_);
                leanh::lean_ctor_set(v___x_4736_, 3, v_currRecDepth_4722_);
                leanh::lean_ctor_set(v___x_4736_, 4, v_maxRecDepth_4723_);
                leanh::lean_ctor_set(v___x_4736_, 5, v_ref_4735_);
                leanh::lean_ctor_set(v___x_4736_, 6, v_currNamespace_4725_);
                leanh::lean_ctor_set(v___x_4736_, 7, v_openDecls_4726_);
                leanh::lean_ctor_set(v___x_4736_, 8, v_initHeartbeats_4727_);
                leanh::lean_ctor_set(v___x_4736_, 9, v_maxHeartbeats_4728_);
                leanh::lean_ctor_set(v___x_4736_, 10, v_quotContext_4729_);
                leanh::lean_ctor_set(v___x_4736_, 11, v_currMacroScope_4730_);
                leanh::lean_ctor_set(v___x_4736_, 12, v_cancelTk_x3f_4732_);
                leanh::lean_ctor_set(v___x_4736_, 13, v_inheritedTraceOptions_4734_);
                leanh::lean_ctor_set_uint8(
                    v___x_4736_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_4731_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4736_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4733_,
                );
                leanh::lean_inc(v_a_4716_);
                leanh::lean_inc_ref(v___x_4736_);
                leanh::lean_inc(v_a_4714_);
                leanh::lean_inc_ref(v_a_4713_);
                leanh::lean_inc(v_a_4712_);
                leanh::lean_inc_ref(v_a_4711_);
                leanh::lean_inc(v_stx_4710_);
                v___x_4737_ = leanh::lean_apply_8(
                    v_evalTerm_4718_,
                    v_stx_4710_,
                    v_a_4711_,
                    v_a_4712_,
                    v_a_4713_,
                    v_a_4714_,
                    v___x_4736_,
                    v_a_4716_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4737_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4736_, 14);
                    leanh::lean_dec(v_stx_4710_);
                    leanh::lean_dec_ref(v_inst_4709_);
                    v_a_4738_ = leanh::lean_ctor_get(v___x_4737_, 0);
                    v_isSharedCheck_4746_ = (!leanh::lean_is_exclusive(v___x_4737_)) as u8;
                    if v_isSharedCheck_4746_ == 0 {
                        v___x_4740_ = v___x_4737_;
                        v_isShared_4741_ = v_isSharedCheck_4746_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4738_);
                        leanh::lean_dec(v___x_4737_);
                        v___x_4740_ = leanh::lean_box(0);
                        v_isShared_4741_ = v_isSharedCheck_4746_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4747_ = leanh::lean_ctor_get(v___x_4737_, 0);
                    v_isSharedCheck_4762_ = (!leanh::lean_is_exclusive(v___x_4737_)) as u8;
                    if v_isSharedCheck_4762_ == 0 {
                        v___x_4749_ = v___x_4737_;
                        v_isShared_4750_ = v_isSharedCheck_4762_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4747_);
                        leanh::lean_dec(v___x_4737_);
                        v___x_4749_ = leanh::lean_box(0);
                        v_isShared_4750_ = v_isSharedCheck_4762_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4742_ = leanh::lean_ctor_get(v_a_4738_, 0);
                leanh::lean_inc(v_fst_4742_);
                leanh::lean_dec(v_a_4738_);
                if v_isShared_4741_ == 0 {
                    leanh::lean_ctor_set(v___x_4740_, 0, v_fst_4742_);
                    v___x_4744_ = v___x_4740_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4745_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_fst_4742_);
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
                leanh::lean_inc(v_a_4747_);
                if v_isShared_4750_ == 0 {
                    v___x_4753_ = v___x_4749_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4761_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4747_);
                    v___x_4753_ = v_reuseFailAlloc_4761_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4759_ = l_Lean_Exception_isInterrupt(v_a_4747_);
                if v___x_4759_ == 0 {
                    leanh::lean_inc(v_a_4747_);
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
                    if leanh::lean_obj_tag(v_a_4747_) == 0 {
                        leanh::lean_dec_ref_known(v_a_4747_, 2);
                        leanh::lean_dec_ref_known(v___x_4736_, 14);
                        leanh::lean_dec(v_stx_4710_);
                        leanh::lean_dec_ref(v_inst_4709_);
                        return v___x_4753_;
                    } else {
                        v_id_4756_ = leanh::lean_ctor_get(v_a_4747_, 0);
                        leanh::lean_inc(v_id_4756_);
                        leanh::lean_dec_ref_known(v_a_4747_, 2);
                        v___x_4757_ =
                            l_Lean_instBEqInternalExceptionId_beq(v___x_4751_, v_id_4756_);
                        leanh::lean_dec(v_id_4756_);
                        if v___x_4757_ == 0 {
                            leanh::lean_dec_ref_known(v___x_4736_, 14);
                            leanh::lean_dec(v_stx_4710_);
                            leanh::lean_dec_ref(v_inst_4709_);
                            return v___x_4753_;
                        } else {
                            leanh::lean_dec_ref(v___x_4753_);
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
                            leanh::lean_dec_ref_known(v___x_4736_, 14);
                            return v___x_4758_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4747_);
                    leanh::lean_dec_ref_known(v___x_4736_, 14);
                    leanh::lean_dec(v_stx_4710_);
                    leanh::lean_dec_ref(v_inst_4709_);
                    return v___x_4753_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg___boxed(
    mut v_inst_4763_: *mut leanh::LeanObject,
    mut v_inst_4764_: *mut leanh::LeanObject,
    mut v_stx_4765_: *mut leanh::LeanObject,
    mut v_a_4766_: *mut leanh::LeanObject,
    mut v_a_4767_: *mut leanh::LeanObject,
    mut v_a_4768_: *mut leanh::LeanObject,
    mut v_a_4769_: *mut leanh::LeanObject,
    mut v_a_4770_: *mut leanh::LeanObject,
    mut v_a_4771_: *mut leanh::LeanObject,
    mut v_a_4772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4771_);
    leanh::lean_dec_ref(v_a_4770_);
    leanh::lean_dec(v_a_4769_);
    leanh::lean_dec_ref(v_a_4768_);
    leanh::lean_dec(v_a_4767_);
    leanh::lean_dec_ref(v_a_4766_);
    return v_res_4773_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(
    mut v_00_u03b1_4774_: *mut leanh::LeanObject,
    mut v_inst_4775_: *mut leanh::LeanObject,
    mut v_inst_4776_: *mut leanh::LeanObject,
    mut v_stx_4777_: *mut leanh::LeanObject,
    mut v_a_4778_: *mut leanh::LeanObject,
    mut v_a_4779_: *mut leanh::LeanObject,
    mut v_a_4780_: *mut leanh::LeanObject,
    mut v_a_4781_: *mut leanh::LeanObject,
    mut v_a_4782_: *mut leanh::LeanObject,
    mut v_a_4783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4786_: *mut leanh::LeanObject,
    mut v_inst_4787_: *mut leanh::LeanObject,
    mut v_inst_4788_: *mut leanh::LeanObject,
    mut v_stx_4789_: *mut leanh::LeanObject,
    mut v_a_4790_: *mut leanh::LeanObject,
    mut v_a_4791_: *mut leanh::LeanObject,
    mut v_a_4792_: *mut leanh::LeanObject,
    mut v_a_4793_: *mut leanh::LeanObject,
    mut v_a_4794_: *mut leanh::LeanObject,
    mut v_a_4795_: *mut leanh::LeanObject,
    mut v_a_4796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4795_);
    leanh::lean_dec_ref(v_a_4794_);
    leanh::lean_dec(v_a_4793_);
    leanh::lean_dec_ref(v_a_4792_);
    leanh::lean_dec(v_a_4791_);
    leanh::lean_dec_ref(v_a_4790_);
    return v_res_4797_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
    mut v_x_4816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: u8 = 0;
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: u8 = 0;
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: u8 = 0;
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: u8 = 0;
    let mut v_t_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4817_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4;
                leanh::lean_inc(v_x_4816_);
                v___x_4818_ = l_Lean_Syntax_isOfKind(v_x_4816_, v___x_4817_);
                if v___x_4818_ == 0 {
                    return v_x_4816_;
                } else {
                    v___x_4819_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4820_ = l_Lean_Syntax_getArg(v_x_4816_, v___x_4819_);
                    v___x_4821_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6;
                    leanh::lean_inc(v___x_4820_);
                    v___x_4822_ = l_Lean_Syntax_isOfKind(v___x_4820_, v___x_4821_);
                    if v___x_4822_ == 0 {
                        leanh::lean_dec(v___x_4820_);
                        return v_x_4816_;
                    } else {
                        v___x_4823_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4824_ = l_Lean_Syntax_getArg(v___x_4820_, v___x_4823_);
                        leanh::lean_dec(v___x_4820_);
                        v___x_4825_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8;
                        leanh::lean_inc(v___x_4824_);
                        v___x_4826_ = l_Lean_Syntax_isOfKind(v___x_4824_, v___x_4825_);
                        if v___x_4826_ == 0 {
                            leanh::lean_dec(v___x_4824_);
                            return v_x_4816_;
                        } else {
                            v___x_4827_ = l_Lean_Syntax_getArg(v___x_4824_, v___x_4819_);
                            leanh::lean_dec(v___x_4824_);
                            v___x_4828_ = leanh::lean_box(0);
                            v___x_4829_ = l_Lean_Syntax_matchesIdent(v___x_4827_, v___x_4828_);
                            leanh::lean_dec(v___x_4827_);
                            if v___x_4829_ == 0 {
                                return v_x_4816_;
                            } else {
                                v_t_4830_ = l_Lean_Syntax_getArg(v_x_4816_, v___x_4823_);
                                leanh::lean_dec(v_x_4816_);
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
    mut v_expectedType_x3f_4832_: *mut leanh::LeanObject,
    mut v_f_4833_: *mut leanh::LeanObject,
    mut v_stx_4834_: *mut leanh::LeanObject,
    mut v_a_4835_: *mut leanh::LeanObject,
    mut v_a_4836_: *mut leanh::LeanObject,
    mut v_a_4837_: *mut leanh::LeanObject,
    mut v_a_4838_: *mut leanh::LeanObject,
    mut v_a_4839_: *mut leanh::LeanObject,
    mut v_a_4840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4854_: u8 = 0;
    let mut v_cancelTk_x3f_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4856_: u8 = 0;
    let mut v_inheritedTraceOptions_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4865_: u8 = 0;
    let mut v_snd_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_4869_: u8 = 0;
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: u8 = 0;
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4879_: u8 = 0;
    let mut v___x_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4883_: u8 = 0;
    let mut v_unused_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4888_: u8 = 0;
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4892_: u8 = 0;
    let mut v_isSharedCheck_4893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4842_ = leanh::lean_ctor_get(v_a_4839_, 0);
                v_fileMap_4843_ = leanh::lean_ctor_get(v_a_4839_, 1);
                v_options_4844_ = leanh::lean_ctor_get(v_a_4839_, 2);
                v_currRecDepth_4845_ = leanh::lean_ctor_get(v_a_4839_, 3);
                v_maxRecDepth_4846_ = leanh::lean_ctor_get(v_a_4839_, 4);
                v_ref_4847_ = leanh::lean_ctor_get(v_a_4839_, 5);
                v_currNamespace_4848_ = leanh::lean_ctor_get(v_a_4839_, 6);
                v_openDecls_4849_ = leanh::lean_ctor_get(v_a_4839_, 7);
                v_initHeartbeats_4850_ = leanh::lean_ctor_get(v_a_4839_, 8);
                v_maxHeartbeats_4851_ = leanh::lean_ctor_get(v_a_4839_, 9);
                v_quotContext_4852_ = leanh::lean_ctor_get(v_a_4839_, 10);
                v_currMacroScope_4853_ = leanh::lean_ctor_get(v_a_4839_, 11);
                v_diag_4854_ = leanh::lean_ctor_get_uint8(
                    v_a_4839_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4855_ = leanh::lean_ctor_get(v_a_4839_, 12);
                v_suppressElabErrors_4856_ = leanh::lean_ctor_get_uint8(
                    v_a_4839_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4857_ = leanh::lean_ctor_get(v_a_4839_, 13);
                leanh::lean_inc(v_stx_4834_);
                v___x_4858_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_4834_,
                    );
                v_ref_4859_ = l_Lean_replaceRef(v_stx_4834_, v_ref_4847_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_4857_);
                leanh::lean_inc(v_cancelTk_x3f_4855_);
                leanh::lean_inc(v_currMacroScope_4853_);
                leanh::lean_inc(v_quotContext_4852_);
                leanh::lean_inc(v_maxHeartbeats_4851_);
                leanh::lean_inc(v_initHeartbeats_4850_);
                leanh::lean_inc(v_openDecls_4849_);
                leanh::lean_inc(v_currNamespace_4848_);
                leanh::lean_inc(v_maxRecDepth_4846_);
                leanh::lean_inc(v_currRecDepth_4845_);
                leanh::lean_inc_ref(v_options_4844_);
                leanh::lean_inc_ref(v_fileMap_4843_);
                leanh::lean_inc_ref(v_fileName_4842_);
                v___x_4860_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_4860_, 0, v_fileName_4842_);
                leanh::lean_ctor_set(v___x_4860_, 1, v_fileMap_4843_);
                leanh::lean_ctor_set(v___x_4860_, 2, v_options_4844_);
                leanh::lean_ctor_set(v___x_4860_, 3, v_currRecDepth_4845_);
                leanh::lean_ctor_set(v___x_4860_, 4, v_maxRecDepth_4846_);
                leanh::lean_ctor_set(v___x_4860_, 5, v_ref_4859_);
                leanh::lean_ctor_set(v___x_4860_, 6, v_currNamespace_4848_);
                leanh::lean_ctor_set(v___x_4860_, 7, v_openDecls_4849_);
                leanh::lean_ctor_set(v___x_4860_, 8, v_initHeartbeats_4850_);
                leanh::lean_ctor_set(v___x_4860_, 9, v_maxHeartbeats_4851_);
                leanh::lean_ctor_set(v___x_4860_, 10, v_quotContext_4852_);
                leanh::lean_ctor_set(v___x_4860_, 11, v_currMacroScope_4853_);
                leanh::lean_ctor_set(v___x_4860_, 12, v_cancelTk_x3f_4855_);
                leanh::lean_ctor_set(v___x_4860_, 13, v_inheritedTraceOptions_4857_);
                leanh::lean_ctor_set_uint8(
                    v___x_4860_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_4854_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4860_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4856_,
                );
                leanh::lean_inc(v_a_4840_);
                leanh::lean_inc(v_a_4838_);
                leanh::lean_inc_ref(v_a_4837_);
                leanh::lean_inc(v_a_4836_);
                leanh::lean_inc_ref(v_a_4835_);
                v___x_4861_ = leanh::lean_apply_8(
                    v_f_4833_,
                    v___x_4858_,
                    v_a_4835_,
                    v_a_4836_,
                    v_a_4837_,
                    v_a_4838_,
                    v___x_4860_,
                    v_a_4840_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4861_) == 0 {
                    v_a_4862_ = leanh::lean_ctor_get(v___x_4861_, 0);
                    v_isSharedCheck_4893_ = (!leanh::lean_is_exclusive(v___x_4861_)) as u8;
                    if v_isSharedCheck_4893_ == 0 {
                        v___x_4864_ = v___x_4861_;
                        v_isShared_4865_ = v_isSharedCheck_4893_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4862_);
                        leanh::lean_dec(v___x_4861_);
                        v___x_4864_ = leanh::lean_box(0);
                        v_isShared_4865_ = v_isSharedCheck_4893_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_stx_4834_);
                    leanh::lean_dec(v_expectedType_x3f_4832_);
                    return v___x_4861_;
                }
            }
            1 => {
                v_snd_4866_ = leanh::lean_ctor_get(v_a_4862_, 1);
                v___x_4867_ = lean_st_ref_get(v_a_4840_);
                v_infoState_4868_ = leanh::lean_ctor_get(v___x_4867_, 7);
                leanh::lean_inc_ref(v_infoState_4868_);
                leanh::lean_dec(v___x_4867_);
                v_enabled_4869_ = leanh::lean_ctor_get_uint8(
                    v_infoState_4868_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_4868_);
                if v_enabled_4869_ == 0 {
                    leanh::lean_dec(v_stx_4834_);
                    leanh::lean_dec(v_expectedType_x3f_4832_);
                    if v_isShared_4865_ == 0 {
                        v___x_4871_ = v___x_4864_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4872_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4862_);
                        v___x_4871_ = v_reuseFailAlloc_4872_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4864_);
                    v___x_4873_ = leanh::lean_box(0);
                    v___x_4874_ = leanh::lean_box(0);
                    v___x_4875_ = 0;
                    leanh::lean_inc(v_snd_4866_);
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
                    if leanh::lean_obj_tag(v___x_4876_) == 0 {
                        v_isSharedCheck_4883_ =
                            (!leanh::lean_is_exclusive(v___x_4876_)) as u8;
                        if v_isSharedCheck_4883_ == 0 {
                            v_unused_4884_ = leanh::lean_ctor_get(v___x_4876_, 0);
                            leanh::lean_dec(v_unused_4884_);
                            v___x_4878_ = v___x_4876_;
                            v_isShared_4879_ = v_isSharedCheck_4883_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4876_);
                            v___x_4878_ = leanh::lean_box(0);
                            v_isShared_4879_ = v_isSharedCheck_4883_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4862_);
                        v_a_4885_ = leanh::lean_ctor_get(v___x_4876_, 0);
                        v_isSharedCheck_4892_ =
                            (!leanh::lean_is_exclusive(v___x_4876_)) as u8;
                        if v_isSharedCheck_4892_ == 0 {
                            v___x_4887_ = v___x_4876_;
                            v_isShared_4888_ = v_isSharedCheck_4892_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4885_);
                            leanh::lean_dec(v___x_4876_);
                            v___x_4887_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_4878_, 0, v_a_4862_);
                    v___x_4881_ = v___x_4878_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4882_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_a_4862_);
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
                    v_reuseFailAlloc_4891_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
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
    mut v_expectedType_x3f_4894_: *mut leanh::LeanObject,
    mut v_f_4895_: *mut leanh::LeanObject,
    mut v_stx_4896_: *mut leanh::LeanObject,
    mut v_a_4897_: *mut leanh::LeanObject,
    mut v_a_4898_: *mut leanh::LeanObject,
    mut v_a_4899_: *mut leanh::LeanObject,
    mut v_a_4900_: *mut leanh::LeanObject,
    mut v_a_4901_: *mut leanh::LeanObject,
    mut v_a_4902_: *mut leanh::LeanObject,
    mut v_a_4903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4902_);
    leanh::lean_dec_ref(v_a_4901_);
    leanh::lean_dec(v_a_4900_);
    leanh::lean_dec_ref(v_a_4899_);
    leanh::lean_dec(v_a_4898_);
    leanh::lean_dec_ref(v_a_4897_);
    return v_res_4904_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(
    mut v_00_u03b1_4905_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_4906_: *mut leanh::LeanObject,
    mut v_f_4907_: *mut leanh::LeanObject,
    mut v_stx_4908_: *mut leanh::LeanObject,
    mut v_a_4909_: *mut leanh::LeanObject,
    mut v_a_4910_: *mut leanh::LeanObject,
    mut v_a_4911_: *mut leanh::LeanObject,
    mut v_a_4912_: *mut leanh::LeanObject,
    mut v_a_4913_: *mut leanh::LeanObject,
    mut v_a_4914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4928_: u8 = 0;
    let mut v_cancelTk_x3f_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4930_: u8 = 0;
    let mut v_inheritedTraceOptions_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4939_: u8 = 0;
    let mut v_snd_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_4943_: u8 = 0;
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: u8 = 0;
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4953_: u8 = 0;
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4957_: u8 = 0;
    let mut v_unused_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4962_: u8 = 0;
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4966_: u8 = 0;
    let mut v_isSharedCheck_4967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4916_ = leanh::lean_ctor_get(v_a_4913_, 0);
                v_fileMap_4917_ = leanh::lean_ctor_get(v_a_4913_, 1);
                v_options_4918_ = leanh::lean_ctor_get(v_a_4913_, 2);
                v_currRecDepth_4919_ = leanh::lean_ctor_get(v_a_4913_, 3);
                v_maxRecDepth_4920_ = leanh::lean_ctor_get(v_a_4913_, 4);
                v_ref_4921_ = leanh::lean_ctor_get(v_a_4913_, 5);
                v_currNamespace_4922_ = leanh::lean_ctor_get(v_a_4913_, 6);
                v_openDecls_4923_ = leanh::lean_ctor_get(v_a_4913_, 7);
                v_initHeartbeats_4924_ = leanh::lean_ctor_get(v_a_4913_, 8);
                v_maxHeartbeats_4925_ = leanh::lean_ctor_get(v_a_4913_, 9);
                v_quotContext_4926_ = leanh::lean_ctor_get(v_a_4913_, 10);
                v_currMacroScope_4927_ = leanh::lean_ctor_get(v_a_4913_, 11);
                v_diag_4928_ = leanh::lean_ctor_get_uint8(
                    v_a_4913_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4929_ = leanh::lean_ctor_get(v_a_4913_, 12);
                v_suppressElabErrors_4930_ = leanh::lean_ctor_get_uint8(
                    v_a_4913_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4931_ = leanh::lean_ctor_get(v_a_4913_, 13);
                leanh::lean_inc(v_stx_4908_);
                v___x_4932_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_4908_,
                    );
                v_ref_4933_ = l_Lean_replaceRef(v_stx_4908_, v_ref_4921_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_4931_);
                leanh::lean_inc(v_cancelTk_x3f_4929_);
                leanh::lean_inc(v_currMacroScope_4927_);
                leanh::lean_inc(v_quotContext_4926_);
                leanh::lean_inc(v_maxHeartbeats_4925_);
                leanh::lean_inc(v_initHeartbeats_4924_);
                leanh::lean_inc(v_openDecls_4923_);
                leanh::lean_inc(v_currNamespace_4922_);
                leanh::lean_inc(v_maxRecDepth_4920_);
                leanh::lean_inc(v_currRecDepth_4919_);
                leanh::lean_inc_ref(v_options_4918_);
                leanh::lean_inc_ref(v_fileMap_4917_);
                leanh::lean_inc_ref(v_fileName_4916_);
                v___x_4934_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_4934_, 0, v_fileName_4916_);
                leanh::lean_ctor_set(v___x_4934_, 1, v_fileMap_4917_);
                leanh::lean_ctor_set(v___x_4934_, 2, v_options_4918_);
                leanh::lean_ctor_set(v___x_4934_, 3, v_currRecDepth_4919_);
                leanh::lean_ctor_set(v___x_4934_, 4, v_maxRecDepth_4920_);
                leanh::lean_ctor_set(v___x_4934_, 5, v_ref_4933_);
                leanh::lean_ctor_set(v___x_4934_, 6, v_currNamespace_4922_);
                leanh::lean_ctor_set(v___x_4934_, 7, v_openDecls_4923_);
                leanh::lean_ctor_set(v___x_4934_, 8, v_initHeartbeats_4924_);
                leanh::lean_ctor_set(v___x_4934_, 9, v_maxHeartbeats_4925_);
                leanh::lean_ctor_set(v___x_4934_, 10, v_quotContext_4926_);
                leanh::lean_ctor_set(v___x_4934_, 11, v_currMacroScope_4927_);
                leanh::lean_ctor_set(v___x_4934_, 12, v_cancelTk_x3f_4929_);
                leanh::lean_ctor_set(v___x_4934_, 13, v_inheritedTraceOptions_4931_);
                leanh::lean_ctor_set_uint8(
                    v___x_4934_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_4928_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4934_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4930_,
                );
                leanh::lean_inc(v_a_4914_);
                leanh::lean_inc(v_a_4912_);
                leanh::lean_inc_ref(v_a_4911_);
                leanh::lean_inc(v_a_4910_);
                leanh::lean_inc_ref(v_a_4909_);
                v___x_4935_ = leanh::lean_apply_8(
                    v_f_4907_,
                    v___x_4932_,
                    v_a_4909_,
                    v_a_4910_,
                    v_a_4911_,
                    v_a_4912_,
                    v___x_4934_,
                    v_a_4914_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4935_) == 0 {
                    v_a_4936_ = leanh::lean_ctor_get(v___x_4935_, 0);
                    v_isSharedCheck_4967_ = (!leanh::lean_is_exclusive(v___x_4935_)) as u8;
                    if v_isSharedCheck_4967_ == 0 {
                        v___x_4938_ = v___x_4935_;
                        v_isShared_4939_ = v_isSharedCheck_4967_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4936_);
                        leanh::lean_dec(v___x_4935_);
                        v___x_4938_ = leanh::lean_box(0);
                        v_isShared_4939_ = v_isSharedCheck_4967_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_stx_4908_);
                    leanh::lean_dec(v_expectedType_x3f_4906_);
                    return v___x_4935_;
                }
            }
            1 => {
                v_snd_4940_ = leanh::lean_ctor_get(v_a_4936_, 1);
                v___x_4941_ = lean_st_ref_get(v_a_4914_);
                v_infoState_4942_ = leanh::lean_ctor_get(v___x_4941_, 7);
                leanh::lean_inc_ref(v_infoState_4942_);
                leanh::lean_dec(v___x_4941_);
                v_enabled_4943_ = leanh::lean_ctor_get_uint8(
                    v_infoState_4942_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_4942_);
                if v_enabled_4943_ == 0 {
                    leanh::lean_dec(v_stx_4908_);
                    leanh::lean_dec(v_expectedType_x3f_4906_);
                    if v_isShared_4939_ == 0 {
                        v___x_4945_ = v___x_4938_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4946_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4936_);
                        v___x_4945_ = v_reuseFailAlloc_4946_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4938_);
                    v___x_4947_ = leanh::lean_box(0);
                    v___x_4948_ = leanh::lean_box(0);
                    v___x_4949_ = 0;
                    leanh::lean_inc(v_snd_4940_);
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
                    if leanh::lean_obj_tag(v___x_4950_) == 0 {
                        v_isSharedCheck_4957_ =
                            (!leanh::lean_is_exclusive(v___x_4950_)) as u8;
                        if v_isSharedCheck_4957_ == 0 {
                            v_unused_4958_ = leanh::lean_ctor_get(v___x_4950_, 0);
                            leanh::lean_dec(v_unused_4958_);
                            v___x_4952_ = v___x_4950_;
                            v_isShared_4953_ = v_isSharedCheck_4957_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4950_);
                            v___x_4952_ = leanh::lean_box(0);
                            v_isShared_4953_ = v_isSharedCheck_4957_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4936_);
                        v_a_4959_ = leanh::lean_ctor_get(v___x_4950_, 0);
                        v_isSharedCheck_4966_ =
                            (!leanh::lean_is_exclusive(v___x_4950_)) as u8;
                        if v_isSharedCheck_4966_ == 0 {
                            v___x_4961_ = v___x_4950_;
                            v_isShared_4962_ = v_isSharedCheck_4966_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4959_);
                            leanh::lean_dec(v___x_4950_);
                            v___x_4961_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_4952_, 0, v_a_4936_);
                    v___x_4955_ = v___x_4952_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4956_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4936_);
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
                    v_reuseFailAlloc_4965_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
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
    mut v_00_u03b1_4968_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_4969_: *mut leanh::LeanObject,
    mut v_f_4970_: *mut leanh::LeanObject,
    mut v_stx_4971_: *mut leanh::LeanObject,
    mut v_a_4972_: *mut leanh::LeanObject,
    mut v_a_4973_: *mut leanh::LeanObject,
    mut v_a_4974_: *mut leanh::LeanObject,
    mut v_a_4975_: *mut leanh::LeanObject,
    mut v_a_4976_: *mut leanh::LeanObject,
    mut v_a_4977_: *mut leanh::LeanObject,
    mut v_a_4978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4977_);
    leanh::lean_dec_ref(v_a_4976_);
    leanh::lean_dec(v_a_4975_);
    leanh::lean_dec_ref(v_a_4974_);
    leanh::lean_dec(v_a_4973_);
    leanh::lean_dec_ref(v_a_4972_);
    return v_res_4979_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(
    mut v_inst_4980_: *mut leanh::LeanObject,
    mut v_f_4981_: *mut leanh::LeanObject,
    mut v_stx_4982_: *mut leanh::LeanObject,
    mut v_a_4983_: *mut leanh::LeanObject,
    mut v_a_4984_: *mut leanh::LeanObject,
    mut v_a_4985_: *mut leanh::LeanObject,
    mut v_a_4986_: *mut leanh::LeanObject,
    mut v_a_4987_: *mut leanh::LeanObject,
    mut v_a_4988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toExpr_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4994_: u8 = 0;
    let mut v_fileName_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5007_: u8 = 0;
    let mut v_cancelTk_x3f_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5009_: u8 = 0;
    let mut v_inheritedTraceOptions_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5018_: u8 = 0;
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5021_: u8 = 0;
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: u8 = 0;
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5039_: u8 = 0;
    let mut v_unused_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5044_: u8 = 0;
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5048_: u8 = 0;
    let mut v_reuseFailAlloc_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5050_: u8 = 0;
    let mut v_a_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5054_: u8 = 0;
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5058_: u8 = 0;
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toExpr_4990_ = leanh::lean_ctor_get(v_inst_4980_, 0);
                v_toTypeExpr_4991_ = leanh::lean_ctor_get(v_inst_4980_, 1);
                v_isSharedCheck_5059_ = (!leanh::lean_is_exclusive(v_inst_4980_)) as u8;
                if v_isSharedCheck_5059_ == 0 {
                    v___x_4993_ = v_inst_4980_;
                    v_isShared_4994_ = v_isSharedCheck_5059_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toTypeExpr_4991_);
                    leanh::lean_inc(v_toExpr_4990_);
                    leanh::lean_dec(v_inst_4980_);
                    v___x_4993_ = leanh::lean_box(0);
                    v_isShared_4994_ = v_isSharedCheck_5059_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileName_4995_ = leanh::lean_ctor_get(v_a_4987_, 0);
                v_fileMap_4996_ = leanh::lean_ctor_get(v_a_4987_, 1);
                v_options_4997_ = leanh::lean_ctor_get(v_a_4987_, 2);
                v_currRecDepth_4998_ = leanh::lean_ctor_get(v_a_4987_, 3);
                v_maxRecDepth_4999_ = leanh::lean_ctor_get(v_a_4987_, 4);
                v_ref_5000_ = leanh::lean_ctor_get(v_a_4987_, 5);
                v_currNamespace_5001_ = leanh::lean_ctor_get(v_a_4987_, 6);
                v_openDecls_5002_ = leanh::lean_ctor_get(v_a_4987_, 7);
                v_initHeartbeats_5003_ = leanh::lean_ctor_get(v_a_4987_, 8);
                v_maxHeartbeats_5004_ = leanh::lean_ctor_get(v_a_4987_, 9);
                v_quotContext_5005_ = leanh::lean_ctor_get(v_a_4987_, 10);
                v_currMacroScope_5006_ = leanh::lean_ctor_get(v_a_4987_, 11);
                v_diag_5007_ = leanh::lean_ctor_get_uint8(
                    v_a_4987_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5008_ = leanh::lean_ctor_get(v_a_4987_, 12);
                v_suppressElabErrors_5009_ = leanh::lean_ctor_get_uint8(
                    v_a_4987_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5010_ = leanh::lean_ctor_get(v_a_4987_, 13);
                leanh::lean_inc(v_stx_4982_);
                v___x_5011_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_4982_,
                    );
                v_ref_5012_ = l_Lean_replaceRef(v_stx_4982_, v_ref_5000_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_5010_);
                leanh::lean_inc(v_cancelTk_x3f_5008_);
                leanh::lean_inc(v_currMacroScope_5006_);
                leanh::lean_inc(v_quotContext_5005_);
                leanh::lean_inc(v_maxHeartbeats_5004_);
                leanh::lean_inc(v_initHeartbeats_5003_);
                leanh::lean_inc(v_openDecls_5002_);
                leanh::lean_inc(v_currNamespace_5001_);
                leanh::lean_inc(v_maxRecDepth_4999_);
                leanh::lean_inc(v_currRecDepth_4998_);
                leanh::lean_inc_ref(v_options_4997_);
                leanh::lean_inc_ref(v_fileMap_4996_);
                leanh::lean_inc_ref(v_fileName_4995_);
                v___x_5013_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_5013_, 0, v_fileName_4995_);
                leanh::lean_ctor_set(v___x_5013_, 1, v_fileMap_4996_);
                leanh::lean_ctor_set(v___x_5013_, 2, v_options_4997_);
                leanh::lean_ctor_set(v___x_5013_, 3, v_currRecDepth_4998_);
                leanh::lean_ctor_set(v___x_5013_, 4, v_maxRecDepth_4999_);
                leanh::lean_ctor_set(v___x_5013_, 5, v_ref_5012_);
                leanh::lean_ctor_set(v___x_5013_, 6, v_currNamespace_5001_);
                leanh::lean_ctor_set(v___x_5013_, 7, v_openDecls_5002_);
                leanh::lean_ctor_set(v___x_5013_, 8, v_initHeartbeats_5003_);
                leanh::lean_ctor_set(v___x_5013_, 9, v_maxHeartbeats_5004_);
                leanh::lean_ctor_set(v___x_5013_, 10, v_quotContext_5005_);
                leanh::lean_ctor_set(v___x_5013_, 11, v_currMacroScope_5006_);
                leanh::lean_ctor_set(v___x_5013_, 12, v_cancelTk_x3f_5008_);
                leanh::lean_ctor_set(v___x_5013_, 13, v_inheritedTraceOptions_5010_);
                leanh::lean_ctor_set_uint8(
                    v___x_5013_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_5007_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5013_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5009_,
                );
                leanh::lean_inc(v_a_4988_);
                leanh::lean_inc(v_a_4986_);
                leanh::lean_inc_ref(v_a_4985_);
                leanh::lean_inc(v_a_4984_);
                leanh::lean_inc_ref(v_a_4983_);
                v___x_5014_ = leanh::lean_apply_8(
                    v_f_4981_,
                    v___x_5011_,
                    v_a_4983_,
                    v_a_4984_,
                    v_a_4985_,
                    v_a_4986_,
                    v___x_5013_,
                    v_a_4988_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5014_) == 0 {
                    v_a_5015_ = leanh::lean_ctor_get(v___x_5014_, 0);
                    v_isSharedCheck_5050_ = (!leanh::lean_is_exclusive(v___x_5014_)) as u8;
                    if v_isSharedCheck_5050_ == 0 {
                        v___x_5017_ = v___x_5014_;
                        v_isShared_5018_ = v_isSharedCheck_5050_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5015_);
                        leanh::lean_dec(v___x_5014_);
                        v___x_5017_ = leanh::lean_box(0);
                        v_isShared_5018_ = v_isSharedCheck_5050_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4993_);
                    leanh::lean_dec_ref(v_toTypeExpr_4991_);
                    leanh::lean_dec_ref(v_toExpr_4990_);
                    leanh::lean_dec(v_stx_4982_);
                    v_a_5051_ = leanh::lean_ctor_get(v___x_5014_, 0);
                    v_isSharedCheck_5058_ = (!leanh::lean_is_exclusive(v___x_5014_)) as u8;
                    if v_isSharedCheck_5058_ == 0 {
                        v___x_5053_ = v___x_5014_;
                        v_isShared_5054_ = v_isSharedCheck_5058_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5051_);
                        leanh::lean_dec(v___x_5014_);
                        v___x_5053_ = leanh::lean_box(0);
                        v_isShared_5054_ = v_isSharedCheck_5058_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5019_ = lean_st_ref_get(v_a_4988_);
                v_infoState_5020_ = leanh::lean_ctor_get(v___x_5019_, 7);
                leanh::lean_inc_ref(v_infoState_5020_);
                leanh::lean_dec(v___x_5019_);
                v_enabled_5021_ = leanh::lean_ctor_get_uint8(
                    v_infoState_5020_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_5020_);
                leanh::lean_inc(v_a_5015_);
                v___x_5022_ = leanh::lean_apply_1(v_toExpr_4990_, v_a_5015_);
                leanh::lean_inc_ref(v___x_5022_);
                if v_isShared_4994_ == 0 {
                    leanh::lean_ctor_set(v___x_4993_, 1, v___x_5022_);
                    leanh::lean_ctor_set(v___x_4993_, 0, v_a_5015_);
                    v___x_5024_ = v___x_4993_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5049_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_a_5015_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5049_, 1, v___x_5022_);
                    v___x_5024_ = v_reuseFailAlloc_5049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_enabled_5021_ == 0 {
                    leanh::lean_dec_ref(v___x_5022_);
                    leanh::lean_dec_ref(v_toTypeExpr_4991_);
                    leanh::lean_dec(v_stx_4982_);
                    if v_isShared_5018_ == 0 {
                        leanh::lean_ctor_set(v___x_5017_, 0, v___x_5024_);
                        v___x_5026_ = v___x_5017_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5027_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
                        v___x_5026_ = v_reuseFailAlloc_5027_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5017_);
                    v___x_5028_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5028_, 0, v_toTypeExpr_4991_);
                    v___x_5029_ = leanh::lean_box(0);
                    v___x_5030_ = leanh::lean_box(0);
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
                    if leanh::lean_obj_tag(v___x_5032_) == 0 {
                        v_isSharedCheck_5039_ =
                            (!leanh::lean_is_exclusive(v___x_5032_)) as u8;
                        if v_isSharedCheck_5039_ == 0 {
                            v_unused_5040_ = leanh::lean_ctor_get(v___x_5032_, 0);
                            leanh::lean_dec(v_unused_5040_);
                            v___x_5034_ = v___x_5032_;
                            v_isShared_5035_ = v_isSharedCheck_5039_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5032_);
                            v___x_5034_ = leanh::lean_box(0);
                            v_isShared_5035_ = v_isSharedCheck_5039_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_5024_);
                        v_a_5041_ = leanh::lean_ctor_get(v___x_5032_, 0);
                        v_isSharedCheck_5048_ =
                            (!leanh::lean_is_exclusive(v___x_5032_)) as u8;
                        if v_isSharedCheck_5048_ == 0 {
                            v___x_5043_ = v___x_5032_;
                            v_isShared_5044_ = v_isSharedCheck_5048_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5041_);
                            leanh::lean_dec(v___x_5032_);
                            v___x_5043_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_5034_, 0, v___x_5024_);
                    v___x_5037_ = v___x_5034_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5038_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5038_, 0, v___x_5024_);
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
                    v_reuseFailAlloc_5047_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5041_);
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
                    v_reuseFailAlloc_5057_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_a_5051_);
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
    mut v_inst_5060_: *mut leanh::LeanObject,
    mut v_f_5061_: *mut leanh::LeanObject,
    mut v_stx_5062_: *mut leanh::LeanObject,
    mut v_a_5063_: *mut leanh::LeanObject,
    mut v_a_5064_: *mut leanh::LeanObject,
    mut v_a_5065_: *mut leanh::LeanObject,
    mut v_a_5066_: *mut leanh::LeanObject,
    mut v_a_5067_: *mut leanh::LeanObject,
    mut v_a_5068_: *mut leanh::LeanObject,
    mut v_a_5069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_5068_);
    leanh::lean_dec_ref(v_a_5067_);
    leanh::lean_dec(v_a_5066_);
    leanh::lean_dec_ref(v_a_5065_);
    leanh::lean_dec(v_a_5064_);
    leanh::lean_dec_ref(v_a_5063_);
    return v_res_5070_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(
    mut v_00_u03b1_5071_: *mut leanh::LeanObject,
    mut v_inst_5072_: *mut leanh::LeanObject,
    mut v_f_5073_: *mut leanh::LeanObject,
    mut v_stx_5074_: *mut leanh::LeanObject,
    mut v_a_5075_: *mut leanh::LeanObject,
    mut v_a_5076_: *mut leanh::LeanObject,
    mut v_a_5077_: *mut leanh::LeanObject,
    mut v_a_5078_: *mut leanh::LeanObject,
    mut v_a_5079_: *mut leanh::LeanObject,
    mut v_a_5080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toExpr_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5086_: u8 = 0;
    let mut v_fileName_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5099_: u8 = 0;
    let mut v_cancelTk_x3f_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5101_: u8 = 0;
    let mut v_inheritedTraceOptions_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5110_: u8 = 0;
    let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5113_: u8 = 0;
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: u8 = 0;
    let mut v___x_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5127_: u8 = 0;
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5131_: u8 = 0;
    let mut v_unused_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5140_: u8 = 0;
    let mut v_reuseFailAlloc_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5142_: u8 = 0;
    let mut v_a_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5150_: u8 = 0;
    let mut v_isSharedCheck_5151_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toExpr_5082_ = leanh::lean_ctor_get(v_inst_5072_, 0);
                v_toTypeExpr_5083_ = leanh::lean_ctor_get(v_inst_5072_, 1);
                v_isSharedCheck_5151_ = (!leanh::lean_is_exclusive(v_inst_5072_)) as u8;
                if v_isSharedCheck_5151_ == 0 {
                    v___x_5085_ = v_inst_5072_;
                    v_isShared_5086_ = v_isSharedCheck_5151_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toTypeExpr_5083_);
                    leanh::lean_inc(v_toExpr_5082_);
                    leanh::lean_dec(v_inst_5072_);
                    v___x_5085_ = leanh::lean_box(0);
                    v_isShared_5086_ = v_isSharedCheck_5151_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileName_5087_ = leanh::lean_ctor_get(v_a_5079_, 0);
                v_fileMap_5088_ = leanh::lean_ctor_get(v_a_5079_, 1);
                v_options_5089_ = leanh::lean_ctor_get(v_a_5079_, 2);
                v_currRecDepth_5090_ = leanh::lean_ctor_get(v_a_5079_, 3);
                v_maxRecDepth_5091_ = leanh::lean_ctor_get(v_a_5079_, 4);
                v_ref_5092_ = leanh::lean_ctor_get(v_a_5079_, 5);
                v_currNamespace_5093_ = leanh::lean_ctor_get(v_a_5079_, 6);
                v_openDecls_5094_ = leanh::lean_ctor_get(v_a_5079_, 7);
                v_initHeartbeats_5095_ = leanh::lean_ctor_get(v_a_5079_, 8);
                v_maxHeartbeats_5096_ = leanh::lean_ctor_get(v_a_5079_, 9);
                v_quotContext_5097_ = leanh::lean_ctor_get(v_a_5079_, 10);
                v_currMacroScope_5098_ = leanh::lean_ctor_get(v_a_5079_, 11);
                v_diag_5099_ = leanh::lean_ctor_get_uint8(
                    v_a_5079_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5100_ = leanh::lean_ctor_get(v_a_5079_, 12);
                v_suppressElabErrors_5101_ = leanh::lean_ctor_get_uint8(
                    v_a_5079_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5102_ = leanh::lean_ctor_get(v_a_5079_, 13);
                leanh::lean_inc(v_stx_5074_);
                v___x_5103_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_5074_,
                    );
                v_ref_5104_ = l_Lean_replaceRef(v_stx_5074_, v_ref_5092_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_5102_);
                leanh::lean_inc(v_cancelTk_x3f_5100_);
                leanh::lean_inc(v_currMacroScope_5098_);
                leanh::lean_inc(v_quotContext_5097_);
                leanh::lean_inc(v_maxHeartbeats_5096_);
                leanh::lean_inc(v_initHeartbeats_5095_);
                leanh::lean_inc(v_openDecls_5094_);
                leanh::lean_inc(v_currNamespace_5093_);
                leanh::lean_inc(v_maxRecDepth_5091_);
                leanh::lean_inc(v_currRecDepth_5090_);
                leanh::lean_inc_ref(v_options_5089_);
                leanh::lean_inc_ref(v_fileMap_5088_);
                leanh::lean_inc_ref(v_fileName_5087_);
                v___x_5105_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_5105_, 0, v_fileName_5087_);
                leanh::lean_ctor_set(v___x_5105_, 1, v_fileMap_5088_);
                leanh::lean_ctor_set(v___x_5105_, 2, v_options_5089_);
                leanh::lean_ctor_set(v___x_5105_, 3, v_currRecDepth_5090_);
                leanh::lean_ctor_set(v___x_5105_, 4, v_maxRecDepth_5091_);
                leanh::lean_ctor_set(v___x_5105_, 5, v_ref_5104_);
                leanh::lean_ctor_set(v___x_5105_, 6, v_currNamespace_5093_);
                leanh::lean_ctor_set(v___x_5105_, 7, v_openDecls_5094_);
                leanh::lean_ctor_set(v___x_5105_, 8, v_initHeartbeats_5095_);
                leanh::lean_ctor_set(v___x_5105_, 9, v_maxHeartbeats_5096_);
                leanh::lean_ctor_set(v___x_5105_, 10, v_quotContext_5097_);
                leanh::lean_ctor_set(v___x_5105_, 11, v_currMacroScope_5098_);
                leanh::lean_ctor_set(v___x_5105_, 12, v_cancelTk_x3f_5100_);
                leanh::lean_ctor_set(v___x_5105_, 13, v_inheritedTraceOptions_5102_);
                leanh::lean_ctor_set_uint8(
                    v___x_5105_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_5099_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5105_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5101_,
                );
                leanh::lean_inc(v_a_5080_);
                leanh::lean_inc(v_a_5078_);
                leanh::lean_inc_ref(v_a_5077_);
                leanh::lean_inc(v_a_5076_);
                leanh::lean_inc_ref(v_a_5075_);
                v___x_5106_ = leanh::lean_apply_8(
                    v_f_5073_,
                    v___x_5103_,
                    v_a_5075_,
                    v_a_5076_,
                    v_a_5077_,
                    v_a_5078_,
                    v___x_5105_,
                    v_a_5080_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5106_) == 0 {
                    v_a_5107_ = leanh::lean_ctor_get(v___x_5106_, 0);
                    v_isSharedCheck_5142_ = (!leanh::lean_is_exclusive(v___x_5106_)) as u8;
                    if v_isSharedCheck_5142_ == 0 {
                        v___x_5109_ = v___x_5106_;
                        v_isShared_5110_ = v_isSharedCheck_5142_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5107_);
                        leanh::lean_dec(v___x_5106_);
                        v___x_5109_ = leanh::lean_box(0);
                        v_isShared_5110_ = v_isSharedCheck_5142_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5085_);
                    leanh::lean_dec_ref(v_toTypeExpr_5083_);
                    leanh::lean_dec_ref(v_toExpr_5082_);
                    leanh::lean_dec(v_stx_5074_);
                    v_a_5143_ = leanh::lean_ctor_get(v___x_5106_, 0);
                    v_isSharedCheck_5150_ = (!leanh::lean_is_exclusive(v___x_5106_)) as u8;
                    if v_isSharedCheck_5150_ == 0 {
                        v___x_5145_ = v___x_5106_;
                        v_isShared_5146_ = v_isSharedCheck_5150_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5143_);
                        leanh::lean_dec(v___x_5106_);
                        v___x_5145_ = leanh::lean_box(0);
                        v_isShared_5146_ = v_isSharedCheck_5150_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5111_ = lean_st_ref_get(v_a_5080_);
                v_infoState_5112_ = leanh::lean_ctor_get(v___x_5111_, 7);
                leanh::lean_inc_ref(v_infoState_5112_);
                leanh::lean_dec(v___x_5111_);
                v_enabled_5113_ = leanh::lean_ctor_get_uint8(
                    v_infoState_5112_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_5112_);
                leanh::lean_inc(v_a_5107_);
                v___x_5114_ = leanh::lean_apply_1(v_toExpr_5082_, v_a_5107_);
                leanh::lean_inc_ref(v___x_5114_);
                if v_isShared_5086_ == 0 {
                    leanh::lean_ctor_set(v___x_5085_, 1, v___x_5114_);
                    leanh::lean_ctor_set(v___x_5085_, 0, v_a_5107_);
                    v___x_5116_ = v___x_5085_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5141_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5107_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5141_, 1, v___x_5114_);
                    v___x_5116_ = v_reuseFailAlloc_5141_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_enabled_5113_ == 0 {
                    leanh::lean_dec_ref(v___x_5114_);
                    leanh::lean_dec_ref(v_toTypeExpr_5083_);
                    leanh::lean_dec(v_stx_5074_);
                    if v_isShared_5110_ == 0 {
                        leanh::lean_ctor_set(v___x_5109_, 0, v___x_5116_);
                        v___x_5118_ = v___x_5109_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5119_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 0, v___x_5116_);
                        v___x_5118_ = v_reuseFailAlloc_5119_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5109_);
                    v___x_5120_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5120_, 0, v_toTypeExpr_5083_);
                    v___x_5121_ = leanh::lean_box(0);
                    v___x_5122_ = leanh::lean_box(0);
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
                    if leanh::lean_obj_tag(v___x_5124_) == 0 {
                        v_isSharedCheck_5131_ =
                            (!leanh::lean_is_exclusive(v___x_5124_)) as u8;
                        if v_isSharedCheck_5131_ == 0 {
                            v_unused_5132_ = leanh::lean_ctor_get(v___x_5124_, 0);
                            leanh::lean_dec(v_unused_5132_);
                            v___x_5126_ = v___x_5124_;
                            v_isShared_5127_ = v_isSharedCheck_5131_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5124_);
                            v___x_5126_ = leanh::lean_box(0);
                            v_isShared_5127_ = v_isSharedCheck_5131_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_5116_);
                        v_a_5133_ = leanh::lean_ctor_get(v___x_5124_, 0);
                        v_isSharedCheck_5140_ =
                            (!leanh::lean_is_exclusive(v___x_5124_)) as u8;
                        if v_isSharedCheck_5140_ == 0 {
                            v___x_5135_ = v___x_5124_;
                            v_isShared_5136_ = v_isSharedCheck_5140_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5133_);
                            leanh::lean_dec(v___x_5124_);
                            v___x_5135_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_5126_, 0, v___x_5116_);
                    v___x_5129_ = v___x_5126_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5130_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5130_, 0, v___x_5116_);
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
                    v_reuseFailAlloc_5139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
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
                    v_reuseFailAlloc_5149_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
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
    mut v_00_u03b1_5152_: *mut leanh::LeanObject,
    mut v_inst_5153_: *mut leanh::LeanObject,
    mut v_f_5154_: *mut leanh::LeanObject,
    mut v_stx_5155_: *mut leanh::LeanObject,
    mut v_a_5156_: *mut leanh::LeanObject,
    mut v_a_5157_: *mut leanh::LeanObject,
    mut v_a_5158_: *mut leanh::LeanObject,
    mut v_a_5159_: *mut leanh::LeanObject,
    mut v_a_5160_: *mut leanh::LeanObject,
    mut v_a_5161_: *mut leanh::LeanObject,
    mut v_a_5162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_5161_);
    leanh::lean_dec_ref(v_a_5160_);
    leanh::lean_dec(v_a_5159_);
    leanh::lean_dec_ref(v_a_5158_);
    leanh::lean_dec(v_a_5157_);
    leanh::lean_dec_ref(v_a_5156_);
    return v_res_5163_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(
    mut v_msgData_5164_: *mut leanh::LeanObject,
    mut v___y_5165_: *mut leanh::LeanObject,
    mut v___y_5166_: *mut leanh::LeanObject,
    mut v___y_5167_: *mut leanh::LeanObject,
    mut v___y_5168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5170_ = lean_st_ref_get(v___y_5168_);
    v_env_5171_ = leanh::lean_ctor_get(v___x_5170_, 0);
    leanh::lean_inc_ref(v_env_5171_);
    leanh::lean_dec(v___x_5170_);
    v___x_5172_ = lean_st_ref_get(v___y_5166_);
    v_mctx_5173_ = leanh::lean_ctor_get(v___x_5172_, 0);
    leanh::lean_inc_ref(v_mctx_5173_);
    leanh::lean_dec(v___x_5172_);
    v_lctx_5174_ = leanh::lean_ctor_get(v___y_5165_, 2);
    v_options_5175_ = leanh::lean_ctor_get(v___y_5167_, 2);
    leanh::lean_inc_ref(v_options_5175_);
    leanh::lean_inc_ref(v_lctx_5174_);
    v___x_5176_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_5176_, 0, v_env_5171_);
    leanh::lean_ctor_set(v___x_5176_, 1, v_mctx_5173_);
    leanh::lean_ctor_set(v___x_5176_, 2, v_lctx_5174_);
    leanh::lean_ctor_set(v___x_5176_, 3, v_options_5175_);
    v___x_5177_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5177_, 0, v___x_5176_);
    leanh::lean_ctor_set(v___x_5177_, 1, v_msgData_5164_);
    v___x_5178_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5178_, 0, v___x_5177_);
    return v___x_5178_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0___boxed(
    mut v_msgData_5179_: *mut leanh::LeanObject,
    mut v___y_5180_: *mut leanh::LeanObject,
    mut v___y_5181_: *mut leanh::LeanObject,
    mut v___y_5182_: *mut leanh::LeanObject,
    mut v___y_5183_: *mut leanh::LeanObject,
    mut v___y_5184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5185_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msgData_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
    leanh::lean_dec(v___y_5183_);
    leanh::lean_dec_ref(v___y_5182_);
    leanh::lean_dec(v___y_5181_);
    leanh::lean_dec_ref(v___y_5180_);
    return v_res_5185_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(
    mut v_msg_5186_: *mut leanh::LeanObject,
    mut v___y_5187_: *mut leanh::LeanObject,
    mut v___y_5188_: *mut leanh::LeanObject,
    mut v___y_5189_: *mut leanh::LeanObject,
    mut v___y_5190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5197_: u8 = 0;
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5192_ = leanh::lean_ctor_get(v___y_5189_, 5);
                v___x_5193_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
                v_a_5194_ = leanh::lean_ctor_get(v___x_5193_, 0);
                v_isSharedCheck_5202_ = (!leanh::lean_is_exclusive(v___x_5193_)) as u8;
                if v_isSharedCheck_5202_ == 0 {
                    v___x_5196_ = v___x_5193_;
                    v_isShared_5197_ = v_isSharedCheck_5202_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5194_);
                    leanh::lean_dec(v___x_5193_);
                    v___x_5196_ = leanh::lean_box(0);
                    v_isShared_5197_ = v_isSharedCheck_5202_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_5192_);
                v___x_5198_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5198_, 0, v_ref_5192_);
                leanh::lean_ctor_set(v___x_5198_, 1, v_a_5194_);
                if v_isShared_5197_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5196_, 1);
                    leanh::lean_ctor_set(v___x_5196_, 0, v___x_5198_);
                    v___x_5200_ = v___x_5196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5201_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5201_, 0, v___x_5198_);
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
    mut v_msg_5203_: *mut leanh::LeanObject,
    mut v___y_5204_: *mut leanh::LeanObject,
    mut v___y_5205_: *mut leanh::LeanObject,
    mut v___y_5206_: *mut leanh::LeanObject,
    mut v___y_5207_: *mut leanh::LeanObject,
    mut v___y_5208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5209_ =
        l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(
            v_msg_5203_,
            v___y_5204_,
            v___y_5205_,
            v___y_5206_,
            v___y_5207_,
        );
    leanh::lean_dec(v___y_5207_);
    leanh::lean_dec_ref(v___y_5206_);
    leanh::lean_dec(v___y_5205_);
    leanh::lean_dec_ref(v___y_5204_);
    return v_res_5209_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5211_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0;
    v___x_5212_ = l_Lean_stringToMessageData(v___x_5211_);
    return v___x_5212_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
    mut v_f_5213_: *mut leanh::LeanObject,
    mut v_e_5214_: *mut leanh::LeanObject,
    mut v_errMsg_5215_: *mut leanh::LeanObject,
    mut v_a_5216_: *mut leanh::LeanObject,
    mut v_a_5217_: *mut leanh::LeanObject,
    mut v_a_5218_: *mut leanh::LeanObject,
    mut v_a_5219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5227_: u8 = 0;
    let mut v_id_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5231_: u8 = 0;
    let mut v___x_5232_: u8 = 0;
    let mut v___x_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5240_: u8 = 0;
    let mut v_unused_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: u8 = 0;
    let mut v___x_5246_: u8 = 0;
    let mut v___y_5248_: u8 = 0;
    let mut v_id_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: u8 = 0;
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5258_: u8 = 0;
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5262_: u8 = 0;
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_f_5213_);
                leanh::lean_inc(v_a_5219_);
                leanh::lean_inc_ref(v_a_5218_);
                leanh::lean_inc(v_a_5217_);
                leanh::lean_inc_ref(v_a_5216_);
                leanh::lean_inc_ref(v_e_5214_);
                v___x_5221_ = leanh::lean_apply_6(
                    v_f_5213_,
                    v_e_5214_,
                    v_a_5216_,
                    v_a_5217_,
                    v_a_5218_,
                    v_a_5219_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5221_) == 0 {
                    leanh::lean_dec_ref(v_errMsg_5215_);
                    leanh::lean_dec_ref(v_e_5214_);
                    leanh::lean_dec_ref(v_f_5213_);
                    return v___x_5221_;
                } else {
                    v_a_5222_ = leanh::lean_ctor_get(v___x_5221_, 0);
                    leanh::lean_inc(v_a_5222_);
                    v___x_5223_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
                    v___x_5263_ = l_Lean_Exception_isInterrupt(v_a_5222_);
                    if v___x_5263_ == 0 {
                        leanh::lean_inc(v_a_5222_);
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
                    if leanh::lean_obj_tag(v___y_5226_) == 0 {
                        leanh::lean_dec_ref_known(v___y_5226_, 2);
                        leanh::lean_dec_ref(v_errMsg_5215_);
                        leanh::lean_dec_ref(v_e_5214_);
                        return v___y_5225_;
                    } else {
                        v_id_5228_ = leanh::lean_ctor_get(v___y_5226_, 0);
                        v_isSharedCheck_5240_ =
                            (!leanh::lean_is_exclusive(v___y_5226_)) as u8;
                        if v_isSharedCheck_5240_ == 0 {
                            v_unused_5241_ = leanh::lean_ctor_get(v___y_5226_, 1);
                            leanh::lean_dec(v_unused_5241_);
                            v___x_5230_ = v___y_5226_;
                            v_isShared_5231_ = v_isSharedCheck_5240_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_id_5228_);
                            leanh::lean_dec(v___y_5226_);
                            v___x_5230_ = leanh::lean_box(0);
                            v_isShared_5231_ = v_isSharedCheck_5240_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_5226_);
                    leanh::lean_dec_ref(v_errMsg_5215_);
                    leanh::lean_dec_ref(v_e_5214_);
                    return v___y_5225_;
                }
            }
            2 => {
                v___x_5232_ = l_Lean_instBEqInternalExceptionId_beq(v___x_5223_, v_id_5228_);
                leanh::lean_dec(v_id_5228_);
                if v___x_5232_ == 0 {
                    leanh::lean_del_object(v___x_5230_);
                    leanh::lean_dec_ref(v_errMsg_5215_);
                    leanh::lean_dec_ref(v_e_5214_);
                    return v___y_5225_;
                } else {
                    leanh::lean_dec_ref(v___y_5225_);
                    v___x_5233_ = leanh::lean_obj_once(
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
                        leanh::lean_ctor_set_tag(v___x_5230_, 7);
                        leanh::lean_ctor_set(v___x_5230_, 1, v___x_5234_);
                        leanh::lean_ctor_set(v___x_5230_, 0, v___x_5233_);
                        v___x_5236_ = v___x_5230_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5239_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5233_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5239_, 1, v___x_5234_);
                        v___x_5236_ = v_reuseFailAlloc_5239_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5237_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5237_, 0, v___x_5236_);
                leanh::lean_ctor_set(v___x_5237_, 1, v_errMsg_5215_);
                v___x_5238_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v___x_5237_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_);
                return v___x_5238_;
            }
            4 => {
                v___x_5245_ = l_Lean_Exception_isInterrupt(v_a_5244_);
                if v___x_5245_ == 0 {
                    leanh::lean_inc_ref(v_a_5244_);
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
                    if leanh::lean_obj_tag(v_a_5222_) == 0 {
                        leanh::lean_dec_ref_known(v_a_5222_, 2);
                        leanh::lean_dec_ref(v_errMsg_5215_);
                        leanh::lean_dec_ref(v_e_5214_);
                        leanh::lean_dec_ref(v_f_5213_);
                        return v___x_5221_;
                    } else {
                        v_id_5249_ = leanh::lean_ctor_get(v_a_5222_, 0);
                        leanh::lean_inc(v_id_5249_);
                        leanh::lean_dec_ref_known(v_a_5222_, 2);
                        v___x_5250_ =
                            l_Lean_instBEqInternalExceptionId_beq(v___x_5223_, v_id_5249_);
                        leanh::lean_dec(v_id_5249_);
                        if v___x_5250_ == 0 {
                            leanh::lean_dec_ref(v_errMsg_5215_);
                            leanh::lean_dec_ref(v_e_5214_);
                            leanh::lean_dec_ref(v_f_5213_);
                            return v___x_5221_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_5221_, 1);
                            leanh::lean_inc(v_a_5219_);
                            leanh::lean_inc_ref(v_a_5218_);
                            leanh::lean_inc(v_a_5217_);
                            leanh::lean_inc_ref(v_a_5216_);
                            leanh::lean_inc_ref(v_e_5214_);
                            v___x_5251_ =
                                lean_whnf(v_e_5214_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_);
                            if leanh::lean_obj_tag(v___x_5251_) == 0 {
                                v_a_5252_ = leanh::lean_ctor_get(v___x_5251_, 0);
                                leanh::lean_inc(v_a_5252_);
                                leanh::lean_dec_ref_known(v___x_5251_, 1);
                                leanh::lean_inc(v_a_5219_);
                                leanh::lean_inc_ref(v_a_5218_);
                                leanh::lean_inc(v_a_5217_);
                                leanh::lean_inc_ref(v_a_5216_);
                                v___x_5253_ = leanh::lean_apply_6(
                                    v_f_5213_,
                                    v_a_5252_,
                                    v_a_5216_,
                                    v_a_5217_,
                                    v_a_5218_,
                                    v_a_5219_,
                                    leanh::lean_box(0),
                                );
                                if leanh::lean_obj_tag(v___x_5253_) == 0 {
                                    leanh::lean_dec_ref(v_errMsg_5215_);
                                    leanh::lean_dec_ref(v_e_5214_);
                                    return v___x_5253_;
                                } else {
                                    v_a_5254_ = leanh::lean_ctor_get(v___x_5253_, 0);
                                    leanh::lean_inc(v_a_5254_);
                                    v___y_5243_ = v___x_5253_;
                                    v_a_5244_ = v_a_5254_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_f_5213_);
                                v_a_5255_ = leanh::lean_ctor_get(v___x_5251_, 0);
                                v_isSharedCheck_5262_ =
                                    (!leanh::lean_is_exclusive(v___x_5251_)) as u8;
                                if v_isSharedCheck_5262_ == 0 {
                                    v___x_5257_ = v___x_5251_;
                                    v_isShared_5258_ = v_isSharedCheck_5262_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5255_);
                                    leanh::lean_dec(v___x_5251_);
                                    v___x_5257_ = leanh::lean_box(0);
                                    v_isShared_5258_ = v_isSharedCheck_5262_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5222_);
                    leanh::lean_dec_ref(v_errMsg_5215_);
                    leanh::lean_dec_ref(v_e_5214_);
                    leanh::lean_dec_ref(v_f_5213_);
                    return v___x_5221_;
                }
            }
            6 => {
                leanh::lean_inc(v_a_5255_);
                if v_isShared_5258_ == 0 {
                    v___x_5260_ = v___x_5257_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5261_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
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
    mut v_f_5265_: *mut leanh::LeanObject,
    mut v_e_5266_: *mut leanh::LeanObject,
    mut v_errMsg_5267_: *mut leanh::LeanObject,
    mut v_a_5268_: *mut leanh::LeanObject,
    mut v_a_5269_: *mut leanh::LeanObject,
    mut v_a_5270_: *mut leanh::LeanObject,
    mut v_a_5271_: *mut leanh::LeanObject,
    mut v_a_5272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5273_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
        v_f_5265_,
        v_e_5266_,
        v_errMsg_5267_,
        v_a_5268_,
        v_a_5269_,
        v_a_5270_,
        v_a_5271_,
    );
    leanh::lean_dec(v_a_5271_);
    leanh::lean_dec_ref(v_a_5270_);
    leanh::lean_dec(v_a_5269_);
    leanh::lean_dec_ref(v_a_5268_);
    return v_res_5273_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(
    mut v_00_u03b1_5274_: *mut leanh::LeanObject,
    mut v_f_5275_: *mut leanh::LeanObject,
    mut v_e_5276_: *mut leanh::LeanObject,
    mut v_errMsg_5277_: *mut leanh::LeanObject,
    mut v_a_5278_: *mut leanh::LeanObject,
    mut v_a_5279_: *mut leanh::LeanObject,
    mut v_a_5280_: *mut leanh::LeanObject,
    mut v_a_5281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5284_: *mut leanh::LeanObject,
    mut v_f_5285_: *mut leanh::LeanObject,
    mut v_e_5286_: *mut leanh::LeanObject,
    mut v_errMsg_5287_: *mut leanh::LeanObject,
    mut v_a_5288_: *mut leanh::LeanObject,
    mut v_a_5289_: *mut leanh::LeanObject,
    mut v_a_5290_: *mut leanh::LeanObject,
    mut v_a_5291_: *mut leanh::LeanObject,
    mut v_a_5292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_5291_);
    leanh::lean_dec_ref(v_a_5290_);
    leanh::lean_dec(v_a_5289_);
    leanh::lean_dec_ref(v_a_5288_);
    return v_res_5293_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(
    mut v_00_u03b1_5294_: *mut leanh::LeanObject,
    mut v_msg_5295_: *mut leanh::LeanObject,
    mut v___y_5296_: *mut leanh::LeanObject,
    mut v___y_5297_: *mut leanh::LeanObject,
    mut v___y_5298_: *mut leanh::LeanObject,
    mut v___y_5299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5302_: *mut leanh::LeanObject,
    mut v_msg_5303_: *mut leanh::LeanObject,
    mut v___y_5304_: *mut leanh::LeanObject,
    mut v___y_5305_: *mut leanh::LeanObject,
    mut v___y_5306_: *mut leanh::LeanObject,
    mut v___y_5307_: *mut leanh::LeanObject,
    mut v___y_5308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5309_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(
        v_00_u03b1_5302_,
        v_msg_5303_,
        v___y_5304_,
        v___y_5305_,
        v___y_5306_,
        v___y_5307_,
    );
    leanh::lean_dec(v___y_5307_);
    leanh::lean_dec_ref(v___y_5306_);
    leanh::lean_dec(v___y_5305_);
    leanh::lean_dec_ref(v___y_5304_);
    return v_res_5309_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
    mut v_item_5310_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_optionComps_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: u8 = 0;
    v_optionComps_5311_ = leanh::lean_ctor_get(v_item_5310_, 5);
    v___x_5312_ = l_List_isEmpty___redArg(v_optionComps_5311_);
    return v___x_5312_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous___boxed(
    mut v_item_5313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5314_: u8 = 0;
    let mut v_r_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5314_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_5313_);
    leanh::lean_dec_ref(v_item_5313_);
    v_r_5315_ = leanh::lean_box((v_res_5314_) as usize);
    return v_r_5315_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_root(
    mut v_item_5316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_optionComps_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_optionComps_5317_ = leanh::lean_ctor_get(v_item_5316_, 5);
    if leanh::lean_obj_tag(v_optionComps_5317_) == 1 {
        let mut v_head_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_5318_ = leanh::lean_ctor_get(v_optionComps_5317_, 0);
        leanh::lean_inc(v_head_5318_);
        return v_head_5318_;
    } else {
        let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5319_ = leanh::lean_box(0);
        return v___x_5319_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_root___boxed(
    mut v_item_5320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5321_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_5320_);
    leanh::lean_dec_ref(v_item_5320_);
    return v_res_5321_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(
    mut v_item_5322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5323_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_5322_);
    v___x_5324_ = l_Lean_Syntax_getId(v___x_5323_);
    leanh::lean_dec(v___x_5323_);
    if leanh::lean_obj_tag(v___x_5324_) == 1 {
        let mut v_str_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_str_5325_ = leanh::lean_ctor_get(v___x_5324_, 1);
        leanh::lean_inc_ref(v_str_5325_);
        leanh::lean_dec_ref_known(v___x_5324_, 2);
        return v_str_5325_;
    } else {
        let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_5324_);
        v___x_5326_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29;
        return v___x_5326_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_getRootStr___boxed(
    mut v_item_5327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5328_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_5327_);
    leanh::lean_dec_ref(v_item_5327_);
    return v_res_5328_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(
    mut v_item_5329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_prevOptionComps_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_prevOptionComps_5330_ = leanh::lean_ctor_get(v_item_5329_, 6);
    v___x_5331_ = leanh::lean_unsigned_to_nat(0);
    v___x_5332_ = l_List_get_x3fInternal___redArg(v_prevOptionComps_5330_, v___x_5331_);
    return v___x_5332_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f___boxed(
    mut v_item_5333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5334_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(v_item_5333_);
    leanh::lean_dec_ref(v_item_5333_);
    return v_res_5334_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(
    mut v_item_5335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_prevOptionComps_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_prevOptionComps_5336_ = leanh::lean_ctor_get(v_item_5335_, 6);
    if leanh::lean_obj_tag(v_prevOptionComps_5336_) == 1 {
        let mut v_head_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_5337_ = leanh::lean_ctor_get(v_prevOptionComps_5336_, 0);
        leanh::lean_inc(v_head_5337_);
        return v_head_5337_;
    } else {
        let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5338_ = leanh::lean_box(0);
        return v___x_5338_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_prevRoot___boxed(
    mut v_item_5339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5340_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(v_item_5339_);
    leanh::lean_dec_ref(v_item_5339_);
    return v_res_5340_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(
    mut v_x_5341_: *mut leanh::LeanObject,
    mut v_x_5342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5342_) == 0 {
                    return v_x_5341_;
                } else {
                    v_head_5343_ = leanh::lean_ctor_get(v_x_5342_, 0);
                    leanh::lean_inc(v_head_5343_);
                    v_tail_5344_ = leanh::lean_ctor_get(v_x_5342_, 1);
                    leanh::lean_inc(v_tail_5344_);
                    leanh::lean_dec_ref_known(v_x_5342_, 2);
                    v___x_5345_ = l_Lean_Name_appendCore(v_x_5341_, v_head_5343_);
                    leanh::lean_dec(v_x_5341_);
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
    mut v_a_5347_: *mut leanh::LeanObject,
    mut v_a_5348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5354_: u8 = 0;
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_5347_) == 0 {
                    v___x_5349_ = l_List_reverse___redArg(v_a_5348_);
                    return v___x_5349_;
                } else {
                    v_head_5350_ = leanh::lean_ctor_get(v_a_5347_, 0);
                    v_tail_5351_ = leanh::lean_ctor_get(v_a_5347_, 1);
                    v_isSharedCheck_5360_ = (!leanh::lean_is_exclusive(v_a_5347_)) as u8;
                    if v_isSharedCheck_5360_ == 0 {
                        v___x_5353_ = v_a_5347_;
                        v_isShared_5354_ = v_isSharedCheck_5360_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5351_);
                        leanh::lean_inc(v_head_5350_);
                        leanh::lean_dec(v_a_5347_);
                        v___x_5353_ = leanh::lean_box(0);
                        v_isShared_5354_ = v_isSharedCheck_5360_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5355_ = l_Lean_Syntax_getId(v_head_5350_);
                leanh::lean_dec(v_head_5350_);
                if v_isShared_5354_ == 0 {
                    leanh::lean_ctor_set(v___x_5353_, 1, v_a_5348_);
                    leanh::lean_ctor_set(v___x_5353_, 0, v___x_5355_);
                    v___x_5357_ = v___x_5353_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5359_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5355_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5359_, 1, v_a_5348_);
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
    mut v_item_5361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_optionComps_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_optionComps_5362_ = leanh::lean_ctor_get(v_item_5361_, 5);
    leanh::lean_inc(v_optionComps_5362_);
    leanh::lean_dec_ref(v_item_5361_);
    v___x_5363_ = leanh::lean_box(0);
    v___x_5364_ = leanh::lean_box(0);
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
    mut v_item_5367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_option_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bool_x3f_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origOptionName_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_optionComps_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prevOptionComps_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5380_: u8 = 0;
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5385_: u8 = 0;
    let mut v_unused_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5368_ = leanh::lean_ctor_get(v_item_5367_, 0);
                leanh::lean_inc(v_ref_5368_);
                v_option_5369_ = leanh::lean_ctor_get(v_item_5367_, 1);
                leanh::lean_inc(v_option_5369_);
                v_value_5370_ = leanh::lean_ctor_get(v_item_5367_, 2);
                leanh::lean_inc(v_value_5370_);
                v_bool_x3f_5371_ = leanh::lean_ctor_get(v_item_5367_, 3);
                leanh::lean_inc(v_bool_x3f_5371_);
                v_origOptionName_5372_ = leanh::lean_ctor_get(v_item_5367_, 4);
                leanh::lean_inc(v_origOptionName_5372_);
                v_optionComps_5373_ = leanh::lean_ctor_get(v_item_5367_, 5);
                v_prevOptionComps_5374_ = leanh::lean_ctor_get(v_item_5367_, 6);
                leanh::lean_inc(v_prevOptionComps_5374_);
                if leanh::lean_obj_tag(v_optionComps_5373_) == 0 {
                    v___y_5376_ = v_optionComps_5373_;
                    state = 1;
                    continue;
                } else {
                    v_tail_5393_ = leanh::lean_ctor_get(v_optionComps_5373_, 1);
                    leanh::lean_inc(v_tail_5393_);
                    v___y_5376_ = v_tail_5393_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5377_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_5367_);
                v_isSharedCheck_5385_ = (!leanh::lean_is_exclusive(v_item_5367_)) as u8;
                if v_isSharedCheck_5385_ == 0 {
                    v_unused_5386_ = leanh::lean_ctor_get(v_item_5367_, 6);
                    leanh::lean_dec(v_unused_5386_);
                    v_unused_5387_ = leanh::lean_ctor_get(v_item_5367_, 5);
                    leanh::lean_dec(v_unused_5387_);
                    v_unused_5388_ = leanh::lean_ctor_get(v_item_5367_, 4);
                    leanh::lean_dec(v_unused_5388_);
                    v_unused_5389_ = leanh::lean_ctor_get(v_item_5367_, 3);
                    leanh::lean_dec(v_unused_5389_);
                    v_unused_5390_ = leanh::lean_ctor_get(v_item_5367_, 2);
                    leanh::lean_dec(v_unused_5390_);
                    v_unused_5391_ = leanh::lean_ctor_get(v_item_5367_, 1);
                    leanh::lean_dec(v_unused_5391_);
                    v_unused_5392_ = leanh::lean_ctor_get(v_item_5367_, 0);
                    leanh::lean_dec(v_unused_5392_);
                    v___x_5379_ = v_item_5367_;
                    v_isShared_5380_ = v_isSharedCheck_5385_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_item_5367_);
                    v___x_5379_ = leanh::lean_box(0);
                    v_isShared_5380_ = v_isSharedCheck_5385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5381_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5381_, 0, v___x_5377_);
                leanh::lean_ctor_set(v___x_5381_, 1, v_prevOptionComps_5374_);
                if v_isShared_5380_ == 0 {
                    leanh::lean_ctor_set(v___x_5379_, 6, v___x_5381_);
                    leanh::lean_ctor_set(v___x_5379_, 5, v___y_5376_);
                    v___x_5383_ = v___x_5379_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5384_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_ref_5368_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 1, v_option_5369_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 2, v_value_5370_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 3, v_bool_x3f_5371_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 4, v_origOptionName_5372_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 5, v___y_5376_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 6, v___x_5381_);
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
-> *mut leanh::LeanObject {
    let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5394_ = leanh::lean_box(1);
    v___x_5395_ = l_Lean_MessageData_ofFormat(v___x_5394_);
    return v___x_5395_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5399_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2;
    v___x_5400_ = l_Lean_MessageData_ofFormat(v___x_5399_);
    return v___x_5400_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(
    mut v_x_5401_: *mut leanh::LeanObject,
    mut v_x_5402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5407_: u8 = 0;
    let mut v_before_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5424_: u8 = 0;
    let mut v_unused_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5402_) == 0 {
                    return v_x_5401_;
                } else {
                    v_head_5403_ = leanh::lean_ctor_get(v_x_5402_, 0);
                    v_tail_5404_ = leanh::lean_ctor_get(v_x_5402_, 1);
                    v_isSharedCheck_5426_ = (!leanh::lean_is_exclusive(v_x_5402_)) as u8;
                    if v_isSharedCheck_5426_ == 0 {
                        v___x_5406_ = v_x_5402_;
                        v_isShared_5407_ = v_isSharedCheck_5426_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5404_);
                        leanh::lean_inc(v_head_5403_);
                        leanh::lean_dec(v_x_5402_);
                        v___x_5406_ = leanh::lean_box(0);
                        v_isShared_5407_ = v_isSharedCheck_5426_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_5408_ = leanh::lean_ctor_get(v_head_5403_, 0);
                v_isSharedCheck_5424_ = (!leanh::lean_is_exclusive(v_head_5403_)) as u8;
                if v_isSharedCheck_5424_ == 0 {
                    v_unused_5425_ = leanh::lean_ctor_get(v_head_5403_, 1);
                    leanh::lean_dec(v_unused_5425_);
                    v___x_5410_ = v_head_5403_;
                    v_isShared_5411_ = v_isSharedCheck_5424_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_5408_);
                    leanh::lean_dec(v_head_5403_);
                    v___x_5410_ = leanh::lean_box(0);
                    v_isShared_5411_ = v_isSharedCheck_5424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5412_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_5411_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5410_, 7);
                    leanh::lean_ctor_set(v___x_5410_, 1, v___x_5412_);
                    leanh::lean_ctor_set(v___x_5410_, 0, v_x_5401_);
                    v___x_5414_ = v___x_5410_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5423_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_x_5401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 1, v___x_5412_);
                    v___x_5414_ = v_reuseFailAlloc_5423_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5415_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3);
                if v_isShared_5407_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5406_, 7);
                    leanh::lean_ctor_set(v___x_5406_, 1, v___x_5415_);
                    leanh::lean_ctor_set(v___x_5406_, 0, v___x_5414_);
                    v___x_5417_ = v___x_5406_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5422_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5422_, 0, v___x_5414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5422_, 1, v___x_5415_);
                    v___x_5417_ = v_reuseFailAlloc_5422_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5418_ = l_Lean_MessageData_ofSyntax(v_before_5408_);
                v___x_5419_ = l_Lean_indentD(v___x_5418_);
                v___x_5420_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5420_, 0, v___x_5417_);
                leanh::lean_ctor_set(v___x_5420_, 1, v___x_5419_);
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
    mut v_opts_5427_: *mut leanh::LeanObject,
    mut v_opt_5428_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_5429_ = leanh::lean_ctor_get(v_opt_5428_, 0);
    v_defValue_5430_ = leanh::lean_ctor_get(v_opt_5428_, 1);
    v_map_5431_ = leanh::lean_ctor_get(v_opts_5427_, 0);
    v___x_5432_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5431_,
            v_name_5429_,
        );
    if leanh::lean_obj_tag(v___x_5432_) == 0 {
        let mut v___x_5433_: u8 = 0;
        v___x_5433_ = (leanh::lean_unbox(v_defValue_5430_) as u8);
        return v___x_5433_;
    } else {
        let mut v_val_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5434_ = leanh::lean_ctor_get(v___x_5432_, 0);
        leanh::lean_inc(v_val_5434_);
        leanh::lean_dec_ref_known(v___x_5432_, 1);
        if leanh::lean_obj_tag(v_val_5434_) == 1 {
            let mut v_v_5435_: u8 = 0;
            v_v_5435_ = leanh::lean_ctor_get_uint8(v_val_5434_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_5434_, 0);
            return v_v_5435_;
        } else {
            let mut v___x_5436_: u8 = 0;
            leanh::lean_dec(v_val_5434_);
            v___x_5436_ = (leanh::lean_unbox(v_defValue_5430_) as u8);
            return v___x_5436_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_opts_5437_: *mut leanh::LeanObject,
    mut v_opt_5438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5439_: u8 = 0;
    let mut v_r_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5439_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_opts_5437_, v_opt_5438_);
    leanh::lean_dec_ref(v_opt_5438_);
    leanh::lean_dec_ref(v_opts_5437_);
    v_r_5440_ = leanh::lean_box((v_res_5439_) as usize);
    return v_r_5440_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5444_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1;
    v___x_5445_ = l_Lean_MessageData_ofFormat(v___x_5444_);
    return v___x_5445_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(
    mut v_msgData_5446_: *mut leanh::LeanObject,
    mut v_macroStack_5447_: *mut leanh::LeanObject,
    mut v___y_5448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: u8 = 0;
    let mut v___x_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5459_: u8 = 0;
    let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5471_: u8 = 0;
    let mut v_unused_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5450_ = leanh::lean_ctor_get(v___y_5448_, 2);
                v___x_5451_ = l_Lean_Elab_pp_macroStack;
                v___x_5452_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_options_5450_, v___x_5451_);
                if v___x_5452_ == 0 {
                    leanh::lean_dec(v_macroStack_5447_);
                    v___x_5453_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5453_, 0, v_msgData_5446_);
                    return v___x_5453_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_5447_) == 0 {
                        v___x_5454_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5454_, 0, v_msgData_5446_);
                        return v___x_5454_;
                    } else {
                        v_head_5455_ = leanh::lean_ctor_get(v_macroStack_5447_, 0);
                        leanh::lean_inc(v_head_5455_);
                        v_after_5456_ = leanh::lean_ctor_get(v_head_5455_, 1);
                        v_isSharedCheck_5471_ =
                            (!leanh::lean_is_exclusive(v_head_5455_)) as u8;
                        if v_isSharedCheck_5471_ == 0 {
                            v_unused_5472_ = leanh::lean_ctor_get(v_head_5455_, 0);
                            leanh::lean_dec(v_unused_5472_);
                            v___x_5458_ = v_head_5455_;
                            v_isShared_5459_ = v_isSharedCheck_5471_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_5456_);
                            leanh::lean_dec(v_head_5455_);
                            v___x_5458_ = leanh::lean_box(0);
                            v_isShared_5459_ = v_isSharedCheck_5471_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5460_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_5459_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5458_, 7);
                    leanh::lean_ctor_set(v___x_5458_, 1, v___x_5460_);
                    leanh::lean_ctor_set(v___x_5458_, 0, v_msgData_5446_);
                    v___x_5462_ = v___x_5458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5470_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_msgData_5446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5470_, 1, v___x_5460_);
                    v___x_5462_ = v_reuseFailAlloc_5470_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5463_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2);
                v___x_5464_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5464_, 0, v___x_5462_);
                leanh::lean_ctor_set(v___x_5464_, 1, v___x_5463_);
                v___x_5465_ = l_Lean_MessageData_ofSyntax(v_after_5456_);
                v___x_5466_ = l_Lean_indentD(v___x_5465_);
                v_msgData_5467_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_5467_, 0, v___x_5464_);
                leanh::lean_ctor_set(v_msgData_5467_, 1, v___x_5466_);
                v___x_5468_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(v_msgData_5467_, v_macroStack_5447_);
                v___x_5469_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5469_, 0, v___x_5468_);
                return v___x_5469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msgData_5473_: *mut leanh::LeanObject,
    mut v_macroStack_5474_: *mut leanh::LeanObject,
    mut v___y_5475_: *mut leanh::LeanObject,
    mut v___y_5476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5477_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_5473_, v_macroStack_5474_, v___y_5475_);
    leanh::lean_dec_ref(v___y_5475_);
    return v_res_5477_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(
    mut v_msg_5478_: *mut leanh::LeanObject,
    mut v___y_5479_: *mut leanh::LeanObject,
    mut v___y_5480_: *mut leanh::LeanObject,
    mut v___y_5481_: *mut leanh::LeanObject,
    mut v___y_5482_: *mut leanh::LeanObject,
    mut v___y_5483_: *mut leanh::LeanObject,
    mut v___y_5484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5495_: u8 = 0;
    let mut v___x_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5486_ = leanh::lean_ctor_get(v___y_5483_, 5);
                v___x_5487_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_5478_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_);
                v_a_5488_ = leanh::lean_ctor_get(v___x_5487_, 0);
                leanh::lean_inc(v_a_5488_);
                leanh::lean_dec_ref(v___x_5487_);
                v_macroStack_5489_ = leanh::lean_ctor_get(v___y_5479_, 1);
                v___x_5490_ = l_Lean_Elab_getBetterRef(v_ref_5486_, v_macroStack_5489_);
                leanh::lean_inc(v_macroStack_5489_);
                v___x_5491_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_a_5488_, v_macroStack_5489_, v___y_5483_);
                v_a_5492_ = leanh::lean_ctor_get(v___x_5491_, 0);
                v_isSharedCheck_5500_ = (!leanh::lean_is_exclusive(v___x_5491_)) as u8;
                if v_isSharedCheck_5500_ == 0 {
                    v___x_5494_ = v___x_5491_;
                    v_isShared_5495_ = v_isSharedCheck_5500_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5492_);
                    leanh::lean_dec(v___x_5491_);
                    v___x_5494_ = leanh::lean_box(0);
                    v_isShared_5495_ = v_isSharedCheck_5500_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5496_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5496_, 0, v___x_5490_);
                leanh::lean_ctor_set(v___x_5496_, 1, v_a_5492_);
                if v_isShared_5495_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5494_, 1);
                    leanh::lean_ctor_set(v___x_5494_, 0, v___x_5496_);
                    v___x_5498_ = v___x_5494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5499_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5499_, 0, v___x_5496_);
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
    mut v_msg_5501_: *mut leanh::LeanObject,
    mut v___y_5502_: *mut leanh::LeanObject,
    mut v___y_5503_: *mut leanh::LeanObject,
    mut v___y_5504_: *mut leanh::LeanObject,
    mut v___y_5505_: *mut leanh::LeanObject,
    mut v___y_5506_: *mut leanh::LeanObject,
    mut v___y_5507_: *mut leanh::LeanObject,
    mut v___y_5508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5509_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_);
    leanh::lean_dec(v___y_5507_);
    leanh::lean_dec_ref(v___y_5506_);
    leanh::lean_dec(v___y_5505_);
    leanh::lean_dec_ref(v___y_5504_);
    leanh::lean_dec(v___y_5503_);
    leanh::lean_dec_ref(v___y_5502_);
    return v_res_5509_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(
    mut v_ref_5510_: *mut leanh::LeanObject,
    mut v_msg_5511_: *mut leanh::LeanObject,
    mut v___y_5512_: *mut leanh::LeanObject,
    mut v___y_5513_: *mut leanh::LeanObject,
    mut v___y_5514_: *mut leanh::LeanObject,
    mut v___y_5515_: *mut leanh::LeanObject,
    mut v___y_5516_: *mut leanh::LeanObject,
    mut v___y_5517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5531_: u8 = 0;
    let mut v_cancelTk_x3f_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5533_: u8 = 0;
    let mut v_inheritedTraceOptions_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5519_ = leanh::lean_ctor_get(v___y_5516_, 0);
    v_fileMap_5520_ = leanh::lean_ctor_get(v___y_5516_, 1);
    v_options_5521_ = leanh::lean_ctor_get(v___y_5516_, 2);
    v_currRecDepth_5522_ = leanh::lean_ctor_get(v___y_5516_, 3);
    v_maxRecDepth_5523_ = leanh::lean_ctor_get(v___y_5516_, 4);
    v_ref_5524_ = leanh::lean_ctor_get(v___y_5516_, 5);
    v_currNamespace_5525_ = leanh::lean_ctor_get(v___y_5516_, 6);
    v_openDecls_5526_ = leanh::lean_ctor_get(v___y_5516_, 7);
    v_initHeartbeats_5527_ = leanh::lean_ctor_get(v___y_5516_, 8);
    v_maxHeartbeats_5528_ = leanh::lean_ctor_get(v___y_5516_, 9);
    v_quotContext_5529_ = leanh::lean_ctor_get(v___y_5516_, 10);
    v_currMacroScope_5530_ = leanh::lean_ctor_get(v___y_5516_, 11);
    v_diag_5531_ = leanh::lean_ctor_get_uint8(
        v___y_5516_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5532_ = leanh::lean_ctor_get(v___y_5516_, 12);
    v_suppressElabErrors_5533_ = leanh::lean_ctor_get_uint8(
        v___y_5516_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5534_ = leanh::lean_ctor_get(v___y_5516_, 13);
    v_ref_5535_ = l_Lean_replaceRef(v_ref_5510_, v_ref_5524_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_5534_);
    leanh::lean_inc(v_cancelTk_x3f_5532_);
    leanh::lean_inc(v_currMacroScope_5530_);
    leanh::lean_inc(v_quotContext_5529_);
    leanh::lean_inc(v_maxHeartbeats_5528_);
    leanh::lean_inc(v_initHeartbeats_5527_);
    leanh::lean_inc(v_openDecls_5526_);
    leanh::lean_inc(v_currNamespace_5525_);
    leanh::lean_inc(v_maxRecDepth_5523_);
    leanh::lean_inc(v_currRecDepth_5522_);
    leanh::lean_inc_ref(v_options_5521_);
    leanh::lean_inc_ref(v_fileMap_5520_);
    leanh::lean_inc_ref(v_fileName_5519_);
    v___x_5536_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_5536_, 0, v_fileName_5519_);
    leanh::lean_ctor_set(v___x_5536_, 1, v_fileMap_5520_);
    leanh::lean_ctor_set(v___x_5536_, 2, v_options_5521_);
    leanh::lean_ctor_set(v___x_5536_, 3, v_currRecDepth_5522_);
    leanh::lean_ctor_set(v___x_5536_, 4, v_maxRecDepth_5523_);
    leanh::lean_ctor_set(v___x_5536_, 5, v_ref_5535_);
    leanh::lean_ctor_set(v___x_5536_, 6, v_currNamespace_5525_);
    leanh::lean_ctor_set(v___x_5536_, 7, v_openDecls_5526_);
    leanh::lean_ctor_set(v___x_5536_, 8, v_initHeartbeats_5527_);
    leanh::lean_ctor_set(v___x_5536_, 9, v_maxHeartbeats_5528_);
    leanh::lean_ctor_set(v___x_5536_, 10, v_quotContext_5529_);
    leanh::lean_ctor_set(v___x_5536_, 11, v_currMacroScope_5530_);
    leanh::lean_ctor_set(v___x_5536_, 12, v_cancelTk_x3f_5532_);
    leanh::lean_ctor_set(v___x_5536_, 13, v_inheritedTraceOptions_5534_);
    leanh::lean_ctor_set_uint8(
        v___x_5536_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_5531_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_5536_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5533_,
    );
    v___x_5537_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___x_5536_, v___y_5517_);
    leanh::lean_dec_ref_known(v___x_5536_, 14);
    return v___x_5537_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg___boxed(
    mut v_ref_5538_: *mut leanh::LeanObject,
    mut v_msg_5539_: *mut leanh::LeanObject,
    mut v___y_5540_: *mut leanh::LeanObject,
    mut v___y_5541_: *mut leanh::LeanObject,
    mut v___y_5542_: *mut leanh::LeanObject,
    mut v___y_5543_: *mut leanh::LeanObject,
    mut v___y_5544_: *mut leanh::LeanObject,
    mut v___y_5545_: *mut leanh::LeanObject,
    mut v___y_5546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_5545_);
    leanh::lean_dec_ref(v___y_5544_);
    leanh::lean_dec(v___y_5543_);
    leanh::lean_dec_ref(v___y_5542_);
    leanh::lean_dec(v___y_5541_);
    leanh::lean_dec_ref(v___y_5540_);
    leanh::lean_dec(v_ref_5538_);
    return v_res_5547_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5549_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0;
    v___x_5550_ = l_Lean_stringToMessageData(v___x_5549_);
    return v___x_5550_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5552_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2;
    v___x_5553_ = l_Lean_stringToMessageData(v___x_5552_);
    return v___x_5553_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(
    mut v_item_5554_: *mut leanh::LeanObject,
    mut v_a_5555_: *mut leanh::LeanObject,
    mut v_a_5556_: *mut leanh::LeanObject,
    mut v_a_5557_: *mut leanh::LeanObject,
    mut v_a_5558_: *mut leanh::LeanObject,
    mut v_a_5559_: *mut leanh::LeanObject,
    mut v_a_5560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bool_x3f_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bool_x3f_5562_ = leanh::lean_ctor_get(v_item_5554_, 3);
    if leanh::lean_obj_tag(v_bool_x3f_5562_) == 0 {
        let mut v___x_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_item_5554_);
        v___x_5563_ = leanh::lean_box(0);
        v___x_5564_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5564_, 0, v___x_5563_);
        return v___x_5564_;
    } else {
        let mut v_option_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_origOptionName_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_option_5565_ = leanh::lean_ctor_get(v_item_5554_, 1);
        leanh::lean_inc(v_option_5565_);
        v_origOptionName_5566_ = leanh::lean_ctor_get(v_item_5554_, 4);
        leanh::lean_inc(v_origOptionName_5566_);
        leanh::lean_dec_ref(v_item_5554_);
        v___x_5567_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1_once
            ),
            _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1,
        );
        v___x_5568_ = l_Lean_MessageData_ofName(v_origOptionName_5566_);
        v___x_5569_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5569_, 0, v___x_5567_);
        leanh::lean_ctor_set(v___x_5569_, 1, v___x_5568_);
        v___x_5570_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3_once
            ),
            _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3,
        );
        v___x_5571_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5571_, 0, v___x_5569_);
        leanh::lean_ctor_set(v___x_5571_, 1, v___x_5570_);
        v___x_5572_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_5565_, v___x_5571_, v_a_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_);
        leanh::lean_dec(v_option_5565_);
        return v___x_5572_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___boxed(
    mut v_item_5573_: *mut leanh::LeanObject,
    mut v_a_5574_: *mut leanh::LeanObject,
    mut v_a_5575_: *mut leanh::LeanObject,
    mut v_a_5576_: *mut leanh::LeanObject,
    mut v_a_5577_: *mut leanh::LeanObject,
    mut v_a_5578_: *mut leanh::LeanObject,
    mut v_a_5579_: *mut leanh::LeanObject,
    mut v_a_5580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5581_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(
        v_item_5573_,
        v_a_5574_,
        v_a_5575_,
        v_a_5576_,
        v_a_5577_,
        v_a_5578_,
        v_a_5579_,
    );
    leanh::lean_dec(v_a_5579_);
    leanh::lean_dec_ref(v_a_5578_);
    leanh::lean_dec(v_a_5577_);
    leanh::lean_dec_ref(v_a_5576_);
    leanh::lean_dec(v_a_5575_);
    leanh::lean_dec_ref(v_a_5574_);
    return v_res_5581_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(
    mut v_00_u03b1_5582_: *mut leanh::LeanObject,
    mut v_ref_5583_: *mut leanh::LeanObject,
    mut v_msg_5584_: *mut leanh::LeanObject,
    mut v___y_5585_: *mut leanh::LeanObject,
    mut v___y_5586_: *mut leanh::LeanObject,
    mut v___y_5587_: *mut leanh::LeanObject,
    mut v___y_5588_: *mut leanh::LeanObject,
    mut v___y_5589_: *mut leanh::LeanObject,
    mut v___y_5590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5593_: *mut leanh::LeanObject,
    mut v_ref_5594_: *mut leanh::LeanObject,
    mut v_msg_5595_: *mut leanh::LeanObject,
    mut v___y_5596_: *mut leanh::LeanObject,
    mut v___y_5597_: *mut leanh::LeanObject,
    mut v___y_5598_: *mut leanh::LeanObject,
    mut v___y_5599_: *mut leanh::LeanObject,
    mut v___y_5600_: *mut leanh::LeanObject,
    mut v___y_5601_: *mut leanh::LeanObject,
    mut v___y_5602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_5601_);
    leanh::lean_dec_ref(v___y_5600_);
    leanh::lean_dec(v___y_5599_);
    leanh::lean_dec_ref(v___y_5598_);
    leanh::lean_dec(v___y_5597_);
    leanh::lean_dec_ref(v___y_5596_);
    leanh::lean_dec(v_ref_5594_);
    return v_res_5603_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(
    mut v_00_u03b1_5604_: *mut leanh::LeanObject,
    mut v_msg_5605_: *mut leanh::LeanObject,
    mut v___y_5606_: *mut leanh::LeanObject,
    mut v___y_5607_: *mut leanh::LeanObject,
    mut v___y_5608_: *mut leanh::LeanObject,
    mut v___y_5609_: *mut leanh::LeanObject,
    mut v___y_5610_: *mut leanh::LeanObject,
    mut v___y_5611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5613_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_);
    return v___x_5613_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___boxed(
    mut v_00_u03b1_5614_: *mut leanh::LeanObject,
    mut v_msg_5615_: *mut leanh::LeanObject,
    mut v___y_5616_: *mut leanh::LeanObject,
    mut v___y_5617_: *mut leanh::LeanObject,
    mut v___y_5618_: *mut leanh::LeanObject,
    mut v___y_5619_: *mut leanh::LeanObject,
    mut v___y_5620_: *mut leanh::LeanObject,
    mut v___y_5621_: *mut leanh::LeanObject,
    mut v___y_5622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5623_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(v_00_u03b1_5614_, v_msg_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
    leanh::lean_dec(v___y_5621_);
    leanh::lean_dec_ref(v___y_5620_);
    leanh::lean_dec(v___y_5619_);
    leanh::lean_dec_ref(v___y_5618_);
    leanh::lean_dec(v___y_5617_);
    leanh::lean_dec_ref(v___y_5616_);
    return v_res_5623_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(
    mut v_msgData_5624_: *mut leanh::LeanObject,
    mut v_macroStack_5625_: *mut leanh::LeanObject,
    mut v___y_5626_: *mut leanh::LeanObject,
    mut v___y_5627_: *mut leanh::LeanObject,
    mut v___y_5628_: *mut leanh::LeanObject,
    mut v___y_5629_: *mut leanh::LeanObject,
    mut v___y_5630_: *mut leanh::LeanObject,
    mut v___y_5631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5633_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_5624_, v_macroStack_5625_, v___y_5630_);
    return v___x_5633_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_5634_: *mut leanh::LeanObject,
    mut v_macroStack_5635_: *mut leanh::LeanObject,
    mut v___y_5636_: *mut leanh::LeanObject,
    mut v___y_5637_: *mut leanh::LeanObject,
    mut v___y_5638_: *mut leanh::LeanObject,
    mut v___y_5639_: *mut leanh::LeanObject,
    mut v___y_5640_: *mut leanh::LeanObject,
    mut v___y_5641_: *mut leanh::LeanObject,
    mut v___y_5642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5643_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(v_msgData_5634_, v_macroStack_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_);
    leanh::lean_dec(v___y_5641_);
    leanh::lean_dec_ref(v___y_5640_);
    leanh::lean_dec(v___y_5639_);
    leanh::lean_dec_ref(v___y_5638_);
    leanh::lean_dec(v___y_5637_);
    leanh::lean_dec_ref(v___y_5636_);
    return v_res_5643_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5645_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0;
    v___x_5646_ = l_Lean_stringToMessageData(v___x_5645_);
    return v___x_5646_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5648_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2;
    v___x_5649_ = l_Lean_stringToMessageData(v___x_5648_);
    return v___x_5649_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5651_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4;
    v___x_5652_ = l_Lean_stringToMessageData(v___x_5651_);
    return v___x_5652_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(
    mut v_item_5653_: *mut leanh::LeanObject,
    mut v_structName_x3f_5654_: *mut leanh::LeanObject,
    mut v_a_5655_: *mut leanh::LeanObject,
    mut v_a_5656_: *mut leanh::LeanObject,
    mut v_a_5657_: *mut leanh::LeanObject,
    mut v_a_5658_: *mut leanh::LeanObject,
    mut v_a_5659_: *mut leanh::LeanObject,
    mut v_a_5660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_option_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origOptionName_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: u8 = 0;
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: u8 = 0;
    let mut v___x_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_option_5662_ = leanh::lean_ctor_get(v_item_5653_, 1);
                leanh::lean_inc(v_option_5662_);
                v_origOptionName_5663_ = leanh::lean_ctor_get(v_item_5653_, 4);
                leanh::lean_inc(v_origOptionName_5663_);
                leanh::lean_dec_ref(v_item_5653_);
                v___x_5681_ = l_Lean_Name_isAnonymous(v_origOptionName_5663_);
                if v___x_5681_ == 0 {
                    v___x_5682_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
                    v___x_5683_ = l_Lean_MessageData_ofName(v_origOptionName_5663_);
                    v___x_5684_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5684_, 0, v___x_5682_);
                    leanh::lean_ctor_set(v___x_5684_, 1, v___x_5683_);
                    v___x_5685_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                    );
                    v___x_5686_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5686_, 0, v___x_5684_);
                    leanh::lean_ctor_set(v___x_5686_, 1, v___x_5685_);
                    v___y_5672_ = v___x_5686_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_origOptionName_5663_);
                    v___x_5687_ = leanh::lean_obj_once(
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
                v___x_5667_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1);
                v___x_5668_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5668_, 0, v___x_5667_);
                leanh::lean_ctor_set(v___x_5668_, 1, v___y_5665_);
                v___x_5669_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5669_, 0, v___x_5668_);
                leanh::lean_ctor_set(v___x_5669_, 1, v___y_5666_);
                v___x_5670_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_5662_, v___x_5669_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_);
                leanh::lean_dec(v_option_5662_);
                return v___x_5670_;
            }
            2 => {
                if leanh::lean_obj_tag(v_structName_x3f_5654_) == 1 {
                    v_val_5673_ = leanh::lean_ctor_get(v_structName_x3f_5654_, 0);
                    leanh::lean_inc(v_val_5673_);
                    leanh::lean_dec_ref_known(v_structName_x3f_5654_, 1);
                    v___x_5674_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
                    v___x_5675_ = 0;
                    v___x_5676_ = l_Lean_MessageData_ofConstName(v_val_5673_, v___x_5675_);
                    v___x_5677_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5677_, 0, v___x_5674_);
                    leanh::lean_ctor_set(v___x_5677_, 1, v___x_5676_);
                    v___x_5678_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                    );
                    v___x_5679_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5679_, 0, v___x_5677_);
                    leanh::lean_ctor_set(v___x_5679_, 1, v___x_5678_);
                    v___y_5665_ = v___y_5672_;
                    v___y_5666_ = v___x_5679_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_structName_x3f_5654_);
                    v___x_5680_ = leanh::lean_obj_once(
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
    mut v_item_5688_: *mut leanh::LeanObject,
    mut v_structName_x3f_5689_: *mut leanh::LeanObject,
    mut v_a_5690_: *mut leanh::LeanObject,
    mut v_a_5691_: *mut leanh::LeanObject,
    mut v_a_5692_: *mut leanh::LeanObject,
    mut v_a_5693_: *mut leanh::LeanObject,
    mut v_a_5694_: *mut leanh::LeanObject,
    mut v_a_5695_: *mut leanh::LeanObject,
    mut v_a_5696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_5695_);
    leanh::lean_dec_ref(v_a_5694_);
    leanh::lean_dec(v_a_5693_);
    leanh::lean_dec_ref(v_a_5692_);
    leanh::lean_dec(v_a_5691_);
    leanh::lean_dec_ref(v_a_5690_);
    return v_res_5697_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(
    mut v_00_u03b1_5698_: *mut leanh::LeanObject,
    mut v_item_5699_: *mut leanh::LeanObject,
    mut v_structName_x3f_5700_: *mut leanh::LeanObject,
    mut v_a_5701_: *mut leanh::LeanObject,
    mut v_a_5702_: *mut leanh::LeanObject,
    mut v_a_5703_: *mut leanh::LeanObject,
    mut v_a_5704_: *mut leanh::LeanObject,
    mut v_a_5705_: *mut leanh::LeanObject,
    mut v_a_5706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5709_: *mut leanh::LeanObject,
    mut v_item_5710_: *mut leanh::LeanObject,
    mut v_structName_x3f_5711_: *mut leanh::LeanObject,
    mut v_a_5712_: *mut leanh::LeanObject,
    mut v_a_5713_: *mut leanh::LeanObject,
    mut v_a_5714_: *mut leanh::LeanObject,
    mut v_a_5715_: *mut leanh::LeanObject,
    mut v_a_5716_: *mut leanh::LeanObject,
    mut v_a_5717_: *mut leanh::LeanObject,
    mut v_a_5718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_5717_);
    leanh::lean_dec_ref(v_a_5716_);
    leanh::lean_dec(v_a_5715_);
    leanh::lean_dec_ref(v_a_5714_);
    leanh::lean_dec(v_a_5713_);
    leanh::lean_dec_ref(v_a_5712_);
    return v_res_5719_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5721_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0;
    v___x_5722_ = l_Lean_stringToMessageData(v___x_5721_);
    return v___x_5722_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5724_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2;
    v___x_5725_ = l_Lean_stringToMessageData(v___x_5724_);
    return v___x_5725_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(
    mut v_item_5726_: *mut leanh::LeanObject,
    mut v_structName_x3f_5727_: *mut leanh::LeanObject,
    mut v_a_5728_: *mut leanh::LeanObject,
    mut v_a_5729_: *mut leanh::LeanObject,
    mut v_a_5730_: *mut leanh::LeanObject,
    mut v_a_5731_: *mut leanh::LeanObject,
    mut v_a_5732_: *mut leanh::LeanObject,
    mut v_a_5733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_option_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origOptionName_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: u8 = 0;
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: u8 = 0;
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_option_5735_ = leanh::lean_ctor_get(v_item_5726_, 1);
                leanh::lean_inc(v_option_5735_);
                v_origOptionName_5736_ = leanh::lean_ctor_get(v_item_5726_, 4);
                leanh::lean_inc(v_origOptionName_5736_);
                leanh::lean_dec_ref(v_item_5726_);
                v___x_5756_ = l_Lean_Name_isAnonymous(v_origOptionName_5736_);
                if v___x_5756_ == 0 {
                    v___x_5757_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
                    v___x_5758_ = l_Lean_MessageData_ofName(v_origOptionName_5736_);
                    v___x_5759_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5759_, 0, v___x_5757_);
                    leanh::lean_ctor_set(v___x_5759_, 1, v___x_5758_);
                    v___x_5760_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                    );
                    v___x_5761_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5761_, 0, v___x_5759_);
                    leanh::lean_ctor_set(v___x_5761_, 1, v___x_5760_);
                    v___y_5747_ = v___x_5761_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_origOptionName_5736_);
                    v___x_5762_ = leanh::lean_obj_once(
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
                v___x_5740_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1);
                v___x_5741_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5741_, 0, v___x_5740_);
                leanh::lean_ctor_set(v___x_5741_, 1, v___y_5738_);
                v___x_5742_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5742_, 0, v___x_5741_);
                leanh::lean_ctor_set(v___x_5742_, 1, v___y_5739_);
                v___x_5743_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3);
                v___x_5744_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5744_, 0, v___x_5742_);
                leanh::lean_ctor_set(v___x_5744_, 1, v___x_5743_);
                v___x_5745_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_5735_, v___x_5744_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_);
                leanh::lean_dec(v_option_5735_);
                return v___x_5745_;
            }
            2 => {
                if leanh::lean_obj_tag(v_structName_x3f_5727_) == 1 {
                    v_val_5748_ = leanh::lean_ctor_get(v_structName_x3f_5727_, 0);
                    leanh::lean_inc(v_val_5748_);
                    leanh::lean_dec_ref_known(v_structName_x3f_5727_, 1);
                    v___x_5749_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
                    v___x_5750_ = 0;
                    v___x_5751_ = l_Lean_MessageData_ofConstName(v_val_5748_, v___x_5750_);
                    v___x_5752_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5752_, 0, v___x_5749_);
                    leanh::lean_ctor_set(v___x_5752_, 1, v___x_5751_);
                    v___x_5753_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                    );
                    v___x_5754_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5754_, 0, v___x_5752_);
                    leanh::lean_ctor_set(v___x_5754_, 1, v___x_5753_);
                    v___y_5738_ = v___y_5747_;
                    v___y_5739_ = v___x_5754_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_structName_x3f_5727_);
                    v___x_5755_ = leanh::lean_obj_once(
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
    mut v_item_5763_: *mut leanh::LeanObject,
    mut v_structName_x3f_5764_: *mut leanh::LeanObject,
    mut v_a_5765_: *mut leanh::LeanObject,
    mut v_a_5766_: *mut leanh::LeanObject,
    mut v_a_5767_: *mut leanh::LeanObject,
    mut v_a_5768_: *mut leanh::LeanObject,
    mut v_a_5769_: *mut leanh::LeanObject,
    mut v_a_5770_: *mut leanh::LeanObject,
    mut v_a_5771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_5770_);
    leanh::lean_dec_ref(v_a_5769_);
    leanh::lean_dec(v_a_5768_);
    leanh::lean_dec_ref(v_a_5767_);
    leanh::lean_dec(v_a_5766_);
    leanh::lean_dec_ref(v_a_5765_);
    return v_res_5772_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(
    mut v_00_u03b1_5773_: *mut leanh::LeanObject,
    mut v_item_5774_: *mut leanh::LeanObject,
    mut v_structName_x3f_5775_: *mut leanh::LeanObject,
    mut v_a_5776_: *mut leanh::LeanObject,
    mut v_a_5777_: *mut leanh::LeanObject,
    mut v_a_5778_: *mut leanh::LeanObject,
    mut v_a_5779_: *mut leanh::LeanObject,
    mut v_a_5780_: *mut leanh::LeanObject,
    mut v_a_5781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5784_: *mut leanh::LeanObject,
    mut v_item_5785_: *mut leanh::LeanObject,
    mut v_structName_x3f_5786_: *mut leanh::LeanObject,
    mut v_a_5787_: *mut leanh::LeanObject,
    mut v_a_5788_: *mut leanh::LeanObject,
    mut v_a_5789_: *mut leanh::LeanObject,
    mut v_a_5790_: *mut leanh::LeanObject,
    mut v_a_5791_: *mut leanh::LeanObject,
    mut v_a_5792_: *mut leanh::LeanObject,
    mut v_a_5793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_5792_);
    leanh::lean_dec_ref(v_a_5791_);
    leanh::lean_dec(v_a_5790_);
    leanh::lean_dec_ref(v_a_5789_);
    leanh::lean_dec(v_a_5788_);
    leanh::lean_dec_ref(v_a_5787_);
    return v_res_5794_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5795_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5795_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5796_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
    v___x_5797_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5797_, 0, v___x_5796_);
    return v___x_5797_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5798_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_5799_ = leanh::lean_unsigned_to_nat(0);
    v___x_5800_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_5800_, 0, v___x_5799_);
    leanh::lean_ctor_set(v___x_5800_, 1, v___x_5799_);
    leanh::lean_ctor_set(v___x_5800_, 2, v___x_5799_);
    leanh::lean_ctor_set(v___x_5800_, 3, v___x_5799_);
    leanh::lean_ctor_set(v___x_5800_, 4, v___x_5798_);
    leanh::lean_ctor_set(v___x_5800_, 5, v___x_5798_);
    leanh::lean_ctor_set(v___x_5800_, 6, v___x_5798_);
    leanh::lean_ctor_set(v___x_5800_, 7, v___x_5798_);
    leanh::lean_ctor_set(v___x_5800_, 8, v___x_5798_);
    leanh::lean_ctor_set(v___x_5800_, 9, v___x_5798_);
    return v___x_5800_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5801_ = leanh::lean_unsigned_to_nat(32);
    v___x_5802_ = lean_mk_empty_array_with_capacity(v___x_5801_);
    v___x_5803_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5803_, 0, v___x_5802_);
    return v___x_5803_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5804_: usize = 0;
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5804_ = 5usize;
    v___x_5805_ = leanh::lean_unsigned_to_nat(0);
    v___x_5806_ = leanh::lean_unsigned_to_nat(32);
    v___x_5807_ = lean_mk_empty_array_with_capacity(v___x_5806_);
    v___x_5808_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
    v___x_5809_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_5809_, 0, v___x_5808_);
    leanh::lean_ctor_set(v___x_5809_, 1, v___x_5807_);
    leanh::lean_ctor_set(v___x_5809_, 2, v___x_5805_);
    leanh::lean_ctor_set(v___x_5809_, 3, v___x_5805_);
    leanh::lean_ctor_set_usize(v___x_5809_, 4, v___x_5804_);
    return v___x_5809_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5810_ = leanh::lean_box(1);
    v___x_5811_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_5812_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_5813_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_5813_, 0, v___x_5812_);
    leanh::lean_ctor_set(v___x_5813_, 1, v___x_5811_);
    leanh::lean_ctor_set(v___x_5813_, 2, v___x_5810_);
    return v___x_5813_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5815_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_5816_ = l_Lean_stringToMessageData(v___x_5815_);
    return v___x_5816_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5818_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_5819_ = l_Lean_stringToMessageData(v___x_5818_);
    return v___x_5819_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5821_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_5822_ = l_Lean_stringToMessageData(v___x_5821_);
    return v___x_5822_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5824_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_5825_ = l_Lean_stringToMessageData(v___x_5824_);
    return v___x_5825_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14;
    v___x_5828_ = l_Lean_stringToMessageData(v___x_5827_);
    return v___x_5828_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5830_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16;
    v___x_5831_ = l_Lean_stringToMessageData(v___x_5830_);
    return v___x_5831_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5833_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18;
    v___x_5834_ = l_Lean_stringToMessageData(v___x_5833_);
    return v___x_5834_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(
    mut v_msg_5835_: *mut leanh::LeanObject,
    mut v_declHint_5836_: *mut leanh::LeanObject,
    mut v___y_5837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: u8 = 0;
    let mut v_isExporting_5842_: u8 = 0;
    let mut v___x_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: u8 = 0;
    let mut v___x_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5864_: u8 = 0;
    let mut v___x_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: u8 = 0;
    let mut v___x_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5896_: u8 = 0;
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5839_ = lean_st_ref_get(v___y_5837_);
                v_env_5840_ = leanh::lean_ctor_get(v___x_5839_, 0);
                leanh::lean_inc_ref(v_env_5840_);
                leanh::lean_dec(v___x_5839_);
                v___x_5841_ = l_Lean_Name_isAnonymous(v_declHint_5836_);
                if v___x_5841_ == 0 {
                    v_isExporting_5842_ = leanh::lean_ctor_get_uint8(
                        v_env_5840_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5842_ == 0 {
                        leanh::lean_dec_ref(v_env_5840_);
                        leanh::lean_dec(v_declHint_5836_);
                        v___x_5843_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5843_, 0, v_msg_5835_);
                        return v___x_5843_;
                    } else {
                        leanh::lean_inc_ref(v_env_5840_);
                        v___x_5844_ = l_Lean_Environment_setExporting(v_env_5840_, v___x_5841_);
                        leanh::lean_inc(v_declHint_5836_);
                        leanh::lean_inc_ref(v___x_5844_);
                        v___x_5845_ = l_Lean_Environment_contains(
                            v___x_5844_,
                            v_declHint_5836_,
                            v_isExporting_5842_,
                        );
                        if v___x_5845_ == 0 {
                            leanh::lean_dec_ref(v___x_5844_);
                            leanh::lean_dec_ref(v_env_5840_);
                            leanh::lean_dec(v_declHint_5836_);
                            v___x_5846_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5846_, 0, v_msg_5835_);
                            return v___x_5846_;
                        } else {
                            v___x_5847_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
                            v___x_5848_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
                            v___x_5849_ = l_Lean_Options_empty;
                            v___x_5850_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_5850_, 0, v___x_5844_);
                            leanh::lean_ctor_set(v___x_5850_, 1, v___x_5847_);
                            leanh::lean_ctor_set(v___x_5850_, 2, v___x_5848_);
                            leanh::lean_ctor_set(v___x_5850_, 3, v___x_5849_);
                            leanh::lean_inc(v_declHint_5836_);
                            v___x_5851_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5836_, v___x_5841_);
                            v_c_5852_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_5852_, 0, v___x_5850_);
                            leanh::lean_ctor_set(v_c_5852_, 1, v___x_5851_);
                            v___x_5853_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5840_,
                                v_declHint_5836_,
                            );
                            if leanh::lean_obj_tag(v___x_5853_) == 0 {
                                leanh::lean_dec_ref(v_env_5840_);
                                leanh::lean_dec(v_declHint_5836_);
                                v___x_5854_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
                                v___x_5855_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5855_, 0, v___x_5854_);
                                leanh::lean_ctor_set(v___x_5855_, 1, v_c_5852_);
                                v___x_5856_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
                                v___x_5857_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5857_, 0, v___x_5855_);
                                leanh::lean_ctor_set(v___x_5857_, 1, v___x_5856_);
                                v___x_5858_ = l_Lean_MessageData_note(v___x_5857_);
                                v___x_5859_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5859_, 0, v_msg_5835_);
                                leanh::lean_ctor_set(v___x_5859_, 1, v___x_5858_);
                                v___x_5860_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_5860_, 0, v___x_5859_);
                                return v___x_5860_;
                            } else {
                                v_val_5861_ = leanh::lean_ctor_get(v___x_5853_, 0);
                                v_isSharedCheck_5896_ =
                                    (!leanh::lean_is_exclusive(v___x_5853_)) as u8;
                                if v_isSharedCheck_5896_ == 0 {
                                    v___x_5863_ = v___x_5853_;
                                    v_isShared_5864_ = v_isSharedCheck_5896_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_5861_);
                                    leanh::lean_dec(v___x_5853_);
                                    v___x_5863_ = leanh::lean_box(0);
                                    v_isShared_5864_ = v_isSharedCheck_5896_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_5840_);
                    leanh::lean_dec(v_declHint_5836_);
                    v___x_5897_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5897_, 0, v_msg_5835_);
                    return v___x_5897_;
                }
            }
            1 => {
                v___x_5865_ = leanh::lean_box(0);
                v___x_5866_ = l_Lean_Environment_header(v_env_5840_);
                leanh::lean_dec_ref(v_env_5840_);
                v___x_5867_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5866_);
                v_mod_5868_ = lean_array_get(v___x_5865_, v___x_5867_, v_val_5861_);
                leanh::lean_dec(v_val_5861_);
                leanh::lean_dec_ref(v___x_5867_);
                v___x_5869_ = l_Lean_isPrivateName(v_declHint_5836_);
                leanh::lean_dec(v_declHint_5836_);
                if v___x_5869_ == 0 {
                    v___x_5870_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_5871_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5871_, 0, v___x_5870_);
                    leanh::lean_ctor_set(v___x_5871_, 1, v_c_5852_);
                    v___x_5872_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_5873_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5873_, 0, v___x_5871_);
                    leanh::lean_ctor_set(v___x_5873_, 1, v___x_5872_);
                    v___x_5874_ = l_Lean_MessageData_ofName(v_mod_5868_);
                    v___x_5875_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5875_, 0, v___x_5873_);
                    leanh::lean_ctor_set(v___x_5875_, 1, v___x_5874_);
                    v___x_5876_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
                    v___x_5877_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5877_, 0, v___x_5875_);
                    leanh::lean_ctor_set(v___x_5877_, 1, v___x_5876_);
                    v___x_5878_ = l_Lean_MessageData_note(v___x_5877_);
                    v___x_5879_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5879_, 0, v_msg_5835_);
                    leanh::lean_ctor_set(v___x_5879_, 1, v___x_5878_);
                    if v_isShared_5864_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5863_, 0);
                        leanh::lean_ctor_set(v___x_5863_, 0, v___x_5879_);
                        v___x_5881_ = v___x_5863_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5882_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5882_, 0, v___x_5879_);
                        v___x_5881_ = v_reuseFailAlloc_5882_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5883_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_5884_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5884_, 0, v___x_5883_);
                    leanh::lean_ctor_set(v___x_5884_, 1, v_c_5852_);
                    v___x_5885_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
                    v___x_5886_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5886_, 0, v___x_5884_);
                    leanh::lean_ctor_set(v___x_5886_, 1, v___x_5885_);
                    v___x_5887_ = l_Lean_MessageData_ofName(v_mod_5868_);
                    v___x_5888_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5888_, 0, v___x_5886_);
                    leanh::lean_ctor_set(v___x_5888_, 1, v___x_5887_);
                    v___x_5889_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
                    v___x_5890_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5890_, 0, v___x_5888_);
                    leanh::lean_ctor_set(v___x_5890_, 1, v___x_5889_);
                    v___x_5891_ = l_Lean_MessageData_note(v___x_5890_);
                    v___x_5892_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5892_, 0, v_msg_5835_);
                    leanh::lean_ctor_set(v___x_5892_, 1, v___x_5891_);
                    if v_isShared_5864_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5863_, 0);
                        leanh::lean_ctor_set(v___x_5863_, 0, v___x_5892_);
                        v___x_5894_ = v___x_5863_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5895_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5895_, 0, v___x_5892_);
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
    mut v_msg_5898_: *mut leanh::LeanObject,
    mut v_declHint_5899_: *mut leanh::LeanObject,
    mut v___y_5900_: *mut leanh::LeanObject,
    mut v___y_5901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5902_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_5898_, v_declHint_5899_, v___y_5900_);
    leanh::lean_dec(v___y_5900_);
    return v_res_5902_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(
    mut v_msg_5903_: *mut leanh::LeanObject,
    mut v_declHint_5904_: *mut leanh::LeanObject,
    mut v___y_5905_: *mut leanh::LeanObject,
    mut v___y_5906_: *mut leanh::LeanObject,
    mut v___y_5907_: *mut leanh::LeanObject,
    mut v___y_5908_: *mut leanh::LeanObject,
    mut v___y_5909_: *mut leanh::LeanObject,
    mut v___y_5910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5912_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_5903_, v_declHint_5904_, v___y_5910_);
                v_a_5913_ = leanh::lean_ctor_get(v___x_5912_, 0);
                v_isSharedCheck_5922_ = (!leanh::lean_is_exclusive(v___x_5912_)) as u8;
                if v_isSharedCheck_5922_ == 0 {
                    v___x_5915_ = v___x_5912_;
                    v_isShared_5916_ = v_isSharedCheck_5922_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5913_);
                    leanh::lean_dec(v___x_5912_);
                    v___x_5915_ = leanh::lean_box(0);
                    v_isShared_5916_ = v_isSharedCheck_5922_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5917_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5918_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5918_, 0, v___x_5917_);
                leanh::lean_ctor_set(v___x_5918_, 1, v_a_5913_);
                if v_isShared_5916_ == 0 {
                    leanh::lean_ctor_set(v___x_5915_, 0, v___x_5918_);
                    v___x_5920_ = v___x_5915_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5921_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5921_, 0, v___x_5918_);
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
    mut v_msg_5923_: *mut leanh::LeanObject,
    mut v_declHint_5924_: *mut leanh::LeanObject,
    mut v___y_5925_: *mut leanh::LeanObject,
    mut v___y_5926_: *mut leanh::LeanObject,
    mut v___y_5927_: *mut leanh::LeanObject,
    mut v___y_5928_: *mut leanh::LeanObject,
    mut v___y_5929_: *mut leanh::LeanObject,
    mut v___y_5930_: *mut leanh::LeanObject,
    mut v___y_5931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5932_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_5923_, v_declHint_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_);
    leanh::lean_dec(v___y_5930_);
    leanh::lean_dec_ref(v___y_5929_);
    leanh::lean_dec(v___y_5928_);
    leanh::lean_dec_ref(v___y_5927_);
    leanh::lean_dec(v___y_5926_);
    leanh::lean_dec_ref(v___y_5925_);
    return v_res_5932_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(
    mut v_ref_5933_: *mut leanh::LeanObject,
    mut v_msg_5934_: *mut leanh::LeanObject,
    mut v_declHint_5935_: *mut leanh::LeanObject,
    mut v___y_5936_: *mut leanh::LeanObject,
    mut v___y_5937_: *mut leanh::LeanObject,
    mut v___y_5938_: *mut leanh::LeanObject,
    mut v___y_5939_: *mut leanh::LeanObject,
    mut v___y_5940_: *mut leanh::LeanObject,
    mut v___y_5941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5943_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_5934_, v_declHint_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_);
    v_a_5944_ = leanh::lean_ctor_get(v___x_5943_, 0);
    leanh::lean_inc(v_a_5944_);
    leanh::lean_dec_ref(v___x_5943_);
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
    mut v_ref_5946_: *mut leanh::LeanObject,
    mut v_msg_5947_: *mut leanh::LeanObject,
    mut v_declHint_5948_: *mut leanh::LeanObject,
    mut v___y_5949_: *mut leanh::LeanObject,
    mut v___y_5950_: *mut leanh::LeanObject,
    mut v___y_5951_: *mut leanh::LeanObject,
    mut v___y_5952_: *mut leanh::LeanObject,
    mut v___y_5953_: *mut leanh::LeanObject,
    mut v___y_5954_: *mut leanh::LeanObject,
    mut v___y_5955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5956_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_5946_, v_msg_5947_, v_declHint_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
    leanh::lean_dec(v___y_5954_);
    leanh::lean_dec_ref(v___y_5953_);
    leanh::lean_dec(v___y_5952_);
    leanh::lean_dec_ref(v___y_5951_);
    leanh::lean_dec(v___y_5950_);
    leanh::lean_dec_ref(v___y_5949_);
    leanh::lean_dec(v_ref_5946_);
    return v_res_5956_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5958_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0;
    v___x_5959_ = l_Lean_stringToMessageData(v___x_5958_);
    return v___x_5959_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_ref_5960_: *mut leanh::LeanObject,
    mut v_constName_5961_: *mut leanh::LeanObject,
    mut v___y_5962_: *mut leanh::LeanObject,
    mut v___y_5963_: *mut leanh::LeanObject,
    mut v___y_5964_: *mut leanh::LeanObject,
    mut v___y_5965_: *mut leanh::LeanObject,
    mut v___y_5966_: *mut leanh::LeanObject,
    mut v___y_5967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: u8 = 0;
    let mut v___x_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5969_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
    v___x_5970_ = 0;
    leanh::lean_inc(v_constName_5961_);
    v___x_5971_ = l_Lean_MessageData_ofConstName(v_constName_5961_, v___x_5970_);
    v___x_5972_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5972_, 0, v___x_5969_);
    leanh::lean_ctor_set(v___x_5972_, 1, v___x_5971_);
    v___x_5973_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
    );
    v___x_5974_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5974_, 0, v___x_5972_);
    leanh::lean_ctor_set(v___x_5974_, 1, v___x_5973_);
    v___x_5975_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_5960_, v___x_5974_, v_constName_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_);
    return v___x_5975_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_ref_5976_: *mut leanh::LeanObject,
    mut v_constName_5977_: *mut leanh::LeanObject,
    mut v___y_5978_: *mut leanh::LeanObject,
    mut v___y_5979_: *mut leanh::LeanObject,
    mut v___y_5980_: *mut leanh::LeanObject,
    mut v___y_5981_: *mut leanh::LeanObject,
    mut v___y_5982_: *mut leanh::LeanObject,
    mut v___y_5983_: *mut leanh::LeanObject,
    mut v___y_5984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5985_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_5976_, v_constName_5977_, v___y_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
    leanh::lean_dec(v___y_5983_);
    leanh::lean_dec_ref(v___y_5982_);
    leanh::lean_dec(v___y_5981_);
    leanh::lean_dec_ref(v___y_5980_);
    leanh::lean_dec(v___y_5979_);
    leanh::lean_dec_ref(v___y_5978_);
    leanh::lean_dec(v_ref_5976_);
    return v_res_5985_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_constName_5986_: *mut leanh::LeanObject,
    mut v___y_5987_: *mut leanh::LeanObject,
    mut v___y_5988_: *mut leanh::LeanObject,
    mut v___y_5989_: *mut leanh::LeanObject,
    mut v___y_5990_: *mut leanh::LeanObject,
    mut v___y_5991_: *mut leanh::LeanObject,
    mut v___y_5992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_5994_ = leanh::lean_ctor_get(v___y_5991_, 5);
    v___x_5995_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_5994_, v_constName_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_);
    return v___x_5995_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_constName_5996_: *mut leanh::LeanObject,
    mut v___y_5997_: *mut leanh::LeanObject,
    mut v___y_5998_: *mut leanh::LeanObject,
    mut v___y_5999_: *mut leanh::LeanObject,
    mut v___y_6000_: *mut leanh::LeanObject,
    mut v___y_6001_: *mut leanh::LeanObject,
    mut v___y_6002_: *mut leanh::LeanObject,
    mut v___y_6003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6004_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_);
    leanh::lean_dec(v___y_6002_);
    leanh::lean_dec_ref(v___y_6001_);
    leanh::lean_dec(v___y_6000_);
    leanh::lean_dec_ref(v___y_5999_);
    leanh::lean_dec(v___y_5998_);
    leanh::lean_dec_ref(v___y_5997_);
    return v_res_6004_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(
    mut v_constName_6005_: *mut leanh::LeanObject,
    mut v___y_6006_: *mut leanh::LeanObject,
    mut v___y_6007_: *mut leanh::LeanObject,
    mut v___y_6008_: *mut leanh::LeanObject,
    mut v___y_6009_: *mut leanh::LeanObject,
    mut v___y_6010_: *mut leanh::LeanObject,
    mut v___y_6011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: u8 = 0;
    let mut v___x_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6021_: u8 = 0;
    let mut v___x_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6013_ = lean_st_ref_get(v___y_6011_);
                v_env_6014_ = leanh::lean_ctor_get(v___x_6013_, 0);
                leanh::lean_inc_ref(v_env_6014_);
                leanh::lean_dec(v___x_6013_);
                v___x_6015_ = 0;
                leanh::lean_inc(v_constName_6005_);
                v___x_6016_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_6014_,
                    v_constName_6005_,
                    v___x_6015_,
                );
                if leanh::lean_obj_tag(v___x_6016_) == 0 {
                    v___x_6017_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_);
                    return v___x_6017_;
                } else {
                    leanh::lean_dec(v_constName_6005_);
                    v_val_6018_ = leanh::lean_ctor_get(v___x_6016_, 0);
                    v_isSharedCheck_6025_ = (!leanh::lean_is_exclusive(v___x_6016_)) as u8;
                    if v_isSharedCheck_6025_ == 0 {
                        v___x_6020_ = v___x_6016_;
                        v_isShared_6021_ = v_isSharedCheck_6025_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6018_);
                        leanh::lean_dec(v___x_6016_);
                        v___x_6020_ = leanh::lean_box(0);
                        v_isShared_6021_ = v_isSharedCheck_6025_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6021_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6020_, 0);
                    v___x_6023_ = v___x_6020_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6024_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6024_, 0, v_val_6018_);
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
    mut v_constName_6026_: *mut leanh::LeanObject,
    mut v___y_6027_: *mut leanh::LeanObject,
    mut v___y_6028_: *mut leanh::LeanObject,
    mut v___y_6029_: *mut leanh::LeanObject,
    mut v___y_6030_: *mut leanh::LeanObject,
    mut v___y_6031_: *mut leanh::LeanObject,
    mut v___y_6032_: *mut leanh::LeanObject,
    mut v___y_6033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6034_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_);
    leanh::lean_dec(v___y_6032_);
    leanh::lean_dec_ref(v___y_6031_);
    leanh::lean_dec(v___y_6030_);
    leanh::lean_dec_ref(v___y_6029_);
    leanh::lean_dec(v___y_6028_);
    leanh::lean_dec_ref(v___y_6027_);
    return v_res_6034_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(
    mut v_a_6035_: *mut leanh::LeanObject,
    mut v_a_6036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6042_: u8 = 0;
    let mut v___x_6043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6048_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6035_) == 0 {
                    v___x_6037_ = l_List_reverse___redArg(v_a_6036_);
                    return v___x_6037_;
                } else {
                    v_head_6038_ = leanh::lean_ctor_get(v_a_6035_, 0);
                    v_tail_6039_ = leanh::lean_ctor_get(v_a_6035_, 1);
                    v_isSharedCheck_6048_ = (!leanh::lean_is_exclusive(v_a_6035_)) as u8;
                    if v_isSharedCheck_6048_ == 0 {
                        v___x_6041_ = v_a_6035_;
                        v_isShared_6042_ = v_isSharedCheck_6048_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6039_);
                        leanh::lean_inc(v_head_6038_);
                        leanh::lean_dec(v_a_6035_);
                        v___x_6041_ = leanh::lean_box(0);
                        v_isShared_6042_ = v_isSharedCheck_6048_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6043_ = l_Lean_mkLevelParam(v_head_6038_);
                if v_isShared_6042_ == 0 {
                    leanh::lean_ctor_set(v___x_6041_, 1, v_a_6036_);
                    leanh::lean_ctor_set(v___x_6041_, 0, v___x_6043_);
                    v___x_6045_ = v___x_6041_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6047_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6047_, 0, v___x_6043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6047_, 1, v_a_6036_);
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
    mut v_constName_6049_: *mut leanh::LeanObject,
    mut v___y_6050_: *mut leanh::LeanObject,
    mut v___y_6051_: *mut leanh::LeanObject,
    mut v___y_6052_: *mut leanh::LeanObject,
    mut v___y_6053_: *mut leanh::LeanObject,
    mut v___y_6054_: *mut leanh::LeanObject,
    mut v___y_6055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6061_: u8 = 0;
    let mut v_levelParams_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6069_: u8 = 0;
    let mut v_a_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6073_: u8 = 0;
    let mut v___x_6075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_constName_6049_);
                v___x_6057_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_);
                if leanh::lean_obj_tag(v___x_6057_) == 0 {
                    v_a_6058_ = leanh::lean_ctor_get(v___x_6057_, 0);
                    v_isSharedCheck_6069_ = (!leanh::lean_is_exclusive(v___x_6057_)) as u8;
                    if v_isSharedCheck_6069_ == 0 {
                        v___x_6060_ = v___x_6057_;
                        v_isShared_6061_ = v_isSharedCheck_6069_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6058_);
                        leanh::lean_dec(v___x_6057_);
                        v___x_6060_ = leanh::lean_box(0);
                        v_isShared_6061_ = v_isSharedCheck_6069_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_constName_6049_);
                    v_a_6070_ = leanh::lean_ctor_get(v___x_6057_, 0);
                    v_isSharedCheck_6077_ = (!leanh::lean_is_exclusive(v___x_6057_)) as u8;
                    if v_isSharedCheck_6077_ == 0 {
                        v___x_6072_ = v___x_6057_;
                        v_isShared_6073_ = v_isSharedCheck_6077_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6070_);
                        leanh::lean_dec(v___x_6057_);
                        v___x_6072_ = leanh::lean_box(0);
                        v_isShared_6073_ = v_isSharedCheck_6077_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_6062_ = leanh::lean_ctor_get(v_a_6058_, 1);
                leanh::lean_inc(v_levelParams_6062_);
                leanh::lean_dec(v_a_6058_);
                v___x_6063_ = leanh::lean_box(0);
                v___x_6064_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(v_levelParams_6062_, v___x_6063_);
                v___x_6065_ = l_Lean_mkConst(v_constName_6049_, v___x_6064_);
                if v_isShared_6061_ == 0 {
                    leanh::lean_ctor_set(v___x_6060_, 0, v___x_6065_);
                    v___x_6067_ = v___x_6060_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6068_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6068_, 0, v___x_6065_);
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
                    v_reuseFailAlloc_6076_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6076_, 0, v_a_6070_);
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
    mut v_constName_6078_: *mut leanh::LeanObject,
    mut v___y_6079_: *mut leanh::LeanObject,
    mut v___y_6080_: *mut leanh::LeanObject,
    mut v___y_6081_: *mut leanh::LeanObject,
    mut v___y_6082_: *mut leanh::LeanObject,
    mut v___y_6083_: *mut leanh::LeanObject,
    mut v___y_6084_: *mut leanh::LeanObject,
    mut v___y_6085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6086_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_constName_6078_, v___y_6079_, v___y_6080_, v___y_6081_, v___y_6082_, v___y_6083_, v___y_6084_);
    leanh::lean_dec(v___y_6084_);
    leanh::lean_dec_ref(v___y_6083_);
    leanh::lean_dec(v___y_6082_);
    leanh::lean_dec_ref(v___y_6081_);
    leanh::lean_dec(v___y_6080_);
    leanh::lean_dec_ref(v___y_6079_);
    return v_res_6086_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(
    mut v_t_6087_: *mut leanh::LeanObject,
    mut v___y_6088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6092_: u8 = 0;
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6107_: u8 = 0;
    let mut v_enabled_6108_: u8 = 0;
    let mut v_assignment_6109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6114_: u8 = 0;
    let mut v___x_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6125_: u8 = 0;
    let mut v_isSharedCheck_6126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6090_ = lean_st_ref_get(v___y_6088_);
                v_infoState_6091_ = leanh::lean_ctor_get(v___x_6090_, 7);
                leanh::lean_inc_ref(v_infoState_6091_);
                leanh::lean_dec(v___x_6090_);
                v_enabled_6092_ = leanh::lean_ctor_get_uint8(
                    v_infoState_6091_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_6091_);
                if v_enabled_6092_ == 0 {
                    leanh::lean_dec_ref(v_t_6087_);
                    v___x_6093_ = leanh::lean_box(0);
                    v___x_6094_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6094_, 0, v___x_6093_);
                    return v___x_6094_;
                } else {
                    v___x_6095_ = lean_st_ref_take(v___y_6088_);
                    v_infoState_6096_ = leanh::lean_ctor_get(v___x_6095_, 7);
                    v_env_6097_ = leanh::lean_ctor_get(v___x_6095_, 0);
                    v_nextMacroScope_6098_ = leanh::lean_ctor_get(v___x_6095_, 1);
                    v_ngen_6099_ = leanh::lean_ctor_get(v___x_6095_, 2);
                    v_auxDeclNGen_6100_ = leanh::lean_ctor_get(v___x_6095_, 3);
                    v_traceState_6101_ = leanh::lean_ctor_get(v___x_6095_, 4);
                    v_cache_6102_ = leanh::lean_ctor_get(v___x_6095_, 5);
                    v_messages_6103_ = leanh::lean_ctor_get(v___x_6095_, 6);
                    v_snapshotTasks_6104_ = leanh::lean_ctor_get(v___x_6095_, 8);
                    v_isSharedCheck_6126_ = (!leanh::lean_is_exclusive(v___x_6095_)) as u8;
                    if v_isSharedCheck_6126_ == 0 {
                        v___x_6106_ = v___x_6095_;
                        v_isShared_6107_ = v_isSharedCheck_6126_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_6104_);
                        leanh::lean_inc(v_infoState_6096_);
                        leanh::lean_inc(v_messages_6103_);
                        leanh::lean_inc(v_cache_6102_);
                        leanh::lean_inc(v_traceState_6101_);
                        leanh::lean_inc(v_auxDeclNGen_6100_);
                        leanh::lean_inc(v_ngen_6099_);
                        leanh::lean_inc(v_nextMacroScope_6098_);
                        leanh::lean_inc(v_env_6097_);
                        leanh::lean_dec(v___x_6095_);
                        v___x_6106_ = leanh::lean_box(0);
                        v_isShared_6107_ = v_isSharedCheck_6126_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_6108_ = leanh::lean_ctor_get_uint8(
                    v_infoState_6096_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_6109_ = leanh::lean_ctor_get(v_infoState_6096_, 0);
                v_lazyAssignment_6110_ = leanh::lean_ctor_get(v_infoState_6096_, 1);
                v_trees_6111_ = leanh::lean_ctor_get(v_infoState_6096_, 2);
                v_isSharedCheck_6125_ = (!leanh::lean_is_exclusive(v_infoState_6096_)) as u8;
                if v_isSharedCheck_6125_ == 0 {
                    v___x_6113_ = v_infoState_6096_;
                    v_isShared_6114_ = v_isSharedCheck_6125_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_trees_6111_);
                    leanh::lean_inc(v_lazyAssignment_6110_);
                    leanh::lean_inc(v_assignment_6109_);
                    leanh::lean_dec(v_infoState_6096_);
                    v___x_6113_ = leanh::lean_box(0);
                    v_isShared_6114_ = v_isSharedCheck_6125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6115_ = l_Lean_PersistentArray_push___redArg(v_trees_6111_, v_t_6087_);
                if v_isShared_6114_ == 0 {
                    leanh::lean_ctor_set(v___x_6113_, 2, v___x_6115_);
                    v___x_6117_ = v___x_6113_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6124_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_assignment_6109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6124_, 1, v_lazyAssignment_6110_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6124_, 2, v___x_6115_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6124_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_6108_,
                    );
                    v___x_6117_ = v_reuseFailAlloc_6124_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6107_ == 0 {
                    leanh::lean_ctor_set(v___x_6106_, 7, v___x_6117_);
                    v___x_6119_ = v___x_6106_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6123_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 0, v_env_6097_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 1, v_nextMacroScope_6098_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 2, v_ngen_6099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 3, v_auxDeclNGen_6100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 4, v_traceState_6101_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 5, v_cache_6102_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 6, v_messages_6103_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 7, v___x_6117_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6123_, 8, v_snapshotTasks_6104_);
                    v___x_6119_ = v_reuseFailAlloc_6123_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6120_ = lean_st_ref_set(v___y_6088_, v___x_6119_);
                v___x_6121_ = leanh::lean_box(0);
                v___x_6122_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6122_, 0, v___x_6121_);
                return v___x_6122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_t_6127_: *mut leanh::LeanObject,
    mut v___y_6128_: *mut leanh::LeanObject,
    mut v___y_6129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6130_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_6127_, v___y_6128_);
    leanh::lean_dec(v___y_6128_);
    return v_res_6130_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6131_ = leanh::lean_unsigned_to_nat(32);
    v___x_6132_ = lean_mk_empty_array_with_capacity(v___x_6131_);
    v___x_6133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6133_, 0, v___x_6132_);
    return v___x_6133_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6134_: usize = 0;
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6134_ = 5usize;
    v___x_6135_ = leanh::lean_unsigned_to_nat(0);
    v___x_6136_ = leanh::lean_unsigned_to_nat(32);
    v___x_6137_ = lean_mk_empty_array_with_capacity(v___x_6136_);
    v___x_6138_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0);
    v___x_6139_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_6139_, 0, v___x_6138_);
    leanh::lean_ctor_set(v___x_6139_, 1, v___x_6137_);
    leanh::lean_ctor_set(v___x_6139_, 2, v___x_6135_);
    leanh::lean_ctor_set(v___x_6139_, 3, v___x_6135_);
    leanh::lean_ctor_set_usize(v___x_6139_, 4, v___x_6134_);
    return v___x_6139_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(
    mut v_t_6140_: *mut leanh::LeanObject,
    mut v___y_6141_: *mut leanh::LeanObject,
    mut v___y_6142_: *mut leanh::LeanObject,
    mut v___y_6143_: *mut leanh::LeanObject,
    mut v___y_6144_: *mut leanh::LeanObject,
    mut v___y_6145_: *mut leanh::LeanObject,
    mut v___y_6146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6150_: u8 = 0;
    v___x_6148_ = lean_st_ref_get(v___y_6146_);
    v_infoState_6149_ = leanh::lean_ctor_get(v___x_6148_, 7);
    leanh::lean_inc_ref(v_infoState_6149_);
    leanh::lean_dec(v___x_6148_);
    v_enabled_6150_ = leanh::lean_ctor_get_uint8(
        v_infoState_6149_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    leanh::lean_dec_ref(v_infoState_6149_);
    if v_enabled_6150_ == 0 {
        let mut v___x_6151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_t_6140_);
        v___x_6151_ = leanh::lean_box(0);
        v___x_6152_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6152_, 0, v___x_6151_);
        return v___x_6152_;
    } else {
        let mut v___x_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6153_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
        v___x_6154_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_6154_, 0, v_t_6140_);
        leanh::lean_ctor_set(v___x_6154_, 1, v___x_6153_);
        v___x_6155_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v___x_6154_, v___y_6146_);
        return v___x_6155_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___boxed(
    mut v_t_6156_: *mut leanh::LeanObject,
    mut v___y_6157_: *mut leanh::LeanObject,
    mut v___y_6158_: *mut leanh::LeanObject,
    mut v___y_6159_: *mut leanh::LeanObject,
    mut v___y_6160_: *mut leanh::LeanObject,
    mut v___y_6161_: *mut leanh::LeanObject,
    mut v___y_6162_: *mut leanh::LeanObject,
    mut v___y_6163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6164_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v_t_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_);
    leanh::lean_dec(v___y_6162_);
    leanh::lean_dec_ref(v___y_6161_);
    leanh::lean_dec(v___y_6160_);
    leanh::lean_dec_ref(v___y_6159_);
    leanh::lean_dec(v___y_6158_);
    leanh::lean_dec_ref(v___y_6157_);
    return v_res_6164_;
}
pub unsafe fn l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(
    mut v_stx_6165_: *mut leanh::LeanObject,
    mut v_n_6166_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_6167_: *mut leanh::LeanObject,
    mut v___y_6168_: *mut leanh::LeanObject,
    mut v___y_6169_: *mut leanh::LeanObject,
    mut v___y_6170_: *mut leanh::LeanObject,
    mut v___y_6171_: *mut leanh::LeanObject,
    mut v___y_6172_: *mut leanh::LeanObject,
    mut v___y_6173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: u8 = 0;
    let mut v___x_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6187_: u8 = 0;
    let mut v___x_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6175_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_n_6166_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_);
                if leanh::lean_obj_tag(v___x_6175_) == 0 {
                    v_a_6176_ = leanh::lean_ctor_get(v___x_6175_, 0);
                    leanh::lean_inc(v_a_6176_);
                    leanh::lean_dec_ref_known(v___x_6175_, 1);
                    v___x_6177_ = leanh::lean_box(0);
                    v___x_6178_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6178_, 0, v___x_6177_);
                    leanh::lean_ctor_set(v___x_6178_, 1, v_stx_6165_);
                    v___x_6179_ = l_Lean_LocalContext_empty;
                    v___x_6180_ = 0;
                    v___x_6181_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
                    leanh::lean_ctor_set(v___x_6181_, 0, v___x_6178_);
                    leanh::lean_ctor_set(v___x_6181_, 1, v___x_6179_);
                    leanh::lean_ctor_set(v___x_6181_, 2, v_expectedType_x3f_6167_);
                    leanh::lean_ctor_set(v___x_6181_, 3, v_a_6176_);
                    leanh::lean_ctor_set_uint8(
                        v___x_6181_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v___x_6180_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_6181_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                        v___x_6180_,
                    );
                    v___x_6182_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6182_, 0, v___x_6181_);
                    v___x_6183_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_6182_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_);
                    return v___x_6183_;
                } else {
                    leanh::lean_dec(v_expectedType_x3f_6167_);
                    leanh::lean_dec(v_stx_6165_);
                    v_a_6184_ = leanh::lean_ctor_get(v___x_6175_, 0);
                    v_isSharedCheck_6191_ = (!leanh::lean_is_exclusive(v___x_6175_)) as u8;
                    if v_isSharedCheck_6191_ == 0 {
                        v___x_6186_ = v___x_6175_;
                        v_isShared_6187_ = v_isSharedCheck_6191_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6184_);
                        leanh::lean_dec(v___x_6175_);
                        v___x_6186_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_6190_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6190_, 0, v_a_6184_);
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
    mut v_stx_6192_: *mut leanh::LeanObject,
    mut v_n_6193_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_6194_: *mut leanh::LeanObject,
    mut v___y_6195_: *mut leanh::LeanObject,
    mut v___y_6196_: *mut leanh::LeanObject,
    mut v___y_6197_: *mut leanh::LeanObject,
    mut v___y_6198_: *mut leanh::LeanObject,
    mut v___y_6199_: *mut leanh::LeanObject,
    mut v___y_6200_: *mut leanh::LeanObject,
    mut v___y_6201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_6200_);
    leanh::lean_dec_ref(v___y_6199_);
    leanh::lean_dec(v___y_6198_);
    leanh::lean_dec_ref(v___y_6197_);
    leanh::lean_dec(v___y_6196_);
    leanh::lean_dec_ref(v___y_6195_);
    return v_res_6202_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
    mut v_item_6203_: *mut leanh::LeanObject,
    mut v_projFn_6204_: *mut leanh::LeanObject,
    mut v_a_6205_: *mut leanh::LeanObject,
    mut v_a_6206_: *mut leanh::LeanObject,
    mut v_a_6207_: *mut leanh::LeanObject,
    mut v_a_6208_: *mut leanh::LeanObject,
    mut v_a_6209_: *mut leanh::LeanObject,
    mut v_a_6210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6214_: u8 = 0;
    v___x_6212_ = lean_st_ref_get(v_a_6210_);
    v_infoState_6213_ = leanh::lean_ctor_get(v___x_6212_, 7);
    leanh::lean_inc_ref(v_infoState_6213_);
    leanh::lean_dec(v___x_6212_);
    v_enabled_6214_ = leanh::lean_ctor_get_uint8(
        v_infoState_6213_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    leanh::lean_dec_ref(v_infoState_6213_);
    if v_enabled_6214_ == 0 {
        let mut v___x_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_projFn_6204_);
        v___x_6215_ = leanh::lean_box(0);
        v___x_6216_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6216_, 0, v___x_6215_);
        return v___x_6216_;
    } else {
        let mut v___x_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_env_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6219_: u8 = 0;
        v___x_6217_ = lean_st_ref_get(v_a_6210_);
        v_env_6218_ = leanh::lean_ctor_get(v___x_6217_, 0);
        leanh::lean_inc_ref(v_env_6218_);
        leanh::lean_dec(v___x_6217_);
        leanh::lean_inc(v_projFn_6204_);
        v___x_6219_ = l_Lean_Environment_contains(v_env_6218_, v_projFn_6204_, v_enabled_6214_);
        if v___x_6219_ == 0 {
            let mut v___x_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_projFn_6204_);
            v___x_6220_ = leanh::lean_box(0);
            v___x_6221_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_6221_, 0, v___x_6220_);
            return v___x_6221_;
        } else {
            let mut v___x_6222_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6222_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_6203_);
            v___x_6223_ = leanh::lean_box(0);
            v___x_6224_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v___x_6222_, v_projFn_6204_, v___x_6223_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_);
            return v___x_6224_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___boxed(
    mut v_item_6225_: *mut leanh::LeanObject,
    mut v_projFn_6226_: *mut leanh::LeanObject,
    mut v_a_6227_: *mut leanh::LeanObject,
    mut v_a_6228_: *mut leanh::LeanObject,
    mut v_a_6229_: *mut leanh::LeanObject,
    mut v_a_6230_: *mut leanh::LeanObject,
    mut v_a_6231_: *mut leanh::LeanObject,
    mut v_a_6232_: *mut leanh::LeanObject,
    mut v_a_6233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_6232_);
    leanh::lean_dec_ref(v_a_6231_);
    leanh::lean_dec(v_a_6230_);
    leanh::lean_dec_ref(v_a_6229_);
    leanh::lean_dec(v_a_6228_);
    leanh::lean_dec_ref(v_a_6227_);
    leanh::lean_dec_ref(v_item_6225_);
    return v_res_6234_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(
    mut v_t_6235_: *mut leanh::LeanObject,
    mut v___y_6236_: *mut leanh::LeanObject,
    mut v___y_6237_: *mut leanh::LeanObject,
    mut v___y_6238_: *mut leanh::LeanObject,
    mut v___y_6239_: *mut leanh::LeanObject,
    mut v___y_6240_: *mut leanh::LeanObject,
    mut v___y_6241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6243_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_6235_, v___y_6241_);
    return v___x_6243_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___boxed(
    mut v_t_6244_: *mut leanh::LeanObject,
    mut v___y_6245_: *mut leanh::LeanObject,
    mut v___y_6246_: *mut leanh::LeanObject,
    mut v___y_6247_: *mut leanh::LeanObject,
    mut v___y_6248_: *mut leanh::LeanObject,
    mut v___y_6249_: *mut leanh::LeanObject,
    mut v___y_6250_: *mut leanh::LeanObject,
    mut v___y_6251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6252_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(v_t_6244_, v___y_6245_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_);
    leanh::lean_dec(v___y_6250_);
    leanh::lean_dec_ref(v___y_6249_);
    leanh::lean_dec(v___y_6248_);
    leanh::lean_dec_ref(v___y_6247_);
    leanh::lean_dec(v___y_6246_);
    leanh::lean_dec_ref(v___y_6245_);
    return v_res_6252_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_6253_: *mut leanh::LeanObject,
    mut v_constName_6254_: *mut leanh::LeanObject,
    mut v___y_6255_: *mut leanh::LeanObject,
    mut v___y_6256_: *mut leanh::LeanObject,
    mut v___y_6257_: *mut leanh::LeanObject,
    mut v___y_6258_: *mut leanh::LeanObject,
    mut v___y_6259_: *mut leanh::LeanObject,
    mut v___y_6260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6262_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_);
    return v___x_6262_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_6263_: *mut leanh::LeanObject,
    mut v_constName_6264_: *mut leanh::LeanObject,
    mut v___y_6265_: *mut leanh::LeanObject,
    mut v___y_6266_: *mut leanh::LeanObject,
    mut v___y_6267_: *mut leanh::LeanObject,
    mut v___y_6268_: *mut leanh::LeanObject,
    mut v___y_6269_: *mut leanh::LeanObject,
    mut v___y_6270_: *mut leanh::LeanObject,
    mut v___y_6271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6272_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_6263_, v_constName_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_);
    leanh::lean_dec(v___y_6270_);
    leanh::lean_dec_ref(v___y_6269_);
    leanh::lean_dec(v___y_6268_);
    leanh::lean_dec_ref(v___y_6267_);
    leanh::lean_dec(v___y_6266_);
    leanh::lean_dec_ref(v___y_6265_);
    return v_res_6272_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b1_6273_: *mut leanh::LeanObject,
    mut v_ref_6274_: *mut leanh::LeanObject,
    mut v_constName_6275_: *mut leanh::LeanObject,
    mut v___y_6276_: *mut leanh::LeanObject,
    mut v___y_6277_: *mut leanh::LeanObject,
    mut v___y_6278_: *mut leanh::LeanObject,
    mut v___y_6279_: *mut leanh::LeanObject,
    mut v___y_6280_: *mut leanh::LeanObject,
    mut v___y_6281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6283_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_6274_, v_constName_6275_, v___y_6276_, v___y_6277_, v___y_6278_, v___y_6279_, v___y_6280_, v___y_6281_);
    return v___x_6283_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b1_6284_: *mut leanh::LeanObject,
    mut v_ref_6285_: *mut leanh::LeanObject,
    mut v_constName_6286_: *mut leanh::LeanObject,
    mut v___y_6287_: *mut leanh::LeanObject,
    mut v___y_6288_: *mut leanh::LeanObject,
    mut v___y_6289_: *mut leanh::LeanObject,
    mut v___y_6290_: *mut leanh::LeanObject,
    mut v___y_6291_: *mut leanh::LeanObject,
    mut v___y_6292_: *mut leanh::LeanObject,
    mut v___y_6293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6294_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_6284_, v_ref_6285_, v_constName_6286_, v___y_6287_, v___y_6288_, v___y_6289_, v___y_6290_, v___y_6291_, v___y_6292_);
    leanh::lean_dec(v___y_6292_);
    leanh::lean_dec_ref(v___y_6291_);
    leanh::lean_dec(v___y_6290_);
    leanh::lean_dec_ref(v___y_6289_);
    leanh::lean_dec(v___y_6288_);
    leanh::lean_dec_ref(v___y_6287_);
    leanh::lean_dec(v_ref_6285_);
    return v_res_6294_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(
    mut v_00_u03b1_6295_: *mut leanh::LeanObject,
    mut v_ref_6296_: *mut leanh::LeanObject,
    mut v_msg_6297_: *mut leanh::LeanObject,
    mut v_declHint_6298_: *mut leanh::LeanObject,
    mut v___y_6299_: *mut leanh::LeanObject,
    mut v___y_6300_: *mut leanh::LeanObject,
    mut v___y_6301_: *mut leanh::LeanObject,
    mut v___y_6302_: *mut leanh::LeanObject,
    mut v___y_6303_: *mut leanh::LeanObject,
    mut v___y_6304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6306_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_6296_, v_msg_6297_, v_declHint_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
    return v___x_6306_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(
    mut v_00_u03b1_6307_: *mut leanh::LeanObject,
    mut v_ref_6308_: *mut leanh::LeanObject,
    mut v_msg_6309_: *mut leanh::LeanObject,
    mut v_declHint_6310_: *mut leanh::LeanObject,
    mut v___y_6311_: *mut leanh::LeanObject,
    mut v___y_6312_: *mut leanh::LeanObject,
    mut v___y_6313_: *mut leanh::LeanObject,
    mut v___y_6314_: *mut leanh::LeanObject,
    mut v___y_6315_: *mut leanh::LeanObject,
    mut v___y_6316_: *mut leanh::LeanObject,
    mut v___y_6317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6318_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_6307_, v_ref_6308_, v_msg_6309_, v_declHint_6310_, v___y_6311_, v___y_6312_, v___y_6313_, v___y_6314_, v___y_6315_, v___y_6316_);
    leanh::lean_dec(v___y_6316_);
    leanh::lean_dec_ref(v___y_6315_);
    leanh::lean_dec(v___y_6314_);
    leanh::lean_dec_ref(v___y_6313_);
    leanh::lean_dec(v___y_6312_);
    leanh::lean_dec_ref(v___y_6311_);
    leanh::lean_dec(v_ref_6308_);
    return v_res_6318_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(
    mut v_msg_6319_: *mut leanh::LeanObject,
    mut v_declHint_6320_: *mut leanh::LeanObject,
    mut v___y_6321_: *mut leanh::LeanObject,
    mut v___y_6322_: *mut leanh::LeanObject,
    mut v___y_6323_: *mut leanh::LeanObject,
    mut v___y_6324_: *mut leanh::LeanObject,
    mut v___y_6325_: *mut leanh::LeanObject,
    mut v___y_6326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6328_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_6319_, v_declHint_6320_, v___y_6326_);
    return v___x_6328_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(
    mut v_msg_6329_: *mut leanh::LeanObject,
    mut v_declHint_6330_: *mut leanh::LeanObject,
    mut v___y_6331_: *mut leanh::LeanObject,
    mut v___y_6332_: *mut leanh::LeanObject,
    mut v___y_6333_: *mut leanh::LeanObject,
    mut v___y_6334_: *mut leanh::LeanObject,
    mut v___y_6335_: *mut leanh::LeanObject,
    mut v___y_6336_: *mut leanh::LeanObject,
    mut v___y_6337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6338_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_6329_, v_declHint_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_);
    leanh::lean_dec(v___y_6336_);
    leanh::lean_dec_ref(v___y_6335_);
    leanh::lean_dec(v___y_6334_);
    leanh::lean_dec_ref(v___y_6333_);
    leanh::lean_dec(v___y_6332_);
    leanh::lean_dec_ref(v___y_6331_);
    return v_res_6338_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(
    mut v_info_6339_: *mut leanh::LeanObject,
    mut v___y_6340_: *mut leanh::LeanObject,
    mut v___y_6341_: *mut leanh::LeanObject,
    mut v___y_6342_: *mut leanh::LeanObject,
    mut v___y_6343_: *mut leanh::LeanObject,
    mut v___y_6344_: *mut leanh::LeanObject,
    mut v___y_6345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6347_ = leanh::lean_alloc_ctor(8, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6347_, 0, v_info_6339_);
    v___x_6348_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_6347_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_, v___y_6345_);
    return v___x_6348_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0___boxed(
    mut v_info_6349_: *mut leanh::LeanObject,
    mut v___y_6350_: *mut leanh::LeanObject,
    mut v___y_6351_: *mut leanh::LeanObject,
    mut v___y_6352_: *mut leanh::LeanObject,
    mut v___y_6353_: *mut leanh::LeanObject,
    mut v___y_6354_: *mut leanh::LeanObject,
    mut v___y_6355_: *mut leanh::LeanObject,
    mut v___y_6356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6357_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v_info_6349_, v___y_6350_, v___y_6351_, v___y_6352_, v___y_6353_, v___y_6354_, v___y_6355_);
    leanh::lean_dec(v___y_6355_);
    leanh::lean_dec_ref(v___y_6354_);
    leanh::lean_dec(v___y_6353_);
    leanh::lean_dec_ref(v___y_6352_);
    leanh::lean_dec(v___y_6351_);
    leanh::lean_dec_ref(v___y_6350_);
    return v_res_6357_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6358_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6358_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6359_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0,
    );
    v___x_6360_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6360_, 0, v___x_6359_);
    return v___x_6360_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6361_ = leanh::lean_box(1);
    v___x_6362_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_6363_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1,
    );
    v___x_6364_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6364_, 0, v___x_6363_);
    leanh::lean_ctor_set(v___x_6364_, 1, v___x_6362_);
    leanh::lean_ctor_set(v___x_6364_, 2, v___x_6361_);
    return v___x_6364_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(
    mut v_item_6365_: *mut leanh::LeanObject,
    mut v_structName_6366_: *mut leanh::LeanObject,
    mut v_a_6367_: *mut leanh::LeanObject,
    mut v_a_6368_: *mut leanh::LeanObject,
    mut v_a_6369_: *mut leanh::LeanObject,
    mut v_a_6370_: *mut leanh::LeanObject,
    mut v_a_6371_: *mut leanh::LeanObject,
    mut v_a_6372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6376_: u8 = 0;
    v___x_6374_ = lean_st_ref_get(v_a_6372_);
    v_infoState_6375_ = leanh::lean_ctor_get(v___x_6374_, 7);
    leanh::lean_inc_ref(v_infoState_6375_);
    leanh::lean_dec(v___x_6374_);
    v_enabled_6376_ = leanh::lean_ctor_get_uint8(
        v_infoState_6375_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    leanh::lean_dec_ref(v_infoState_6375_);
    if v_enabled_6376_ == 0 {
        let mut v___x_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_structName_6366_);
        v___x_6377_ = leanh::lean_box(0);
        v___x_6378_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6378_, 0, v___x_6377_);
        return v___x_6378_;
    } else {
        let mut v___x_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_env_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6381_: u8 = 0;
        v___x_6379_ = lean_st_ref_get(v_a_6372_);
        v_env_6380_ = leanh::lean_ctor_get(v___x_6379_, 0);
        leanh::lean_inc_ref(v_env_6380_);
        leanh::lean_dec(v___x_6379_);
        leanh::lean_inc(v_structName_6366_);
        v___x_6381_ = l_Lean_Environment_contains(v_env_6380_, v_structName_6366_, v_enabled_6376_);
        if v___x_6381_ == 0 {
            let mut v___x_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6383_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_structName_6366_);
            v___x_6382_ = leanh::lean_box(0);
            v___x_6383_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_6383_, 0, v___x_6382_);
            return v___x_6383_;
        } else {
            let mut v___x_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6385_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6388_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6384_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_6365_);
            v___x_6385_ = l_Lean_Syntax_getId(v___x_6384_);
            v___x_6386_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_6386_, 0, v___x_6385_);
            v___x_6387_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once
                ),
                _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2,
            );
            v___x_6388_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
            leanh::lean_ctor_set(v___x_6388_, 0, v___x_6384_);
            leanh::lean_ctor_set(v___x_6388_, 1, v___x_6386_);
            leanh::lean_ctor_set(v___x_6388_, 2, v___x_6387_);
            leanh::lean_ctor_set(v___x_6388_, 3, v_structName_6366_);
            v___x_6389_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_6388_, v_a_6367_, v_a_6368_, v_a_6369_, v_a_6370_, v_a_6371_, v_a_6372_);
            return v___x_6389_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___boxed(
    mut v_item_6390_: *mut leanh::LeanObject,
    mut v_structName_6391_: *mut leanh::LeanObject,
    mut v_a_6392_: *mut leanh::LeanObject,
    mut v_a_6393_: *mut leanh::LeanObject,
    mut v_a_6394_: *mut leanh::LeanObject,
    mut v_a_6395_: *mut leanh::LeanObject,
    mut v_a_6396_: *mut leanh::LeanObject,
    mut v_a_6397_: *mut leanh::LeanObject,
    mut v_a_6398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6399_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_6397_);
    leanh::lean_dec_ref(v_a_6396_);
    leanh::lean_dec(v_a_6395_);
    leanh::lean_dec_ref(v_a_6394_);
    leanh::lean_dec(v_a_6393_);
    leanh::lean_dec_ref(v_a_6392_);
    leanh::lean_dec_ref(v_item_6390_);
    return v_res_6399_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(
    mut v_cfg_6400_: *mut leanh::LeanObject,
    mut v_withRef_6401_: *mut leanh::LeanObject,
    mut v___x_6402_: *mut leanh::LeanObject,
    mut v_oldRef_6403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_6404_ = l_Lean_replaceRef(v_cfg_6400_, v_oldRef_6403_);
    v___x_6405_ = leanh::lean_apply_3(
        v_withRef_6401_,
        leanh::lean_box(0),
        v_ref_6404_,
        v___x_6402_,
    );
    return v___x_6405_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed(
    mut v_cfg_6406_: *mut leanh::LeanObject,
    mut v_withRef_6407_: *mut leanh::LeanObject,
    mut v___x_6408_: *mut leanh::LeanObject,
    mut v_oldRef_6409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6410_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(
        v_cfg_6406_,
        v_withRef_6407_,
        v___x_6408_,
        v_oldRef_6409_,
    );
    leanh::lean_dec(v_oldRef_6409_);
    leanh::lean_dec(v_cfg_6406_);
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
    mut v_x_6414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1685__boxed_6415_: u32 = 0;
    let mut v_res_6416_: u8 = 0;
    let mut v_r_6417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1685__boxed_6415_ = leanh::lean_unbox_uint32(v_x_6414_);
    leanh::lean_dec(v_x_6414_);
    v_res_6416_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(v_x_1685__boxed_6415_);
    v_r_6417_ = leanh::lean_box((v_res_6416_) as usize);
    return v_r_6417_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2(
    mut v___f_6418_: *mut leanh::LeanObject,
    mut v_s_6419_: *mut leanh::LeanObject,
    mut v___y_6420_: *mut leanh::LeanObject,
    mut v___y_6421_: *mut leanh::LeanObject,
    mut v___y_6422_: *mut leanh::LeanObject,
    mut v___y_6423_: *mut leanh::LeanObject,
    mut v___y_6424_: *mut leanh::LeanObject,
    mut v___y_6425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6426_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_6418_);
    v___x_6427_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_6419_, v___x_6426_, v___y_6420_, leanh::lean_box(0), leanh::lean_box(0), v___y_6423_, v___y_6424_, v___y_6425_);
    return v___x_6427_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(
    mut v___f_6429_: *mut leanh::LeanObject,
    mut v_si_6430_: *mut leanh::LeanObject,
    mut v_val_6431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: u8 = 0;
    let mut v___x_6444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6439_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0;
                v___x_6440_ = leanh::lean_unsigned_to_nat(0);
                v___x_6441_ = lean_string_utf8_byte_size(v_val_6431_);
                leanh::lean_inc_ref(v_val_6431_);
                v___x_6442_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6442_, 0, v_val_6431_);
                leanh::lean_ctor_set(v___x_6442_, 1, v___x_6440_);
                leanh::lean_ctor_set(v___x_6442_, 2, v___x_6441_);
                v___x_6443_ =
                    l_String_Slice_contains___redArg(v___f_6429_, v___x_6442_, v___f_6439_);
                if v___x_6443_ == 0 {
                    v___x_6444_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_val_6431_);
                    v___x_6445_ = l_Lean_Name_str___override(v___x_6444_, v_val_6431_);
                    v___y_6433_ = v___x_6445_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_val_6431_);
                    v___x_6446_ = l_String_toName(v_val_6431_);
                    v___y_6433_ = v___x_6446_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6434_ = leanh::lean_unsigned_to_nat(0);
                v___x_6435_ = lean_string_utf8_byte_size(v_val_6431_);
                v___x_6436_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6436_, 0, v_val_6431_);
                leanh::lean_ctor_set(v___x_6436_, 1, v___x_6434_);
                leanh::lean_ctor_set(v___x_6436_, 2, v___x_6435_);
                v___x_6437_ = leanh::lean_box(0);
                v___x_6438_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_6438_, 0, v_si_6430_);
                leanh::lean_ctor_set(v___x_6438_, 1, v___x_6436_);
                leanh::lean_ctor_set(v___x_6438_, 2, v___y_6433_);
                leanh::lean_ctor_set(v___x_6438_, 3, v___x_6437_);
                return v___x_6438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(
    mut v_atomAsIdent_6447_: *mut leanh::LeanObject,
    mut v_stx_6448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_stx_6448_) {
        3 => {
            let mut v___x_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_atomAsIdent_6447_);
            v___x_6449_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_6449_, 0, v_stx_6448_);
            return v___x_6449_;
        }
        2 => {
            let mut v_info_6450_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_info_6450_ = leanh::lean_ctor_get(v_stx_6448_, 0);
            leanh::lean_inc(v_info_6450_);
            v_val_6451_ = leanh::lean_ctor_get(v_stx_6448_, 1);
            leanh::lean_inc_ref(v_val_6451_);
            leanh::lean_dec_ref_known(v_stx_6448_, 2);
            v___x_6452_ =
                leanh::lean_apply_2(v_atomAsIdent_6447_, v_info_6450_, v_val_6451_);
            v___x_6453_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_6453_, 0, v___x_6452_);
            return v___x_6453_;
        }
        _ => {
            let mut v___x_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_stx_6448_);
            leanh::lean_dec_ref(v_atomAsIdent_6447_);
            v___x_6454_ = leanh::lean_box(0);
            return v___x_6454_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___redArg(
    mut v_inst_6478_: *mut leanh::LeanObject,
    mut v_inst_6479_: *mut leanh::LeanObject,
    mut v_init_6480_: *mut leanh::LeanObject,
    mut v_cfgs_6481_: *mut leanh::LeanObject,
    mut v_k_6482_: *mut leanh::LeanObject,
    mut v_onErr_6483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: u8 = 0;
    v___x_6484_ = leanh::lean_unsigned_to_nat(0);
    v___x_6485_ = lean_array_get_size(v_cfgs_6481_);
    v___x_6486_ = lean_nat_dec_lt(v___x_6484_, v___x_6485_);
    if v___x_6486_ == 0 {
        let mut v_toApplicative_6487_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_onErr_6483_);
        leanh::lean_dec(v_k_6482_);
        leanh::lean_dec_ref(v_cfgs_6481_);
        leanh::lean_dec_ref(v_inst_6479_);
        v_toApplicative_6487_ = leanh::lean_ctor_get(v_inst_6478_, 0);
        leanh::lean_inc_ref(v_toApplicative_6487_);
        leanh::lean_dec_ref(v_inst_6478_);
        v_toPure_6488_ = leanh::lean_ctor_get(v_toApplicative_6487_, 1);
        leanh::lean_inc(v_toPure_6488_);
        leanh::lean_dec_ref(v_toApplicative_6487_);
        v___x_6489_ =
            leanh::lean_apply_2(v_toPure_6488_, leanh::lean_box(0), v_init_6480_);
        return v___x_6489_;
    } else {
        let mut v___f_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6491_: u8 = 0;
        leanh::lean_inc_ref(v_inst_6478_);
        v___f_6490_ = leanh::lean_alloc_closure(
            l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0 as *mut core::ffi::c_void,
            6,
            4,
        );
        leanh::lean_closure_set(v___f_6490_, 0, v_inst_6478_);
        leanh::lean_closure_set(v___f_6490_, 1, v_inst_6479_);
        leanh::lean_closure_set(v___f_6490_, 2, v_k_6482_);
        leanh::lean_closure_set(v___f_6490_, 3, v_onErr_6483_);
        v___x_6491_ = lean_nat_dec_le(v___x_6485_, v___x_6485_);
        if v___x_6491_ == 0 {
            if v___x_6486_ == 0 {
                let mut v_toApplicative_6492_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_6490_);
                leanh::lean_dec_ref(v_cfgs_6481_);
                v_toApplicative_6492_ = leanh::lean_ctor_get(v_inst_6478_, 0);
                leanh::lean_inc_ref(v_toApplicative_6492_);
                leanh::lean_dec_ref(v_inst_6478_);
                v_toPure_6493_ = leanh::lean_ctor_get(v_toApplicative_6492_, 1);
                leanh::lean_inc(v_toPure_6493_);
                leanh::lean_dec_ref(v_toApplicative_6492_);
                v___x_6494_ = leanh::lean_apply_2(
                    v_toPure_6493_,
                    leanh::lean_box(0),
                    v_init_6480_,
                );
                return v___x_6494_;
            } else {
                let mut v___x_6495_: usize = 0;
                let mut v___x_6496_: usize = 0;
                let mut v___x_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6495_ = 0usize;
                v___x_6496_ = lean_usize_of_nat(v___x_6485_);
                v___x_6497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6498_ = 0usize;
            v___x_6499_ = lean_usize_of_nat(v___x_6485_);
            v___x_6500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_inst_6501_: *mut leanh::LeanObject,
    mut v_inst_6502_: *mut leanh::LeanObject,
    mut v_init_6503_: *mut leanh::LeanObject,
    mut v_cfg_6504_: *mut leanh::LeanObject,
    mut v_k_6505_: *mut leanh::LeanObject,
    mut v_onErr_6506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRef_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: u8 = 0;
    let mut v___x_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: u8 = 0;
    let mut v___f_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_atomAsIdent_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: u8 = 0;
    let mut v_info_6533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6551_: u8 = 0;
    let mut v___x_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: u8 = 0;
    let mut v___x_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: u8 = 0;
    let mut v___x_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: u8 = 0;
    let mut v___x_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: u8 = 0;
    let mut v___x_6568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: u8 = 0;
    let mut v___x_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6525_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1;
                leanh::lean_inc(v_cfg_6504_);
                v___x_6526_ = l_Lean_Syntax_isOfKind(v_cfg_6504_, v___x_6525_);
                if v___x_6526_ == 0 {
                    v___x_6527_ = l_Lean_Syntax_getNumArgs(v_cfg_6504_);
                    v___x_6528_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6529_ = lean_nat_dec_eq(v___x_6527_, v___x_6528_);
                    if v___x_6529_ == 0 {
                        v___f_6530_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3;
                        v_atomAsIdent_6531_ =
                            l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4;
                        v___x_6532_ = lean_nat_dec_le(v___x_6528_, v___x_6527_);
                        if v___x_6532_ == 0 {
                            leanh::lean_dec(v___x_6527_);
                            if leanh::lean_obj_tag(v_cfg_6504_) == 2 {
                                leanh::lean_dec(v_onErr_6506_);
                                leanh::lean_dec_ref(v_inst_6502_);
                                leanh::lean_dec_ref(v_inst_6501_);
                                v_info_6533_ = leanh::lean_ctor_get(v_cfg_6504_, 0);
                                v_val_6534_ = leanh::lean_ctor_get(v_cfg_6504_, 1);
                                leanh::lean_inc_ref(v_val_6534_);
                                leanh::lean_inc(v_info_6533_);
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
                                v___x_6541_ = leanh::lean_box(0);
                                leanh::lean_inc(v___x_6535_);
                                v___x_6542_ =
                                    l_Lean_Syntax_identComponents(v___x_6535_, v___x_6541_);
                                v___x_6543_ = leanh::lean_box(0);
                                v___x_6544_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                                leanh::lean_ctor_set(v___x_6544_, 0, v_cfg_6504_);
                                leanh::lean_ctor_set(v___x_6544_, 1, v___x_6535_);
                                leanh::lean_ctor_set(v___x_6544_, 2, v___x_6537_);
                                leanh::lean_ctor_set(v___x_6544_, 3, v___x_6538_);
                                leanh::lean_ctor_set(v___x_6544_, 4, v___x_6540_);
                                leanh::lean_ctor_set(v___x_6544_, 5, v___x_6542_);
                                leanh::lean_ctor_set(v___x_6544_, 6, v___x_6543_);
                                v___x_6545_ = leanh::lean_apply_2(
                                    v_k_6505_,
                                    v_init_6503_,
                                    v___x_6544_,
                                );
                                return v___x_6545_;
                            } else {
                                leanh::lean_dec(v_k_6505_);
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_6546_ = leanh::lean_unsigned_to_nat(0);
                            v___x_6547_ = l_Lean_Syntax_getArg(v_cfg_6504_, v___x_6546_);
                            if leanh::lean_obj_tag(v___x_6547_) == 2 {
                                v_val_6548_ = leanh::lean_ctor_get(v___x_6547_, 1);
                                leanh::lean_inc_ref(v_val_6548_);
                                v___x_6562_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11;
                                v___x_6563_ = lean_string_dec_eq(v_val_6548_, v___x_6562_);
                                if v___x_6563_ == 0 {
                                    v___x_6564_ =
                                        l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12;
                                    v___x_6565_ = lean_string_dec_eq(v_val_6548_, v___x_6564_);
                                    if v___x_6565_ == 0 {
                                        leanh::lean_dec_ref_known(v___x_6547_, 2);
                                        v___x_6566_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13;
                                        v___x_6567_ = lean_string_dec_eq(v_val_6548_, v___x_6566_);
                                        leanh::lean_dec_ref(v_val_6548_);
                                        if v___x_6567_ == 0 {
                                            leanh::lean_dec(v___x_6527_);
                                            leanh::lean_dec(v_k_6505_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_6568_ = leanh::lean_unsigned_to_nat(5);
                                            v___x_6569_ = lean_nat_dec_le(v___x_6527_, v___x_6568_);
                                            leanh::lean_dec(v___x_6527_);
                                            if v___x_6569_ == 0 {
                                                leanh::lean_dec(v_k_6505_);
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_6570_ =
                                                    l_Lean_Syntax_getArg(v_cfg_6504_, v___x_6528_);
                                                v___x_6571_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_6531_, v___x_6570_);
                                                if leanh::lean_obj_tag(v___x_6571_) == 1 {
                                                    leanh::lean_dec(v_onErr_6506_);
                                                    leanh::lean_dec_ref(v_inst_6502_);
                                                    leanh::lean_dec_ref(v_inst_6501_);
                                                    v_val_6572_ =
                                                        leanh::lean_ctor_get(v___x_6571_, 0);
                                                    leanh::lean_inc_n(v_val_6572_, 2);
                                                    leanh::lean_dec_ref_known(
                                                        v___x_6571_,
                                                        1,
                                                    );
                                                    v___x_6573_ =
                                                        leanh::lean_unsigned_to_nat(3);
                                                    v___x_6574_ = l_Lean_Syntax_getArg(
                                                        v_cfg_6504_,
                                                        v___x_6573_,
                                                    );
                                                    v___x_6575_ = leanh::lean_box(0);
                                                    v___x_6576_ = l_Lean_TSyntax_getId(v_val_6572_);
                                                    v___x_6577_ =
                                                        lean_erase_macro_scopes(v___x_6576_);
                                                    v___x_6578_ = l_Lean_Syntax_identComponents(
                                                        v_val_6572_,
                                                        v___x_6575_,
                                                    );
                                                    v___x_6579_ = leanh::lean_box(0);
                                                    v___x_6580_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        7,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        0,
                                                        v_cfg_6504_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        1,
                                                        v_val_6572_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        2,
                                                        v___x_6574_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        3,
                                                        v___x_6575_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        4,
                                                        v___x_6577_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        5,
                                                        v___x_6578_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_6580_,
                                                        6,
                                                        v___x_6579_,
                                                    );
                                                    v___x_6581_ = leanh::lean_apply_2(
                                                        v_k_6505_,
                                                        v_init_6503_,
                                                        v___x_6580_,
                                                    );
                                                    return v___x_6581_;
                                                } else {
                                                    leanh::lean_dec(v___x_6571_);
                                                    leanh::lean_dec(v_k_6505_);
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_val_6548_);
                                        v___x_6582_ =
                                            leanh::lean_box((v___x_6529_) as usize);
                                        v___x_6583_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(v___x_6583_, 0, v___x_6582_);
                                        v___y_6550_ = v___x_6583_;
                                        v_val_6551_ = v___x_6529_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_val_6548_);
                                    v___x_6584_ = leanh::lean_box((v___x_6563_) as usize);
                                    v___x_6585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_6585_, 0, v___x_6584_);
                                    v___y_6550_ = v___x_6585_;
                                    v_val_6551_ = v___x_6563_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_6547_);
                                leanh::lean_dec(v___x_6527_);
                                leanh::lean_dec(v_k_6505_);
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_6527_);
                        v___x_6586_ = leanh::lean_unsigned_to_nat(0);
                        v___x_6587_ = l_Lean_Syntax_getArg(v_cfg_6504_, v___x_6586_);
                        leanh::lean_dec(v_cfg_6504_);
                        v_cfg_6504_ = v___x_6587_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_6589_ = l_Lean_Syntax_getArgs(v_cfg_6504_);
                    leanh::lean_dec(v_cfg_6504_);
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
                v___x_6513_ = leanh::lean_box(0);
                leanh::lean_inc(v___y_6508_);
                v___x_6514_ = l_Lean_Syntax_identComponents(v___y_6508_, v___x_6513_);
                v___x_6515_ = leanh::lean_box(0);
                v___x_6516_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                leanh::lean_ctor_set(v___x_6516_, 0, v_cfg_6504_);
                leanh::lean_ctor_set(v___x_6516_, 1, v___y_6508_);
                leanh::lean_ctor_set(v___x_6516_, 2, v___y_6510_);
                leanh::lean_ctor_set(v___x_6516_, 3, v___y_6509_);
                leanh::lean_ctor_set(v___x_6516_, 4, v___x_6512_);
                leanh::lean_ctor_set(v___x_6516_, 5, v___x_6514_);
                leanh::lean_ctor_set(v___x_6516_, 6, v___x_6515_);
                v___x_6517_ = leanh::lean_apply_2(v_k_6505_, v_init_6503_, v___x_6516_);
                return v___x_6517_;
            }
            2 => {
                v_toBind_6519_ = leanh::lean_ctor_get(v_inst_6501_, 1);
                leanh::lean_inc(v_toBind_6519_);
                leanh::lean_dec_ref(v_inst_6501_);
                v_getRef_6520_ = leanh::lean_ctor_get(v_inst_6502_, 0);
                leanh::lean_inc(v_getRef_6520_);
                v_withRef_6521_ = leanh::lean_ctor_get(v_inst_6502_, 1);
                leanh::lean_inc(v_withRef_6521_);
                leanh::lean_dec_ref(v_inst_6502_);
                leanh::lean_inc(v_cfg_6504_);
                v___x_6522_ = leanh::lean_apply_2(v_onErr_6506_, v_init_6503_, v_cfg_6504_);
                v___f_6523_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_6523_, 0, v_cfg_6504_);
                leanh::lean_closure_set(v___f_6523_, 1, v_withRef_6521_);
                leanh::lean_closure_set(v___f_6523_, 2, v___x_6522_);
                v___x_6524_ = leanh::lean_apply_4(
                    v_toBind_6519_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_getRef_6520_,
                    v___f_6523_,
                );
                return v___x_6524_;
            }
            3 => {
                v___x_6552_ = leanh::lean_unsigned_to_nat(2);
                v___x_6553_ = lean_nat_dec_eq(v___x_6527_, v___x_6552_);
                leanh::lean_dec(v___x_6527_);
                if v___x_6553_ == 0 {
                    leanh::lean_dec(v___y_6550_);
                    leanh::lean_dec_ref_known(v___x_6547_, 2);
                    leanh::lean_dec(v_k_6505_);
                    state = 2;
                    continue;
                } else {
                    v___x_6554_ = l_Lean_Syntax_getArg(v_cfg_6504_, v___x_6528_);
                    v___x_6555_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(
                        v_atomAsIdent_6531_,
                        v___x_6554_,
                    );
                    if leanh::lean_obj_tag(v___x_6555_) == 1 {
                        leanh::lean_dec(v_onErr_6506_);
                        leanh::lean_dec_ref(v_inst_6502_);
                        leanh::lean_dec_ref(v_inst_6501_);
                        if v_val_6551_ == 0 {
                            v_val_6556_ = leanh::lean_ctor_get(v___x_6555_, 0);
                            leanh::lean_inc(v_val_6556_);
                            leanh::lean_dec_ref_known(v___x_6555_, 1);
                            v___x_6557_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10;
                            v___x_6558_ =
                                l_Lean_mkCIdentFrom(v___x_6547_, v___x_6557_, v___x_6529_);
                            leanh::lean_dec_ref_known(v___x_6547_, 2);
                            v___y_6508_ = v_val_6556_;
                            v___y_6509_ = v___y_6550_;
                            v___y_6510_ = v___x_6558_;
                            state = 1;
                            continue;
                        } else {
                            v_val_6559_ = leanh::lean_ctor_get(v___x_6555_, 0);
                            leanh::lean_inc(v_val_6559_);
                            leanh::lean_dec_ref_known(v___x_6555_, 1);
                            v___x_6560_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7;
                            v___x_6561_ =
                                l_Lean_mkCIdentFrom(v___x_6547_, v___x_6560_, v___x_6529_);
                            leanh::lean_dec_ref_known(v___x_6547_, 2);
                            v___y_6508_ = v_val_6559_;
                            v___y_6509_ = v___y_6550_;
                            v___y_6510_ = v___x_6561_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_6555_);
                        leanh::lean_dec(v___y_6550_);
                        leanh::lean_dec_ref_known(v___x_6547_, 2);
                        leanh::lean_dec(v_k_6505_);
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
    mut v_inst_6591_: *mut leanh::LeanObject,
    mut v_inst_6592_: *mut leanh::LeanObject,
    mut v_k_6593_: *mut leanh::LeanObject,
    mut v_onErr_6594_: *mut leanh::LeanObject,
    mut v_x_6595_: *mut leanh::LeanObject,
    mut v_cfg_x27_6596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6598_: *mut leanh::LeanObject,
    mut v_m_6599_: *mut leanh::LeanObject,
    mut v_inst_6600_: *mut leanh::LeanObject,
    mut v_inst_6601_: *mut leanh::LeanObject,
    mut v_init_6602_: *mut leanh::LeanObject,
    mut v_cfg_6603_: *mut leanh::LeanObject,
    mut v_k_6604_: *mut leanh::LeanObject,
    mut v_onErr_6605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6606_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6607_: *mut leanh::LeanObject,
    mut v_m_6608_: *mut leanh::LeanObject,
    mut v_inst_6609_: *mut leanh::LeanObject,
    mut v_inst_6610_: *mut leanh::LeanObject,
    mut v_init_6611_: *mut leanh::LeanObject,
    mut v_cfgs_6612_: *mut leanh::LeanObject,
    mut v_k_6613_: *mut leanh::LeanObject,
    mut v_onErr_6614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_6626_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_6626_) == 1 {
        let mut v_pre_6627_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_6627_ = leanh::lean_ctor_get(v_x_6626_, 0);
        match leanh::lean_obj_tag(v_pre_6627_) {
            1 => {
                let mut v_pre_6628_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_6628_ = leanh::lean_ctor_get(v_pre_6627_, 0);
                match leanh::lean_obj_tag(v_pre_6628_) {
                    0 => {
                        let mut v_str_6629_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_6630_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_6631_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_6632_: u8 = 0;
                        v_str_6629_ = leanh::lean_ctor_get(v_x_6626_, 1);
                        v_str_6630_ = leanh::lean_ctor_get(v_pre_6627_, 1);
                        v___x_6631_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0;
                        v___x_6632_ = lean_string_dec_eq(v_str_6630_, v___x_6631_);
                        if v___x_6632_ == 0 {
                            let mut v___x_6633_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6634_: u8 = 0;
                            v___x_6633_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1;
                            v___x_6634_ = lean_string_dec_eq(v_str_6630_, v___x_6633_);
                            if v___x_6634_ == 0 {
                                return v___y_6624_;
                            } else {
                                let mut v___x_6635_: *mut leanh::LeanObject =
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
                            let mut v___x_6637_: *mut leanh::LeanObject =
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
                        let mut v_pre_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_6639_ = leanh::lean_ctor_get(v_pre_6628_, 0);
                        if leanh::lean_obj_tag(v_pre_6639_) == 0 {
                            let mut v_str_6640_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_6641_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_6642_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6643_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_6644_: u8 = 0;
                            v_str_6640_ = leanh::lean_ctor_get(v_x_6626_, 1);
                            v_str_6641_ = leanh::lean_ctor_get(v_pre_6627_, 1);
                            v_str_6642_ = leanh::lean_ctor_get(v_pre_6628_, 1);
                            v___x_6643_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4;
                            v___x_6644_ = lean_string_dec_eq(v_str_6642_, v___x_6643_);
                            if v___x_6644_ == 0 {
                                return v___y_6624_;
                            } else {
                                let mut v___x_6645_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_6646_: u8 = 0;
                                v___x_6645_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5;
                                v___x_6646_ = lean_string_dec_eq(v_str_6641_, v___x_6645_);
                                if v___x_6646_ == 0 {
                                    return v___y_6624_;
                                } else {
                                    let mut v___x_6647_: *mut leanh::LeanObject =
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
                let mut v_str_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6650_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6651_: u8 = 0;
                v_str_6649_ = leanh::lean_ctor_get(v_x_6626_, 1);
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
    mut v___y_6652_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_6653_: *mut leanh::LeanObject,
    mut v_x_6654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6697__boxed_6655_: u8 = 0;
    let mut v_suppressElabErrors_boxed_6656_: u8 = 0;
    let mut v_res_6657_: u8 = 0;
    let mut v_r_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_6697__boxed_6655_ = (leanh::lean_unbox(v___y_6652_) as u8);
    v_suppressElabErrors_boxed_6656_ = (leanh::lean_unbox(v_suppressElabErrors_6653_) as u8);
    v_res_6657_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(v___y_6697__boxed_6655_, v_suppressElabErrors_boxed_6656_, v_x_6654_);
    leanh::lean_dec(v_x_6654_);
    v_r_6658_ = leanh::lean_box((v_res_6657_) as usize);
    return v_r_6658_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(
    mut v_ref_6659_: *mut leanh::LeanObject,
    mut v_msgData_6660_: *mut leanh::LeanObject,
    mut v_severity_6661_: u8,
    mut v_isSilent_6662_: u8,
    mut v___y_6663_: *mut leanh::LeanObject,
    mut v___y_6664_: *mut leanh::LeanObject,
    mut v___y_6665_: *mut leanh::LeanObject,
    mut v___y_6666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6672_: u8 = 0;
    let mut v___y_6673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6674_: u8 = 0;
    let mut v___y_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6692_: u8 = 0;
    let mut v___x_6693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6703_: u8 = 0;
    let mut v___y_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6707_: u8 = 0;
    let mut v___y_6708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6709_: u8 = 0;
    let mut v___y_6710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6711_: u8 = 0;
    let mut v___y_6712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6718_: u8 = 0;
    let mut v___x_6719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: u8 = 0;
    let mut v___x_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6728_: u8 = 0;
    let mut v___y_6730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6733_: u8 = 0;
    let mut v___y_6734_: u8 = 0;
    let mut v___y_6735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6736_: u8 = 0;
    let mut v___y_6737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6742_: u8 = 0;
    let mut v___y_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6744_: u8 = 0;
    let mut v___y_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6747_: u8 = 0;
    let mut v_ref_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: u8 = 0;
    let mut v___y_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6756_: u8 = 0;
    let mut v___y_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6759_: u8 = 0;
    let mut v___y_6760_: u8 = 0;
    let mut v___y_6762_: u8 = 0;
    let mut v_fileName_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6767_: u8 = 0;
    let mut v___x_6768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: u8 = 0;
    let mut v___x_6772_: u8 = 0;
    let mut v___x_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: u8 = 0;
    let mut v___x_6775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_inc_ref(v_msgData_6660_);
                    v___x_6778_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6660_);
                    v___y_6762_ = v___x_6778_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_6678_ = lean_st_ref_take(v___y_6677_);
                v_currNamespace_6679_ = leanh::lean_ctor_get(v___y_6676_, 6);
                v_openDecls_6680_ = leanh::lean_ctor_get(v___y_6676_, 7);
                v_env_6681_ = leanh::lean_ctor_get(v___x_6678_, 0);
                v_nextMacroScope_6682_ = leanh::lean_ctor_get(v___x_6678_, 1);
                v_ngen_6683_ = leanh::lean_ctor_get(v___x_6678_, 2);
                v_auxDeclNGen_6684_ = leanh::lean_ctor_get(v___x_6678_, 3);
                v_traceState_6685_ = leanh::lean_ctor_get(v___x_6678_, 4);
                v_cache_6686_ = leanh::lean_ctor_get(v___x_6678_, 5);
                v_messages_6687_ = leanh::lean_ctor_get(v___x_6678_, 6);
                v_infoState_6688_ = leanh::lean_ctor_get(v___x_6678_, 7);
                v_snapshotTasks_6689_ = leanh::lean_ctor_get(v___x_6678_, 8);
                v_isSharedCheck_6703_ = (!leanh::lean_is_exclusive(v___x_6678_)) as u8;
                if v_isSharedCheck_6703_ == 0 {
                    v___x_6691_ = v___x_6678_;
                    v_isShared_6692_ = v_isSharedCheck_6703_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6689_);
                    leanh::lean_inc(v_infoState_6688_);
                    leanh::lean_inc(v_messages_6687_);
                    leanh::lean_inc(v_cache_6686_);
                    leanh::lean_inc(v_traceState_6685_);
                    leanh::lean_inc(v_auxDeclNGen_6684_);
                    leanh::lean_inc(v_ngen_6683_);
                    leanh::lean_inc(v_nextMacroScope_6682_);
                    leanh::lean_inc(v_env_6681_);
                    leanh::lean_dec(v___x_6678_);
                    v___x_6691_ = leanh::lean_box(0);
                    v_isShared_6692_ = v_isSharedCheck_6703_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_6680_);
                leanh::lean_inc(v_currNamespace_6679_);
                v___x_6693_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6693_, 0, v_currNamespace_6679_);
                leanh::lean_ctor_set(v___x_6693_, 1, v_openDecls_6680_);
                v___x_6694_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6694_, 0, v___x_6693_);
                leanh::lean_ctor_set(v___x_6694_, 1, v___y_6669_);
                leanh::lean_inc_ref(v___y_6671_);
                leanh::lean_inc_ref(v___y_6673_);
                v___x_6695_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_6695_, 0, v___y_6673_);
                leanh::lean_ctor_set(v___x_6695_, 1, v___y_6670_);
                leanh::lean_ctor_set(v___x_6695_, 2, v___y_6675_);
                leanh::lean_ctor_set(v___x_6695_, 3, v___y_6671_);
                leanh::lean_ctor_set(v___x_6695_, 4, v___x_6694_);
                leanh::lean_ctor_set_uint8(
                    v___x_6695_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_6672_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6695_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_6674_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6695_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_6662_,
                );
                v___x_6696_ = l_Lean_MessageLog_add(v___x_6695_, v_messages_6687_);
                if v_isShared_6692_ == 0 {
                    leanh::lean_ctor_set(v___x_6691_, 6, v___x_6696_);
                    v___x_6698_ = v___x_6691_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6702_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 0, v_env_6681_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 1, v_nextMacroScope_6682_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 2, v_ngen_6683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 3, v_auxDeclNGen_6684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 4, v_traceState_6685_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 5, v_cache_6686_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 6, v___x_6696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 7, v_infoState_6688_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 8, v_snapshotTasks_6689_);
                    v___x_6698_ = v_reuseFailAlloc_6702_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6699_ = lean_st_ref_set(v___y_6677_, v___x_6698_);
                v___x_6700_ = leanh::lean_box(0);
                v___x_6701_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6701_, 0, v___x_6700_);
                return v___x_6701_;
            }
            4 => {
                v___x_6713_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_6660_,
                    );
                v___x_6714_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v___x_6713_, v___y_6663_, v___y_6664_, v___y_6665_, v___y_6666_);
                v_a_6715_ = leanh::lean_ctor_get(v___x_6714_, 0);
                v_isSharedCheck_6728_ = (!leanh::lean_is_exclusive(v___x_6714_)) as u8;
                if v_isSharedCheck_6728_ == 0 {
                    v___x_6717_ = v___x_6714_;
                    v_isShared_6718_ = v_isSharedCheck_6728_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6715_);
                    leanh::lean_dec(v___x_6714_);
                    v___x_6717_ = leanh::lean_box(0);
                    v_isShared_6718_ = v_isSharedCheck_6728_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_6708_, 2);
                v___x_6719_ = l_Lean_FileMap_toPosition(v___y_6708_, v___y_6706_);
                leanh::lean_dec(v___y_6706_);
                v___x_6720_ = l_Lean_FileMap_toPosition(v___y_6708_, v___y_6712_);
                leanh::lean_dec(v___y_6712_);
                v___x_6721_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6721_, 0, v___x_6720_);
                v___x_6722_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29;
                if v___y_6707_ == 0 {
                    leanh::lean_del_object(v___x_6717_);
                    leanh::lean_dec_ref(v___y_6705_);
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
                    leanh::lean_inc(v_a_6715_);
                    v___x_6723_ = l_Lean_MessageData_hasTag(v___y_6705_, v_a_6715_);
                    if v___x_6723_ == 0 {
                        leanh::lean_dec_ref_known(v___x_6721_, 1);
                        leanh::lean_dec_ref(v___x_6719_);
                        leanh::lean_dec(v_a_6715_);
                        v___x_6724_ = leanh::lean_box(0);
                        if v_isShared_6718_ == 0 {
                            leanh::lean_ctor_set(v___x_6717_, 0, v___x_6724_);
                            v___x_6726_ = v___x_6717_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_6727_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6727_, 0, v___x_6724_);
                            v___x_6726_ = v_reuseFailAlloc_6727_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6717_);
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
                leanh::lean_dec(v___y_6731_);
                if leanh::lean_obj_tag(v___x_6738_) == 0 {
                    leanh::lean_inc(v___y_6737_);
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
                    v_val_6739_ = leanh::lean_ctor_get(v___x_6738_, 0);
                    leanh::lean_inc(v_val_6739_);
                    leanh::lean_dec_ref_known(v___x_6738_, 1);
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
                if leanh::lean_obj_tag(v___x_6749_) == 0 {
                    v___x_6750_ = leanh::lean_unsigned_to_nat(0);
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
                    v_val_6751_ = leanh::lean_ctor_get(v___x_6749_, 0);
                    leanh::lean_inc(v_val_6751_);
                    leanh::lean_dec_ref_known(v___x_6749_, 1);
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
                    v_fileName_6763_ = leanh::lean_ctor_get(v___y_6665_, 0);
                    v_fileMap_6764_ = leanh::lean_ctor_get(v___y_6665_, 1);
                    v_options_6765_ = leanh::lean_ctor_get(v___y_6665_, 2);
                    v_ref_6766_ = leanh::lean_ctor_get(v___y_6665_, 5);
                    v_suppressElabErrors_6767_ = leanh::lean_ctor_get_uint8(
                        v___y_6665_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_6768_ = leanh::lean_box((v___y_6762_) as usize);
                    v___x_6769_ = leanh::lean_box((v_suppressElabErrors_6767_) as usize);
                    v___f_6770_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_6770_, 0, v___x_6768_);
                    leanh::lean_closure_set(v___f_6770_, 1, v___x_6769_);
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
                    leanh::lean_dec_ref(v_msgData_6660_);
                    v___x_6775_ = leanh::lean_box(0);
                    v___x_6776_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6776_, 0, v___x_6775_);
                    return v___x_6776_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_6779_: *mut leanh::LeanObject,
    mut v_msgData_6780_: *mut leanh::LeanObject,
    mut v_severity_6781_: *mut leanh::LeanObject,
    mut v_isSilent_6782_: *mut leanh::LeanObject,
    mut v___y_6783_: *mut leanh::LeanObject,
    mut v___y_6784_: *mut leanh::LeanObject,
    mut v___y_6785_: *mut leanh::LeanObject,
    mut v___y_6786_: *mut leanh::LeanObject,
    mut v___y_6787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_6788_: u8 = 0;
    let mut v_isSilent_boxed_6789_: u8 = 0;
    let mut v_res_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6788_ = (leanh::lean_unbox(v_severity_6781_) as u8);
    v_isSilent_boxed_6789_ = (leanh::lean_unbox(v_isSilent_6782_) as u8);
    v_res_6790_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_6779_, v_msgData_6780_, v_severity_boxed_6788_, v_isSilent_boxed_6789_, v___y_6783_, v___y_6784_, v___y_6785_, v___y_6786_);
    leanh::lean_dec(v___y_6786_);
    leanh::lean_dec_ref(v___y_6785_);
    leanh::lean_dec(v___y_6784_);
    leanh::lean_dec_ref(v___y_6783_);
    leanh::lean_dec(v_ref_6779_);
    return v_res_6790_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(
    mut v_msgData_6791_: *mut leanh::LeanObject,
    mut v_severity_6792_: u8,
    mut v_isSilent_6793_: u8,
    mut v___y_6794_: *mut leanh::LeanObject,
    mut v___y_6795_: *mut leanh::LeanObject,
    mut v___y_6796_: *mut leanh::LeanObject,
    mut v___y_6797_: *mut leanh::LeanObject,
    mut v___y_6798_: *mut leanh::LeanObject,
    mut v___y_6799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_6801_ = leanh::lean_ctor_get(v___y_6798_, 5);
    v___x_6802_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_6801_, v_msgData_6791_, v_severity_6792_, v_isSilent_6793_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_);
    return v___x_6802_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3___boxed(
    mut v_msgData_6803_: *mut leanh::LeanObject,
    mut v_severity_6804_: *mut leanh::LeanObject,
    mut v_isSilent_6805_: *mut leanh::LeanObject,
    mut v___y_6806_: *mut leanh::LeanObject,
    mut v___y_6807_: *mut leanh::LeanObject,
    mut v___y_6808_: *mut leanh::LeanObject,
    mut v___y_6809_: *mut leanh::LeanObject,
    mut v___y_6810_: *mut leanh::LeanObject,
    mut v___y_6811_: *mut leanh::LeanObject,
    mut v___y_6812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_6813_: u8 = 0;
    let mut v_isSilent_boxed_6814_: u8 = 0;
    let mut v_res_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6813_ = (leanh::lean_unbox(v_severity_6804_) as u8);
    v_isSilent_boxed_6814_ = (leanh::lean_unbox(v_isSilent_6805_) as u8);
    v_res_6815_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_6803_, v_severity_boxed_6813_, v_isSilent_boxed_6814_, v___y_6806_, v___y_6807_, v___y_6808_, v___y_6809_, v___y_6810_, v___y_6811_);
    leanh::lean_dec(v___y_6811_);
    leanh::lean_dec_ref(v___y_6810_);
    leanh::lean_dec(v___y_6809_);
    leanh::lean_dec_ref(v___y_6808_);
    leanh::lean_dec(v___y_6807_);
    leanh::lean_dec_ref(v___y_6806_);
    return v_res_6815_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(
    mut v_msgData_6816_: *mut leanh::LeanObject,
    mut v___y_6817_: *mut leanh::LeanObject,
    mut v___y_6818_: *mut leanh::LeanObject,
    mut v___y_6819_: *mut leanh::LeanObject,
    mut v___y_6820_: *mut leanh::LeanObject,
    mut v___y_6821_: *mut leanh::LeanObject,
    mut v___y_6822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6824_: u8 = 0;
    let mut v___x_6825_: u8 = 0;
    let mut v___x_6826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6824_ = 2;
    v___x_6825_ = 0;
    v___x_6826_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_6816_, v___x_6824_, v___x_6825_, v___y_6817_, v___y_6818_, v___y_6819_, v___y_6820_, v___y_6821_, v___y_6822_);
    return v___x_6826_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1___boxed(
    mut v_msgData_6827_: *mut leanh::LeanObject,
    mut v___y_6828_: *mut leanh::LeanObject,
    mut v___y_6829_: *mut leanh::LeanObject,
    mut v___y_6830_: *mut leanh::LeanObject,
    mut v___y_6831_: *mut leanh::LeanObject,
    mut v___y_6832_: *mut leanh::LeanObject,
    mut v___y_6833_: *mut leanh::LeanObject,
    mut v___y_6834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6835_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v_msgData_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_, v___y_6833_);
    leanh::lean_dec(v___y_6833_);
    leanh::lean_dec_ref(v___y_6832_);
    leanh::lean_dec(v___y_6831_);
    leanh::lean_dec_ref(v___y_6830_);
    leanh::lean_dec(v___y_6829_);
    leanh::lean_dec_ref(v___y_6828_);
    return v_res_6835_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(
    mut v_ref_6836_: *mut leanh::LeanObject,
    mut v_msgData_6837_: *mut leanh::LeanObject,
    mut v___y_6838_: *mut leanh::LeanObject,
    mut v___y_6839_: *mut leanh::LeanObject,
    mut v___y_6840_: *mut leanh::LeanObject,
    mut v___y_6841_: *mut leanh::LeanObject,
    mut v___y_6842_: *mut leanh::LeanObject,
    mut v___y_6843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6845_: u8 = 0;
    let mut v___x_6846_: u8 = 0;
    let mut v___x_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6845_ = 2;
    v___x_6846_ = 0;
    v___x_6847_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_6836_, v_msgData_6837_, v___x_6845_, v___x_6846_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_);
    return v___x_6847_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0___boxed(
    mut v_ref_6848_: *mut leanh::LeanObject,
    mut v_msgData_6849_: *mut leanh::LeanObject,
    mut v___y_6850_: *mut leanh::LeanObject,
    mut v___y_6851_: *mut leanh::LeanObject,
    mut v___y_6852_: *mut leanh::LeanObject,
    mut v___y_6853_: *mut leanh::LeanObject,
    mut v___y_6854_: *mut leanh::LeanObject,
    mut v___y_6855_: *mut leanh::LeanObject,
    mut v___y_6856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6857_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_6848_, v_msgData_6849_, v___y_6850_, v___y_6851_, v___y_6852_, v___y_6853_, v___y_6854_, v___y_6855_);
    leanh::lean_dec(v___y_6855_);
    leanh::lean_dec_ref(v___y_6854_);
    leanh::lean_dec(v___y_6853_);
    leanh::lean_dec_ref(v___y_6852_);
    leanh::lean_dec(v___y_6851_);
    leanh::lean_dec_ref(v___y_6850_);
    leanh::lean_dec(v_ref_6848_);
    return v_res_6857_;
}
pub unsafe fn _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6859_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0;
    v___x_6860_ = l_Lean_stringToMessageData(v___x_6859_);
    return v___x_6860_;
}
pub unsafe fn l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(
    mut v_ex_6861_: *mut leanh::LeanObject,
    mut v___y_6862_: *mut leanh::LeanObject,
    mut v___y_6863_: *mut leanh::LeanObject,
    mut v___y_6864_: *mut leanh::LeanObject,
    mut v___y_6865_: *mut leanh::LeanObject,
    mut v___y_6866_: *mut leanh::LeanObject,
    mut v___y_6867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_6870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_6872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6874_: u8 = 0;
    let mut v___x_6875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6884_: u8 = 0;
    let mut v_ref_6885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6893_: u8 = 0;
    let mut v___x_6894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: u8 = 0;
    let mut v___x_6897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_ex_6861_) == 0 {
                    v_ref_6869_ = leanh::lean_ctor_get(v_ex_6861_, 0);
                    leanh::lean_inc(v_ref_6869_);
                    v_msg_6870_ = leanh::lean_ctor_get(v_ex_6861_, 1);
                    leanh::lean_inc_ref(v_msg_6870_);
                    leanh::lean_dec_ref_known(v_ex_6861_, 2);
                    v___x_6871_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_6869_, v_msg_6870_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_, v___y_6867_);
                    leanh::lean_dec(v_ref_6869_);
                    return v___x_6871_;
                } else {
                    v_id_6872_ = leanh::lean_ctor_get(v_ex_6861_, 0);
                    leanh::lean_inc(v_id_6872_);
                    v___x_6896_ = l_Lean_Elab_isAbortExceptionId(v_id_6872_);
                    if v___x_6896_ == 0 {
                        v___x_6897_ = l_Lean_Exception_isInterrupt(v_ex_6861_);
                        leanh::lean_dec_ref_known(v_ex_6861_, 2);
                        v___y_6874_ = v___x_6897_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v_ex_6861_, 2);
                        v___y_6874_ = v___x_6896_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6874_ == 0 {
                    v___x_6875_ = l_Lean_InternalExceptionId_getName(v_id_6872_);
                    leanh::lean_dec(v_id_6872_);
                    if leanh::lean_obj_tag(v___x_6875_) == 0 {
                        v_a_6876_ = leanh::lean_ctor_get(v___x_6875_, 0);
                        leanh::lean_inc(v_a_6876_);
                        leanh::lean_dec_ref_known(v___x_6875_, 1);
                        v___x_6877_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once), _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1);
                        v___x_6878_ = l_Lean_MessageData_ofName(v_a_6876_);
                        v___x_6879_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6879_, 0, v___x_6877_);
                        leanh::lean_ctor_set(v___x_6879_, 1, v___x_6878_);
                        v___x_6880_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v___x_6879_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_, v___y_6867_);
                        return v___x_6880_;
                    } else {
                        v_a_6881_ = leanh::lean_ctor_get(v___x_6875_, 0);
                        v_isSharedCheck_6893_ =
                            (!leanh::lean_is_exclusive(v___x_6875_)) as u8;
                        if v_isSharedCheck_6893_ == 0 {
                            v___x_6883_ = v___x_6875_;
                            v_isShared_6884_ = v_isSharedCheck_6893_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6881_);
                            leanh::lean_dec(v___x_6875_);
                            v___x_6883_ = leanh::lean_box(0);
                            v_isShared_6884_ = v_isSharedCheck_6893_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_id_6872_);
                    v___x_6894_ = leanh::lean_box(0);
                    v___x_6895_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6895_, 0, v___x_6894_);
                    return v___x_6895_;
                }
            }
            2 => {
                v_ref_6885_ = leanh::lean_ctor_get(v___y_6866_, 5);
                v___x_6886_ = lean_io_error_to_string(v_a_6881_);
                v___x_6887_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6887_, 0, v___x_6886_);
                v___x_6888_ = l_Lean_MessageData_ofFormat(v___x_6887_);
                leanh::lean_inc(v_ref_6885_);
                v___x_6889_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6889_, 0, v_ref_6885_);
                leanh::lean_ctor_set(v___x_6889_, 1, v___x_6888_);
                if v_isShared_6884_ == 0 {
                    leanh::lean_ctor_set(v___x_6883_, 0, v___x_6889_);
                    v___x_6891_ = v___x_6883_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6892_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6892_, 0, v___x_6889_);
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
    mut v_ex_6898_: *mut leanh::LeanObject,
    mut v___y_6899_: *mut leanh::LeanObject,
    mut v___y_6900_: *mut leanh::LeanObject,
    mut v___y_6901_: *mut leanh::LeanObject,
    mut v___y_6902_: *mut leanh::LeanObject,
    mut v___y_6903_: *mut leanh::LeanObject,
    mut v___y_6904_: *mut leanh::LeanObject,
    mut v___y_6905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6906_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_6904_);
    leanh::lean_dec_ref(v___y_6903_);
    leanh::lean_dec(v___y_6902_);
    leanh::lean_dec_ref(v___y_6901_);
    leanh::lean_dec(v___y_6900_);
    leanh::lean_dec_ref(v___y_6899_);
    return v_res_6906_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(
    mut v_a_6907_: *mut leanh::LeanObject,
    mut v_config_6908_: *mut leanh::LeanObject,
    mut v_____r_6909_: *mut leanh::LeanObject,
    mut v___y_6910_: *mut leanh::LeanObject,
    mut v___y_6911_: *mut leanh::LeanObject,
    mut v___y_6912_: *mut leanh::LeanObject,
    mut v___y_6913_: *mut leanh::LeanObject,
    mut v___y_6914_: *mut leanh::LeanObject,
    mut v___y_6915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6920_: u8 = 0;
    let mut v___x_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6925_: u8 = 0;
    let mut v_unused_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6930_: u8 = 0;
    let mut v___x_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6917_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_a_6907_, v___y_6910_, v___y_6911_, v___y_6912_, v___y_6913_, v___y_6914_, v___y_6915_);
                if leanh::lean_obj_tag(v___x_6917_) == 0 {
                    v_isSharedCheck_6925_ = (!leanh::lean_is_exclusive(v___x_6917_)) as u8;
                    if v_isSharedCheck_6925_ == 0 {
                        v_unused_6926_ = leanh::lean_ctor_get(v___x_6917_, 0);
                        leanh::lean_dec(v_unused_6926_);
                        v___x_6919_ = v___x_6917_;
                        v_isShared_6920_ = v_isSharedCheck_6925_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6917_);
                        v___x_6919_ = leanh::lean_box(0);
                        v_isShared_6920_ = v_isSharedCheck_6925_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_config_6908_);
                    v_a_6927_ = leanh::lean_ctor_get(v___x_6917_, 0);
                    v_isSharedCheck_6934_ = (!leanh::lean_is_exclusive(v___x_6917_)) as u8;
                    if v_isSharedCheck_6934_ == 0 {
                        v___x_6929_ = v___x_6917_;
                        v_isShared_6930_ = v_isSharedCheck_6934_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6927_);
                        leanh::lean_dec(v___x_6917_);
                        v___x_6929_ = leanh::lean_box(0);
                        v_isShared_6930_ = v_isSharedCheck_6934_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6921_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6921_, 0, v_config_6908_);
                if v_isShared_6920_ == 0 {
                    leanh::lean_ctor_set(v___x_6919_, 0, v___x_6921_);
                    v___x_6923_ = v___x_6919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6924_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6924_, 0, v___x_6921_);
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
                    v_reuseFailAlloc_6933_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6933_, 0, v_a_6927_);
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
    mut v_a_6935_: *mut leanh::LeanObject,
    mut v_config_6936_: *mut leanh::LeanObject,
    mut v_____r_6937_: *mut leanh::LeanObject,
    mut v___y_6938_: *mut leanh::LeanObject,
    mut v___y_6939_: *mut leanh::LeanObject,
    mut v___y_6940_: *mut leanh::LeanObject,
    mut v___y_6941_: *mut leanh::LeanObject,
    mut v___y_6942_: *mut leanh::LeanObject,
    mut v___y_6943_: *mut leanh::LeanObject,
    mut v___y_6944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_6943_);
    leanh::lean_dec_ref(v___y_6942_);
    leanh::lean_dec(v___y_6941_);
    leanh::lean_dec_ref(v___y_6940_);
    leanh::lean_dec(v___y_6939_);
    leanh::lean_dec_ref(v___y_6938_);
    return v_res_6945_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(
    mut v___f_6946_: *mut leanh::LeanObject,
    mut v_x_6947_: *mut leanh::LeanObject,
    mut v___y_6948_: *mut leanh::LeanObject,
    mut v___y_6949_: *mut leanh::LeanObject,
    mut v___y_6950_: *mut leanh::LeanObject,
    mut v___y_6951_: *mut leanh::LeanObject,
    mut v___y_6952_: *mut leanh::LeanObject,
    mut v___y_6953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6955_ = leanh::lean_box(0);
    leanh::lean_inc(v___y_6953_);
    leanh::lean_inc_ref(v___y_6952_);
    leanh::lean_inc(v___y_6951_);
    leanh::lean_inc_ref(v___y_6950_);
    leanh::lean_inc(v___y_6949_);
    leanh::lean_inc_ref(v___y_6948_);
    v___x_6956_ = leanh::lean_apply_8(
        v___f_6946_,
        v___x_6955_,
        v___y_6948_,
        v___y_6949_,
        v___y_6950_,
        v___y_6951_,
        v___y_6952_,
        v___y_6953_,
        leanh::lean_box(0),
    );
    return v___x_6956_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1___boxed(
    mut v___f_6957_: *mut leanh::LeanObject,
    mut v_x_6958_: *mut leanh::LeanObject,
    mut v___y_6959_: *mut leanh::LeanObject,
    mut v___y_6960_: *mut leanh::LeanObject,
    mut v___y_6961_: *mut leanh::LeanObject,
    mut v___y_6962_: *mut leanh::LeanObject,
    mut v___y_6963_: *mut leanh::LeanObject,
    mut v___y_6964_: *mut leanh::LeanObject,
    mut v___y_6965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6966_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_6964_);
    leanh::lean_dec_ref(v___y_6963_);
    leanh::lean_dec(v___y_6962_);
    leanh::lean_dec_ref(v___y_6961_);
    leanh::lean_dec(v___y_6960_);
    leanh::lean_dec_ref(v___y_6959_);
    leanh::lean_dec_ref(v_x_6958_);
    return v_res_6966_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(
    mut v_eval_6967_: *mut leanh::LeanObject,
    mut v_config_6968_: *mut leanh::LeanObject,
    mut v_item_6969_: *mut leanh::LeanObject,
    mut v_logExceptions_6970_: u8,
    mut v_a_6971_: *mut leanh::LeanObject,
    mut v_a_6972_: *mut leanh::LeanObject,
    mut v_a_6973_: *mut leanh::LeanObject,
    mut v_a_6974_: *mut leanh::LeanObject,
    mut v_a_6975_: *mut leanh::LeanObject,
    mut v_a_6976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6983_: u8 = 0;
    let mut v_a_6984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6988_: u8 = 0;
    let mut v_a_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6992_: u8 = 0;
    let mut v___x_6994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6996_: u8 = 0;
    let mut v___x_6997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7001_: u8 = 0;
    let mut v___x_7003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7004_: u8 = 0;
    let mut v_extra_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_7006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: u8 = 0;
    let mut v___x_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7016_: u8 = 0;
    let mut v_unused_7017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: u8 = 0;
    let mut v___x_7019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_6976_);
                leanh::lean_inc_ref(v_a_6975_);
                leanh::lean_inc(v_a_6974_);
                leanh::lean_inc_ref(v_a_6973_);
                leanh::lean_inc(v_a_6972_);
                leanh::lean_inc_ref(v_a_6971_);
                leanh::lean_inc(v_config_6968_);
                v___x_6997_ = leanh::lean_apply_9(
                    v_eval_6967_,
                    v_config_6968_,
                    v_item_6969_,
                    v_a_6971_,
                    v_a_6972_,
                    v_a_6973_,
                    v_a_6974_,
                    v_a_6975_,
                    v_a_6976_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_6997_) == 0 {
                    leanh::lean_dec(v_config_6968_);
                    return v___x_6997_;
                } else {
                    v_a_6998_ = leanh::lean_ctor_get(v___x_6997_, 0);
                    leanh::lean_inc_n(v_a_6998_, 2);
                    leanh::lean_inc(v_config_6968_);
                    v___f_6999_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        2,
                    );
                    leanh::lean_closure_set(v___f_6999_, 0, v_a_6998_);
                    leanh::lean_closure_set(v___f_6999_, 1, v_config_6968_);
                    v___x_7018_ = l_Lean_Exception_isInterrupt(v_a_6998_);
                    if v___x_7018_ == 0 {
                        leanh::lean_inc(v_a_6998_);
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
                if leanh::lean_obj_tag(v___y_6979_) == 0 {
                    v_a_6980_ = leanh::lean_ctor_get(v___y_6979_, 0);
                    v_isSharedCheck_6988_ = (!leanh::lean_is_exclusive(v___y_6979_)) as u8;
                    if v_isSharedCheck_6988_ == 0 {
                        v___x_6982_ = v___y_6979_;
                        v_isShared_6983_ = v_isSharedCheck_6988_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6980_);
                        leanh::lean_dec(v___y_6979_);
                        v___x_6982_ = leanh::lean_box(0);
                        v_isShared_6983_ = v_isSharedCheck_6988_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6989_ = leanh::lean_ctor_get(v___y_6979_, 0);
                    v_isSharedCheck_6996_ = (!leanh::lean_is_exclusive(v___y_6979_)) as u8;
                    if v_isSharedCheck_6996_ == 0 {
                        v___x_6991_ = v___y_6979_;
                        v_isShared_6992_ = v_isSharedCheck_6996_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6989_);
                        leanh::lean_dec(v___y_6979_);
                        v___x_6991_ = leanh::lean_box(0);
                        v_isShared_6992_ = v_isSharedCheck_6996_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_a_6984_ = leanh::lean_ctor_get(v_a_6980_, 0);
                leanh::lean_inc(v_a_6984_);
                leanh::lean_dec(v_a_6980_);
                if v_isShared_6983_ == 0 {
                    leanh::lean_ctor_set(v___x_6982_, 0, v_a_6984_);
                    v___x_6986_ = v___x_6982_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6987_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6987_, 0, v_a_6984_);
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
                    v_reuseFailAlloc_6995_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6995_, 0, v_a_6989_);
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
                        leanh::lean_dec_ref(v___f_6999_);
                        leanh::lean_dec(v_a_6998_);
                        leanh::lean_dec(v_config_6968_);
                        return v___x_6997_;
                    } else {
                        v_isSharedCheck_7016_ =
                            (!leanh::lean_is_exclusive(v___x_6997_)) as u8;
                        if v_isSharedCheck_7016_ == 0 {
                            v_unused_7017_ = leanh::lean_ctor_get(v___x_6997_, 0);
                            leanh::lean_dec(v_unused_7017_);
                            v___x_7003_ = v___x_6997_;
                            v_isShared_7004_ = v_isSharedCheck_7016_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_6997_);
                            v___x_7003_ = leanh::lean_box(0);
                            v_isShared_7004_ = v_isSharedCheck_7016_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___f_6999_);
                    leanh::lean_dec(v_a_6998_);
                    leanh::lean_dec(v_config_6968_);
                    return v___x_6997_;
                }
            }
            7 => {
                if leanh::lean_obj_tag(v_a_6998_) == 1 {
                    v_extra_7005_ = leanh::lean_ctor_get(v_a_6998_, 1);
                    if leanh::lean_obj_tag(v_extra_7005_) == 0 {
                        leanh::lean_dec_ref(v___f_6999_);
                        v_id_7006_ = leanh::lean_ctor_get(v_a_6998_, 0);
                        v___x_7007_ = l_Lean_Elab_abortTermExceptionId;
                        v___x_7008_ =
                            l_Lean_instBEqInternalExceptionId_beq(v_id_7006_, v___x_7007_);
                        if v___x_7008_ == 0 {
                            leanh::lean_del_object(v___x_7003_);
                            v___x_7009_ = leanh::lean_box(0);
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
                            leanh::lean_dec_ref_known(v_a_6998_, 2);
                            if v_isShared_7004_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_7003_, 0);
                                leanh::lean_ctor_set(v___x_7003_, 0, v_config_6968_);
                                v___x_7012_ = v___x_7003_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_7013_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(
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
                        leanh::lean_del_object(v___x_7003_);
                        leanh::lean_dec(v_config_6968_);
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
                        leanh::lean_dec_ref_known(v_a_6998_, 2);
                        v___y_6979_ = v___x_7014_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7003_);
                    leanh::lean_dec(v_config_6968_);
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
                    leanh::lean_dec(v_a_6998_);
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
    mut v_eval_7020_: *mut leanh::LeanObject,
    mut v_config_7021_: *mut leanh::LeanObject,
    mut v_item_7022_: *mut leanh::LeanObject,
    mut v_logExceptions_7023_: *mut leanh::LeanObject,
    mut v_a_7024_: *mut leanh::LeanObject,
    mut v_a_7025_: *mut leanh::LeanObject,
    mut v_a_7026_: *mut leanh::LeanObject,
    mut v_a_7027_: *mut leanh::LeanObject,
    mut v_a_7028_: *mut leanh::LeanObject,
    mut v_a_7029_: *mut leanh::LeanObject,
    mut v_a_7030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_7031_: u8 = 0;
    let mut v_res_7032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7031_ = (leanh::lean_unbox(v_logExceptions_7023_) as u8);
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
    leanh::lean_dec(v_a_7029_);
    leanh::lean_dec_ref(v_a_7028_);
    leanh::lean_dec(v_a_7027_);
    leanh::lean_dec_ref(v_a_7026_);
    leanh::lean_dec(v_a_7025_);
    leanh::lean_dec_ref(v_a_7024_);
    return v_res_7032_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(
    mut v_00_u03b1_7033_: *mut leanh::LeanObject,
    mut v_eval_7034_: *mut leanh::LeanObject,
    mut v_config_7035_: *mut leanh::LeanObject,
    mut v_item_7036_: *mut leanh::LeanObject,
    mut v_logExceptions_7037_: u8,
    mut v_a_7038_: *mut leanh::LeanObject,
    mut v_a_7039_: *mut leanh::LeanObject,
    mut v_a_7040_: *mut leanh::LeanObject,
    mut v_a_7041_: *mut leanh::LeanObject,
    mut v_a_7042_: *mut leanh::LeanObject,
    mut v_a_7043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7045_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_7046_: *mut leanh::LeanObject,
    mut v_eval_7047_: *mut leanh::LeanObject,
    mut v_config_7048_: *mut leanh::LeanObject,
    mut v_item_7049_: *mut leanh::LeanObject,
    mut v_logExceptions_7050_: *mut leanh::LeanObject,
    mut v_a_7051_: *mut leanh::LeanObject,
    mut v_a_7052_: *mut leanh::LeanObject,
    mut v_a_7053_: *mut leanh::LeanObject,
    mut v_a_7054_: *mut leanh::LeanObject,
    mut v_a_7055_: *mut leanh::LeanObject,
    mut v_a_7056_: *mut leanh::LeanObject,
    mut v_a_7057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_7058_: u8 = 0;
    let mut v_res_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7058_ = (leanh::lean_unbox(v_logExceptions_7050_) as u8);
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
    leanh::lean_dec(v_a_7056_);
    leanh::lean_dec_ref(v_a_7055_);
    leanh::lean_dec(v_a_7054_);
    leanh::lean_dec_ref(v_a_7053_);
    leanh::lean_dec(v_a_7052_);
    leanh::lean_dec_ref(v_a_7051_);
    return v_res_7059_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(
    mut v_ref_7060_: *mut leanh::LeanObject,
    mut v_msgData_7061_: *mut leanh::LeanObject,
    mut v_severity_7062_: u8,
    mut v_isSilent_7063_: u8,
    mut v___y_7064_: *mut leanh::LeanObject,
    mut v___y_7065_: *mut leanh::LeanObject,
    mut v___y_7066_: *mut leanh::LeanObject,
    mut v___y_7067_: *mut leanh::LeanObject,
    mut v___y_7068_: *mut leanh::LeanObject,
    mut v___y_7069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7071_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_7060_, v_msgData_7061_, v_severity_7062_, v_isSilent_7063_, v___y_7066_, v___y_7067_, v___y_7068_, v___y_7069_);
    return v___x_7071_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___boxed(
    mut v_ref_7072_: *mut leanh::LeanObject,
    mut v_msgData_7073_: *mut leanh::LeanObject,
    mut v_severity_7074_: *mut leanh::LeanObject,
    mut v_isSilent_7075_: *mut leanh::LeanObject,
    mut v___y_7076_: *mut leanh::LeanObject,
    mut v___y_7077_: *mut leanh::LeanObject,
    mut v___y_7078_: *mut leanh::LeanObject,
    mut v___y_7079_: *mut leanh::LeanObject,
    mut v___y_7080_: *mut leanh::LeanObject,
    mut v___y_7081_: *mut leanh::LeanObject,
    mut v___y_7082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_7083_: u8 = 0;
    let mut v_isSilent_boxed_7084_: u8 = 0;
    let mut v_res_7085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_7083_ = (leanh::lean_unbox(v_severity_7074_) as u8);
    v_isSilent_boxed_7084_ = (leanh::lean_unbox(v_isSilent_7075_) as u8);
    v_res_7085_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(v_ref_7072_, v_msgData_7073_, v_severity_boxed_7083_, v_isSilent_boxed_7084_, v___y_7076_, v___y_7077_, v___y_7078_, v___y_7079_, v___y_7080_, v___y_7081_);
    leanh::lean_dec(v___y_7081_);
    leanh::lean_dec_ref(v___y_7080_);
    leanh::lean_dec(v___y_7079_);
    leanh::lean_dec_ref(v___y_7078_);
    leanh::lean_dec(v___y_7077_);
    leanh::lean_dec_ref(v___y_7076_);
    leanh::lean_dec(v_ref_7072_);
    return v_res_7085_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_7086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7086_ = leanh::lean_box(0);
    v___x_7087_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_7088_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7088_, 0, v___x_7087_);
    leanh::lean_ctor_set(v___x_7088_, 1, v___x_7086_);
    return v___x_7088_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_7090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7090_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0);
    v___x_7091_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7091_, 0, v___x_7090_);
    return v___x_7091_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___boxed(
    mut v___y_7092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7093_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
    return v_res_7093_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(
    mut v_00_u03b1_7094_: *mut leanh::LeanObject,
    mut v___y_7095_: *mut leanh::LeanObject,
    mut v___y_7096_: *mut leanh::LeanObject,
    mut v___y_7097_: *mut leanh::LeanObject,
    mut v___y_7098_: *mut leanh::LeanObject,
    mut v___y_7099_: *mut leanh::LeanObject,
    mut v___y_7100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7102_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
    return v___x_7102_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___boxed(
    mut v_00_u03b1_7103_: *mut leanh::LeanObject,
    mut v___y_7104_: *mut leanh::LeanObject,
    mut v___y_7105_: *mut leanh::LeanObject,
    mut v___y_7106_: *mut leanh::LeanObject,
    mut v___y_7107_: *mut leanh::LeanObject,
    mut v___y_7108_: *mut leanh::LeanObject,
    mut v___y_7109_: *mut leanh::LeanObject,
    mut v___y_7110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7111_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(v_00_u03b1_7103_, v___y_7104_, v___y_7105_, v___y_7106_, v___y_7107_, v___y_7108_, v___y_7109_);
    leanh::lean_dec(v___y_7109_);
    leanh::lean_dec_ref(v___y_7108_);
    leanh::lean_dec(v___y_7107_);
    leanh::lean_dec_ref(v___y_7106_);
    leanh::lean_dec(v___y_7105_);
    leanh::lean_dec_ref(v___y_7104_);
    return v_res_7111_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7115_ = leanh::lean_unsigned_to_nat(1);
    v___x_7116_ = l_Lean_Level_ofNat(v___x_7115_);
    return v___x_7116_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7117_ = leanh::lean_box(0);
    v___x_7118_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2,
    );
    v___x_7119_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7119_, 0, v___x_7118_);
    leanh::lean_ctor_set(v___x_7119_, 1, v___x_7117_);
    return v___x_7119_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_7120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7120_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_7126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7126_ = leanh::lean_box(0);
    v___x_7127_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6;
    v___x_7128_ = l_Lean_Expr_const___override(v___x_7127_, v___x_7126_);
    return v___x_7128_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(
    mut v_cfg_7132_: *mut leanh::LeanObject,
    mut v_cfgItem_7133_: *mut leanh::LeanObject,
    mut v_cfgType_x3f_7134_: *mut leanh::LeanObject,
    mut v_a_7135_: *mut leanh::LeanObject,
    mut v_a_7136_: *mut leanh::LeanObject,
    mut v_a_7137_: *mut leanh::LeanObject,
    mut v_a_7138_: *mut leanh::LeanObject,
    mut v_a_7139_: *mut leanh::LeanObject,
    mut v_a_7140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_7143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: u8 = 0;
    let mut v___x_7150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_7155_: u8 = 0;
    let mut v___x_7156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7159_: u8 = 0;
    let mut v___x_7160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: u8 = 0;
    let mut v___x_7168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: u8 = 0;
    let mut v___x_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_cfgType_x3f_7134_) == 1 {
                    v_val_7152_ = leanh::lean_ctor_get(v_cfgType_x3f_7134_, 0);
                    leanh::lean_inc(v_val_7152_);
                    leanh::lean_dec_ref_known(v_cfgType_x3f_7134_, 1);
                    v___x_7153_ = lean_st_ref_get(v_a_7140_);
                    v_infoState_7154_ = leanh::lean_ctor_get(v___x_7153_, 7);
                    leanh::lean_inc_ref(v_infoState_7154_);
                    leanh::lean_dec(v___x_7153_);
                    v_enabled_7155_ = leanh::lean_ctor_get_uint8(
                        v_infoState_7154_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    leanh::lean_dec_ref(v_infoState_7154_);
                    if v_enabled_7155_ == 0 {
                        leanh::lean_dec(v_val_7152_);
                        v___y_7143_ = v_a_7135_;
                        v___y_7144_ = v_a_7136_;
                        v___y_7145_ = v_a_7137_;
                        v___y_7146_ = v_a_7138_;
                        v___y_7147_ = v_a_7139_;
                        v___y_7148_ = v_a_7140_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7156_ = leanh::lean_unsigned_to_nat(0);
                        v___x_7157_ = l_Lean_Syntax_getArg(v_cfgItem_7133_, v___x_7156_);
                        v___x_7171_ = l_Lean_Syntax_isAtom(v___x_7157_);
                        if v___x_7171_ == 0 {
                            v___y_7159_ = v___x_7171_;
                            state = 2;
                            continue;
                        } else {
                            v___x_7172_ = leanh::lean_unsigned_to_nat(1);
                            v___x_7173_ = l_Lean_Syntax_getArg(v_cfgItem_7133_, v___x_7172_);
                            v___x_7174_ = l_Lean_Syntax_isMissing(v___x_7173_);
                            leanh::lean_dec(v___x_7173_);
                            v___y_7159_ = v___x_7174_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_cfgType_x3f_7134_);
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
                    leanh::lean_dec(v_cfg_7132_);
                    v___x_7150_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
                    return v___x_7150_;
                } else {
                    v___x_7151_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7151_, 0, v_cfg_7132_);
                    return v___x_7151_;
                }
            }
            2 => {
                if v___y_7159_ == 0 {
                    leanh::lean_dec(v___x_7157_);
                    leanh::lean_dec(v_val_7152_);
                    v___y_7143_ = v_a_7135_;
                    v___y_7144_ = v_a_7136_;
                    v___y_7145_ = v_a_7137_;
                    v___y_7146_ = v_a_7138_;
                    v___y_7147_ = v_a_7139_;
                    v___y_7148_ = v_a_7140_;
                    state = 1;
                    continue;
                } else {
                    v___x_7160_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once), _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4);
                    v___x_7161_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once), _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7);
                    v___x_7162_ = l_Lean_mkAppB(v___x_7160_, v_val_7152_, v___x_7161_);
                    v___x_7163_ =
                        l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9;
                    v___x_7164_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7164_, 0, v___x_7163_);
                    leanh::lean_ctor_set(v___x_7164_, 1, v___x_7157_);
                    v___x_7165_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2,
                    );
                    v___x_7166_ = leanh::lean_box(0);
                    v___x_7167_ = 0;
                    v___x_7168_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
                    leanh::lean_ctor_set(v___x_7168_, 0, v___x_7164_);
                    leanh::lean_ctor_set(v___x_7168_, 1, v___x_7165_);
                    leanh::lean_ctor_set(v___x_7168_, 2, v___x_7166_);
                    leanh::lean_ctor_set(v___x_7168_, 3, v___x_7162_);
                    leanh::lean_ctor_set_uint8(
                        v___x_7168_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v___x_7167_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_7168_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                        v___x_7167_,
                    );
                    v___x_7169_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7169_, 0, v___x_7168_);
                    leanh::lean_ctor_set(v___x_7169_, 1, v___x_7166_);
                    v___x_7170_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_7169_, v_a_7135_, v_a_7136_, v_a_7137_, v_a_7138_, v_a_7139_, v_a_7140_);
                    leanh::lean_dec_ref(v___x_7170_);
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
    mut v_cfg_7175_: *mut leanh::LeanObject,
    mut v_cfgItem_7176_: *mut leanh::LeanObject,
    mut v_cfgType_x3f_7177_: *mut leanh::LeanObject,
    mut v_a_7178_: *mut leanh::LeanObject,
    mut v_a_7179_: *mut leanh::LeanObject,
    mut v_a_7180_: *mut leanh::LeanObject,
    mut v_a_7181_: *mut leanh::LeanObject,
    mut v_a_7182_: *mut leanh::LeanObject,
    mut v_a_7183_: *mut leanh::LeanObject,
    mut v_a_7184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7185_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_7183_);
    leanh::lean_dec_ref(v_a_7182_);
    leanh::lean_dec(v_a_7181_);
    leanh::lean_dec_ref(v_a_7180_);
    leanh::lean_dec(v_a_7179_);
    leanh::lean_dec_ref(v_a_7178_);
    leanh::lean_dec(v_cfgItem_7176_);
    return v_res_7185_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(
    mut v_00_u03b1_7186_: *mut leanh::LeanObject,
    mut v_cfg_7187_: *mut leanh::LeanObject,
    mut v_cfgItem_7188_: *mut leanh::LeanObject,
    mut v_cfgType_x3f_7189_: *mut leanh::LeanObject,
    mut v_a_7190_: *mut leanh::LeanObject,
    mut v_a_7191_: *mut leanh::LeanObject,
    mut v_a_7192_: *mut leanh::LeanObject,
    mut v_a_7193_: *mut leanh::LeanObject,
    mut v_a_7194_: *mut leanh::LeanObject,
    mut v_a_7195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7197_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_7198_: *mut leanh::LeanObject,
    mut v_cfg_7199_: *mut leanh::LeanObject,
    mut v_cfgItem_7200_: *mut leanh::LeanObject,
    mut v_cfgType_x3f_7201_: *mut leanh::LeanObject,
    mut v_a_7202_: *mut leanh::LeanObject,
    mut v_a_7203_: *mut leanh::LeanObject,
    mut v_a_7204_: *mut leanh::LeanObject,
    mut v_a_7205_: *mut leanh::LeanObject,
    mut v_a_7206_: *mut leanh::LeanObject,
    mut v_a_7207_: *mut leanh::LeanObject,
    mut v_a_7208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7209_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_7207_);
    leanh::lean_dec_ref(v_a_7206_);
    leanh::lean_dec(v_a_7205_);
    leanh::lean_dec_ref(v_a_7204_);
    leanh::lean_dec(v_a_7203_);
    leanh::lean_dec_ref(v_a_7202_);
    leanh::lean_dec(v_cfgItem_7200_);
    return v_res_7209_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(
    mut v_s_7210_: *mut leanh::LeanObject,
    mut v_a_7211_: *mut leanh::LeanObject,
    mut v_b_7212_: u8,
) -> u8 {
    let mut v_str_7213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_7214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_7215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: u8 = 0;
    let mut v___x_7218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: u32 = 0;
    let mut v___x_7220_: u32 = 0;
    let mut v___x_7221_: u8 = 0;
    let mut v___x_7222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_7213_ = leanh::lean_ctor_get(v_s_7210_, 0);
                v_startInclusive_7214_ = leanh::lean_ctor_get(v_s_7210_, 1);
                v_endExclusive_7215_ = leanh::lean_ctor_get(v_s_7210_, 2);
                v___x_7216_ = lean_nat_sub(v_endExclusive_7215_, v_startInclusive_7214_);
                v___x_7217_ = lean_nat_dec_eq(v_a_7211_, v___x_7216_);
                leanh::lean_dec(v___x_7216_);
                if v___x_7217_ == 0 {
                    v___x_7218_ = lean_nat_add(v_startInclusive_7214_, v_a_7211_);
                    leanh::lean_dec(v_a_7211_);
                    v___x_7219_ = lean_string_utf8_get_fast(v_str_7213_, v___x_7218_);
                    v___x_7220_ = 46;
                    v___x_7221_ = lean_uint32_dec_eq(v___x_7219_, v___x_7220_);
                    if v___x_7221_ == 0 {
                        v___x_7222_ = lean_string_utf8_next_fast(v_str_7213_, v___x_7218_);
                        leanh::lean_dec(v___x_7218_);
                        v___x_7223_ = lean_nat_sub(v___x_7222_, v_startInclusive_7214_);
                        v_a_7211_ = v___x_7223_;
                        v_b_7212_ = v___x_7221_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_7218_);
                        return v___x_7221_;
                    }
                } else {
                    leanh::lean_dec(v_a_7211_);
                    return v_b_7212_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_s_7225_: *mut leanh::LeanObject,
    mut v_a_7226_: *mut leanh::LeanObject,
    mut v_b_7227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_7228_: u8 = 0;
    let mut v_res_7229_: u8 = 0;
    let mut v_r_7230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_7228_ = (leanh::lean_unbox(v_b_7227_) as u8);
    v_res_7229_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_7225_, v_a_7226_, v_b_boxed_7228_);
    leanh::lean_dec_ref(v_s_7225_);
    v_r_7230_ = leanh::lean_box((v_res_7229_) as usize);
    return v_r_7230_;
}
pub unsafe fn l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(
    mut v_s_7231_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_searcher_7232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: u8 = 0;
    let mut v___x_7234_: u8 = 0;
    v_searcher_7232_ = leanh::lean_unsigned_to_nat(0);
    v___x_7233_ = 0;
    v___x_7234_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_7231_, v_searcher_7232_, v___x_7233_);
    return v___x_7234_;
}
pub unsafe fn l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0___boxed(
    mut v_s_7235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7236_: u8 = 0;
    let mut v_r_7237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7236_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v_s_7235_);
    leanh::lean_dec_ref(v_s_7235_);
    v_r_7237_ = leanh::lean_box((v_res_7236_) as usize);
    return v_r_7237_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(
    mut v_si_7238_: *mut leanh::LeanObject,
    mut v_val_7239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_7241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: u8 = 0;
    let mut v___x_7251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7247_ = leanh::lean_unsigned_to_nat(0);
                v___x_7248_ = lean_string_utf8_byte_size(v_val_7239_);
                leanh::lean_inc_ref(v_val_7239_);
                v___x_7249_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_7249_, 0, v_val_7239_);
                leanh::lean_ctor_set(v___x_7249_, 1, v___x_7247_);
                leanh::lean_ctor_set(v___x_7249_, 2, v___x_7248_);
                v___x_7250_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v___x_7249_);
                leanh::lean_dec_ref_known(v___x_7249_, 3);
                if v___x_7250_ == 0 {
                    v___x_7251_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_val_7239_);
                    v___x_7252_ = l_Lean_Name_str___override(v___x_7251_, v_val_7239_);
                    v___y_7241_ = v___x_7252_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_val_7239_);
                    v___x_7253_ = l_String_toName(v_val_7239_);
                    v___y_7241_ = v___x_7253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7242_ = leanh::lean_unsigned_to_nat(0);
                v___x_7243_ = lean_string_utf8_byte_size(v_val_7239_);
                v___x_7244_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_7244_, 0, v_val_7239_);
                leanh::lean_ctor_set(v___x_7244_, 1, v___x_7242_);
                leanh::lean_ctor_set(v___x_7244_, 2, v___x_7243_);
                v___x_7245_ = leanh::lean_box(0);
                v___x_7246_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_7246_, 0, v_si_7238_);
                leanh::lean_ctor_set(v___x_7246_, 1, v___x_7244_);
                leanh::lean_ctor_set(v___x_7246_, 2, v___y_7241_);
                leanh::lean_ctor_set(v___x_7246_, 3, v___x_7245_);
                return v___x_7246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(
    mut v_eval_7255_: *mut leanh::LeanObject,
    mut v_logExceptions_7256_: u8,
    mut v_onErr_7257_: *mut leanh::LeanObject,
    mut v_init_7258_: *mut leanh::LeanObject,
    mut v_cfgs_7259_: *mut leanh::LeanObject,
    mut v___y_7260_: *mut leanh::LeanObject,
    mut v___y_7261_: *mut leanh::LeanObject,
    mut v___y_7262_: *mut leanh::LeanObject,
    mut v___y_7263_: *mut leanh::LeanObject,
    mut v___y_7264_: *mut leanh::LeanObject,
    mut v___y_7265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: u8 = 0;
    v___x_7267_ = leanh::lean_unsigned_to_nat(0);
    v___x_7268_ = lean_array_get_size(v_cfgs_7259_);
    v___x_7269_ = lean_nat_dec_lt(v___x_7267_, v___x_7268_);
    if v___x_7269_ == 0 {
        let mut v___x_7270_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_onErr_7257_);
        leanh::lean_dec_ref(v_eval_7255_);
        v___x_7270_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7270_, 0, v_init_7258_);
        return v___x_7270_;
    } else {
        let mut v___x_7271_: u8 = 0;
        v___x_7271_ = lean_nat_dec_le(v___x_7268_, v___x_7268_);
        if v___x_7271_ == 0 {
            if v___x_7269_ == 0 {
                let mut v___x_7272_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_onErr_7257_);
                leanh::lean_dec_ref(v_eval_7255_);
                v___x_7272_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7272_, 0, v_init_7258_);
                return v___x_7272_;
            } else {
                let mut v___x_7273_: usize = 0;
                let mut v___x_7274_: usize = 0;
                let mut v___x_7275_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_7273_ = 0usize;
                v___x_7274_ = lean_usize_of_nat(v___x_7268_);
                v___x_7275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_7255_, v_logExceptions_7256_, v_onErr_7257_, v_cfgs_7259_, v___x_7273_, v___x_7274_, v_init_7258_, v___y_7260_, v___y_7261_, v___y_7262_, v___y_7263_, v___y_7264_, v___y_7265_);
                return v___x_7275_;
            }
        } else {
            let mut v___x_7276_: usize = 0;
            let mut v___x_7277_: usize = 0;
            let mut v___x_7278_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_7276_ = 0usize;
            v___x_7277_ = lean_usize_of_nat(v___x_7268_);
            v___x_7278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_7255_, v_logExceptions_7256_, v_onErr_7257_, v_cfgs_7259_, v___x_7276_, v___x_7277_, v_init_7258_, v___y_7260_, v___y_7261_, v___y_7262_, v___y_7263_, v___y_7264_, v___y_7265_);
            return v___x_7278_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(
    mut v_eval_7279_: *mut leanh::LeanObject,
    mut v_logExceptions_7280_: u8,
    mut v_onErr_7281_: *mut leanh::LeanObject,
    mut v_init_7282_: *mut leanh::LeanObject,
    mut v_cfg_7283_: *mut leanh::LeanObject,
    mut v___y_7284_: *mut leanh::LeanObject,
    mut v___y_7285_: *mut leanh::LeanObject,
    mut v___y_7286_: *mut leanh::LeanObject,
    mut v___y_7287_: *mut leanh::LeanObject,
    mut v___y_7288_: *mut leanh::LeanObject,
    mut v___y_7289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_7292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_7303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7315_: u8 = 0;
    let mut v_cancelTk_x3f_7316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7317_: u8 = 0;
    let mut v_inheritedTraceOptions_7318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: u8 = 0;
    let mut v___x_7324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7326_: u8 = 0;
    let mut v_atomAsIdent_7327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7328_: u8 = 0;
    let mut v_info_7329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7347_: u8 = 0;
    let mut v___x_7348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7349_: u8 = 0;
    let mut v___x_7350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: u8 = 0;
    let mut v___x_7360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: u8 = 0;
    let mut v___x_7362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: u8 = 0;
    let mut v___x_7364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7365_: u8 = 0;
    let mut v___x_7366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7322_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1;
                leanh::lean_inc(v_cfg_7283_);
                v___x_7323_ = l_Lean_Syntax_isOfKind(v_cfg_7283_, v___x_7322_);
                if v___x_7323_ == 0 {
                    v___x_7324_ = l_Lean_Syntax_getNumArgs(v_cfg_7283_);
                    v___x_7325_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7326_ = lean_nat_dec_eq(v___x_7324_, v___x_7325_);
                    if v___x_7326_ == 0 {
                        v_atomAsIdent_7327_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0;
                        v___x_7328_ = lean_nat_dec_le(v___x_7325_, v___x_7324_);
                        if v___x_7328_ == 0 {
                            leanh::lean_dec(v___x_7324_);
                            if leanh::lean_obj_tag(v_cfg_7283_) == 2 {
                                leanh::lean_dec_ref(v_onErr_7281_);
                                v_info_7329_ = leanh::lean_ctor_get(v_cfg_7283_, 0);
                                v_val_7330_ = leanh::lean_ctor_get(v_cfg_7283_, 1);
                                leanh::lean_inc_ref(v_val_7330_);
                                leanh::lean_inc(v_info_7329_);
                                v___x_7331_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(v_info_7329_, v_val_7330_);
                                v___x_7332_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7;
                                v___x_7333_ =
                                    l_Lean_mkCIdentFrom(v_cfg_7283_, v___x_7332_, v___x_7326_);
                                v___x_7334_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8;
                                v___x_7335_ = l_Lean_TSyntax_getId(v___x_7331_);
                                v___x_7336_ = lean_erase_macro_scopes(v___x_7335_);
                                v___x_7337_ = leanh::lean_box(0);
                                leanh::lean_inc(v___x_7331_);
                                v___x_7338_ =
                                    l_Lean_Syntax_identComponents(v___x_7331_, v___x_7337_);
                                v___x_7339_ = leanh::lean_box(0);
                                v___x_7340_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                                leanh::lean_ctor_set(v___x_7340_, 0, v_cfg_7283_);
                                leanh::lean_ctor_set(v___x_7340_, 1, v___x_7331_);
                                leanh::lean_ctor_set(v___x_7340_, 2, v___x_7333_);
                                leanh::lean_ctor_set(v___x_7340_, 3, v___x_7334_);
                                leanh::lean_ctor_set(v___x_7340_, 4, v___x_7336_);
                                leanh::lean_ctor_set(v___x_7340_, 5, v___x_7338_);
                                leanh::lean_ctor_set(v___x_7340_, 6, v___x_7339_);
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
                                leanh::lean_dec_ref(v_eval_7279_);
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_7342_ = leanh::lean_unsigned_to_nat(0);
                            v___x_7343_ = l_Lean_Syntax_getArg(v_cfg_7283_, v___x_7342_);
                            if leanh::lean_obj_tag(v___x_7343_) == 2 {
                                v_val_7344_ = leanh::lean_ctor_get(v___x_7343_, 1);
                                leanh::lean_inc_ref(v_val_7344_);
                                v___x_7358_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11;
                                v___x_7359_ = lean_string_dec_eq(v_val_7344_, v___x_7358_);
                                if v___x_7359_ == 0 {
                                    v___x_7360_ =
                                        l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12;
                                    v___x_7361_ = lean_string_dec_eq(v_val_7344_, v___x_7360_);
                                    if v___x_7361_ == 0 {
                                        leanh::lean_dec_ref_known(v___x_7343_, 2);
                                        v___x_7362_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13;
                                        v___x_7363_ = lean_string_dec_eq(v_val_7344_, v___x_7362_);
                                        leanh::lean_dec_ref(v_val_7344_);
                                        if v___x_7363_ == 0 {
                                            leanh::lean_dec(v___x_7324_);
                                            leanh::lean_dec_ref(v_eval_7279_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_7364_ = leanh::lean_unsigned_to_nat(5);
                                            v___x_7365_ = lean_nat_dec_le(v___x_7324_, v___x_7364_);
                                            leanh::lean_dec(v___x_7324_);
                                            if v___x_7365_ == 0 {
                                                leanh::lean_dec_ref(v_eval_7279_);
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_7366_ =
                                                    l_Lean_Syntax_getArg(v_cfg_7283_, v___x_7325_);
                                                v___x_7367_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_7327_, v___x_7366_);
                                                if leanh::lean_obj_tag(v___x_7367_) == 1 {
                                                    leanh::lean_dec_ref(v_onErr_7281_);
                                                    v_val_7368_ =
                                                        leanh::lean_ctor_get(v___x_7367_, 0);
                                                    leanh::lean_inc_n(v_val_7368_, 2);
                                                    leanh::lean_dec_ref_known(
                                                        v___x_7367_,
                                                        1,
                                                    );
                                                    v___x_7369_ =
                                                        leanh::lean_unsigned_to_nat(3);
                                                    v___x_7370_ = l_Lean_Syntax_getArg(
                                                        v_cfg_7283_,
                                                        v___x_7369_,
                                                    );
                                                    v___x_7371_ = leanh::lean_box(0);
                                                    v___x_7372_ = l_Lean_TSyntax_getId(v_val_7368_);
                                                    v___x_7373_ =
                                                        lean_erase_macro_scopes(v___x_7372_);
                                                    v___x_7374_ = l_Lean_Syntax_identComponents(
                                                        v_val_7368_,
                                                        v___x_7371_,
                                                    );
                                                    v___x_7375_ = leanh::lean_box(0);
                                                    v___x_7376_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        7,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        0,
                                                        v_cfg_7283_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        1,
                                                        v_val_7368_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        2,
                                                        v___x_7370_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        3,
                                                        v___x_7371_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        4,
                                                        v___x_7373_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        5,
                                                        v___x_7374_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_7376_,
                                                        6,
                                                        v___x_7375_,
                                                    );
                                                    v___x_7377_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_7279_, v_init_7282_, v___x_7376_, v_logExceptions_7280_, v___y_7284_, v___y_7285_, v___y_7286_, v___y_7287_, v___y_7288_, v___y_7289_);
                                                    return v___x_7377_;
                                                } else {
                                                    leanh::lean_dec(v___x_7367_);
                                                    leanh::lean_dec_ref(v_eval_7279_);
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_val_7344_);
                                        v___x_7378_ =
                                            leanh::lean_box((v___x_7326_) as usize);
                                        v___x_7379_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(v___x_7379_, 0, v___x_7378_);
                                        v___y_7346_ = v___x_7379_;
                                        v_val_7347_ = v___x_7326_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_val_7344_);
                                    v___x_7380_ = leanh::lean_box((v___x_7359_) as usize);
                                    v___x_7381_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_7381_, 0, v___x_7380_);
                                    v___y_7346_ = v___x_7381_;
                                    v_val_7347_ = v___x_7359_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_7343_);
                                leanh::lean_dec(v___x_7324_);
                                leanh::lean_dec_ref(v_eval_7279_);
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_7324_);
                        v___x_7382_ = leanh::lean_unsigned_to_nat(0);
                        v___x_7383_ = l_Lean_Syntax_getArg(v_cfg_7283_, v___x_7382_);
                        leanh::lean_dec(v_cfg_7283_);
                        v_cfg_7283_ = v___x_7383_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_7385_ = l_Lean_Syntax_getArgs(v_cfg_7283_);
                    leanh::lean_dec(v_cfg_7283_);
                    v___x_7386_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7279_, v_logExceptions_7280_, v_onErr_7281_, v_init_7282_, v___x_7385_, v___y_7284_, v___y_7285_, v___y_7286_, v___y_7287_, v___y_7288_, v___y_7289_);
                    leanh::lean_dec_ref(v___x_7385_);
                    return v___x_7386_;
                }
            }
            1 => {
                v___x_7295_ = l_Lean_TSyntax_getId(v___y_7292_);
                v___x_7296_ = lean_erase_macro_scopes(v___x_7295_);
                v___x_7297_ = leanh::lean_box(0);
                leanh::lean_inc(v___y_7292_);
                v___x_7298_ = l_Lean_Syntax_identComponents(v___y_7292_, v___x_7297_);
                v___x_7299_ = leanh::lean_box(0);
                v___x_7300_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                leanh::lean_ctor_set(v___x_7300_, 0, v_cfg_7283_);
                leanh::lean_ctor_set(v___x_7300_, 1, v___y_7292_);
                leanh::lean_ctor_set(v___x_7300_, 2, v___y_7294_);
                leanh::lean_ctor_set(v___x_7300_, 3, v___y_7293_);
                leanh::lean_ctor_set(v___x_7300_, 4, v___x_7296_);
                leanh::lean_ctor_set(v___x_7300_, 5, v___x_7298_);
                leanh::lean_ctor_set(v___x_7300_, 6, v___x_7299_);
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
                v_fileName_7303_ = leanh::lean_ctor_get(v___y_7288_, 0);
                v_fileMap_7304_ = leanh::lean_ctor_get(v___y_7288_, 1);
                v_options_7305_ = leanh::lean_ctor_get(v___y_7288_, 2);
                v_currRecDepth_7306_ = leanh::lean_ctor_get(v___y_7288_, 3);
                v_maxRecDepth_7307_ = leanh::lean_ctor_get(v___y_7288_, 4);
                v_ref_7308_ = leanh::lean_ctor_get(v___y_7288_, 5);
                v_currNamespace_7309_ = leanh::lean_ctor_get(v___y_7288_, 6);
                v_openDecls_7310_ = leanh::lean_ctor_get(v___y_7288_, 7);
                v_initHeartbeats_7311_ = leanh::lean_ctor_get(v___y_7288_, 8);
                v_maxHeartbeats_7312_ = leanh::lean_ctor_get(v___y_7288_, 9);
                v_quotContext_7313_ = leanh::lean_ctor_get(v___y_7288_, 10);
                v_currMacroScope_7314_ = leanh::lean_ctor_get(v___y_7288_, 11);
                v_diag_7315_ = leanh::lean_ctor_get_uint8(
                    v___y_7288_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7316_ = leanh::lean_ctor_get(v___y_7288_, 12);
                v_suppressElabErrors_7317_ = leanh::lean_ctor_get_uint8(
                    v___y_7288_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7318_ = leanh::lean_ctor_get(v___y_7288_, 13);
                v_ref_7319_ = l_Lean_replaceRef(v_cfg_7283_, v_ref_7308_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_7318_);
                leanh::lean_inc(v_cancelTk_x3f_7316_);
                leanh::lean_inc(v_currMacroScope_7314_);
                leanh::lean_inc(v_quotContext_7313_);
                leanh::lean_inc(v_maxHeartbeats_7312_);
                leanh::lean_inc(v_initHeartbeats_7311_);
                leanh::lean_inc(v_openDecls_7310_);
                leanh::lean_inc(v_currNamespace_7309_);
                leanh::lean_inc(v_maxRecDepth_7307_);
                leanh::lean_inc(v_currRecDepth_7306_);
                leanh::lean_inc_ref(v_options_7305_);
                leanh::lean_inc_ref(v_fileMap_7304_);
                leanh::lean_inc_ref(v_fileName_7303_);
                v___x_7320_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_7320_, 0, v_fileName_7303_);
                leanh::lean_ctor_set(v___x_7320_, 1, v_fileMap_7304_);
                leanh::lean_ctor_set(v___x_7320_, 2, v_options_7305_);
                leanh::lean_ctor_set(v___x_7320_, 3, v_currRecDepth_7306_);
                leanh::lean_ctor_set(v___x_7320_, 4, v_maxRecDepth_7307_);
                leanh::lean_ctor_set(v___x_7320_, 5, v_ref_7319_);
                leanh::lean_ctor_set(v___x_7320_, 6, v_currNamespace_7309_);
                leanh::lean_ctor_set(v___x_7320_, 7, v_openDecls_7310_);
                leanh::lean_ctor_set(v___x_7320_, 8, v_initHeartbeats_7311_);
                leanh::lean_ctor_set(v___x_7320_, 9, v_maxHeartbeats_7312_);
                leanh::lean_ctor_set(v___x_7320_, 10, v_quotContext_7313_);
                leanh::lean_ctor_set(v___x_7320_, 11, v_currMacroScope_7314_);
                leanh::lean_ctor_set(v___x_7320_, 12, v_cancelTk_x3f_7316_);
                leanh::lean_ctor_set(v___x_7320_, 13, v_inheritedTraceOptions_7318_);
                leanh::lean_ctor_set_uint8(
                    v___x_7320_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_7315_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_7320_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7317_,
                );
                leanh::lean_inc(v___y_7289_);
                leanh::lean_inc(v___y_7287_);
                leanh::lean_inc_ref(v___y_7286_);
                leanh::lean_inc(v___y_7285_);
                leanh::lean_inc_ref(v___y_7284_);
                v___x_7321_ = leanh::lean_apply_9(
                    v_onErr_7281_,
                    v_init_7282_,
                    v_cfg_7283_,
                    v___y_7284_,
                    v___y_7285_,
                    v___y_7286_,
                    v___y_7287_,
                    v___x_7320_,
                    v___y_7289_,
                    leanh::lean_box(0),
                );
                return v___x_7321_;
            }
            3 => {
                v___x_7348_ = leanh::lean_unsigned_to_nat(2);
                v___x_7349_ = lean_nat_dec_eq(v___x_7324_, v___x_7348_);
                leanh::lean_dec(v___x_7324_);
                if v___x_7349_ == 0 {
                    leanh::lean_dec(v___y_7346_);
                    leanh::lean_dec_ref_known(v___x_7343_, 2);
                    leanh::lean_dec_ref(v_eval_7279_);
                    state = 2;
                    continue;
                } else {
                    v___x_7350_ = l_Lean_Syntax_getArg(v_cfg_7283_, v___x_7325_);
                    v___x_7351_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(
                        v_atomAsIdent_7327_,
                        v___x_7350_,
                    );
                    if leanh::lean_obj_tag(v___x_7351_) == 1 {
                        leanh::lean_dec_ref(v_onErr_7281_);
                        if v_val_7347_ == 0 {
                            v_val_7352_ = leanh::lean_ctor_get(v___x_7351_, 0);
                            leanh::lean_inc(v_val_7352_);
                            leanh::lean_dec_ref_known(v___x_7351_, 1);
                            v___x_7353_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10;
                            v___x_7354_ =
                                l_Lean_mkCIdentFrom(v___x_7343_, v___x_7353_, v___x_7326_);
                            leanh::lean_dec_ref_known(v___x_7343_, 2);
                            v___y_7292_ = v_val_7352_;
                            v___y_7293_ = v___y_7346_;
                            v___y_7294_ = v___x_7354_;
                            state = 1;
                            continue;
                        } else {
                            v_val_7355_ = leanh::lean_ctor_get(v___x_7351_, 0);
                            leanh::lean_inc(v_val_7355_);
                            leanh::lean_dec_ref_known(v___x_7351_, 1);
                            v___x_7356_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7;
                            v___x_7357_ =
                                l_Lean_mkCIdentFrom(v___x_7343_, v___x_7356_, v___x_7326_);
                            leanh::lean_dec_ref_known(v___x_7343_, 2);
                            v___y_7292_ = v_val_7355_;
                            v___y_7293_ = v___y_7346_;
                            v___y_7294_ = v___x_7357_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_7351_);
                        leanh::lean_dec(v___y_7346_);
                        leanh::lean_dec_ref_known(v___x_7343_, 2);
                        leanh::lean_dec_ref(v_eval_7279_);
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
    mut v_eval_7387_: *mut leanh::LeanObject,
    mut v_logExceptions_7388_: u8,
    mut v_onErr_7389_: *mut leanh::LeanObject,
    mut v_as_7390_: *mut leanh::LeanObject,
    mut v_i_7391_: usize,
    mut v_stop_7392_: usize,
    mut v_b_7393_: *mut leanh::LeanObject,
    mut v___y_7394_: *mut leanh::LeanObject,
    mut v___y_7395_: *mut leanh::LeanObject,
    mut v___y_7396_: *mut leanh::LeanObject,
    mut v___y_7397_: *mut leanh::LeanObject,
    mut v___y_7398_: *mut leanh::LeanObject,
    mut v___y_7399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7401_: u8 = 0;
    let mut v___x_7402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: usize = 0;
    let mut v___x_7406_: usize = 0;
    let mut v___x_7408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7401_ = lean_usize_dec_eq(v_i_7391_, v_stop_7392_);
                if v___x_7401_ == 0 {
                    v___x_7402_ = lean_array_uget_borrowed(v_as_7390_, v_i_7391_);
                    leanh::lean_inc(v___x_7402_);
                    leanh::lean_inc_ref(v_onErr_7389_);
                    leanh::lean_inc_ref(v_eval_7387_);
                    v___x_7403_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7387_, v_logExceptions_7388_, v_onErr_7389_, v_b_7393_, v___x_7402_, v___y_7394_, v___y_7395_, v___y_7396_, v___y_7397_, v___y_7398_, v___y_7399_);
                    if leanh::lean_obj_tag(v___x_7403_) == 0 {
                        v_a_7404_ = leanh::lean_ctor_get(v___x_7403_, 0);
                        leanh::lean_inc(v_a_7404_);
                        leanh::lean_dec_ref_known(v___x_7403_, 1);
                        v___x_7405_ = 1usize;
                        v___x_7406_ = lean_usize_add(v_i_7391_, v___x_7405_);
                        v_i_7391_ = v___x_7406_;
                        v_b_7393_ = v_a_7404_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_onErr_7389_);
                        leanh::lean_dec_ref(v_eval_7387_);
                        return v___x_7403_;
                    }
                } else {
                    leanh::lean_dec_ref(v_onErr_7389_);
                    leanh::lean_dec_ref(v_eval_7387_);
                    v___x_7408_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7408_, 0, v_b_7393_);
                    return v___x_7408_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_eval_7409_: *mut leanh::LeanObject,
    mut v_logExceptions_7410_: *mut leanh::LeanObject,
    mut v_onErr_7411_: *mut leanh::LeanObject,
    mut v_as_7412_: *mut leanh::LeanObject,
    mut v_i_7413_: *mut leanh::LeanObject,
    mut v_stop_7414_: *mut leanh::LeanObject,
    mut v_b_7415_: *mut leanh::LeanObject,
    mut v___y_7416_: *mut leanh::LeanObject,
    mut v___y_7417_: *mut leanh::LeanObject,
    mut v___y_7418_: *mut leanh::LeanObject,
    mut v___y_7419_: *mut leanh::LeanObject,
    mut v___y_7420_: *mut leanh::LeanObject,
    mut v___y_7421_: *mut leanh::LeanObject,
    mut v___y_7422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_7423_: u8 = 0;
    let mut v_i_boxed_7424_: usize = 0;
    let mut v_stop_boxed_7425_: usize = 0;
    let mut v_res_7426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7423_ = (leanh::lean_unbox(v_logExceptions_7410_) as u8);
    v_i_boxed_7424_ = leanh::lean_unbox_usize(v_i_7413_);
    leanh::lean_dec(v_i_7413_);
    v_stop_boxed_7425_ = leanh::lean_unbox_usize(v_stop_7414_);
    leanh::lean_dec(v_stop_7414_);
    v_res_7426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_7409_, v_logExceptions_boxed_7423_, v_onErr_7411_, v_as_7412_, v_i_boxed_7424_, v_stop_boxed_7425_, v_b_7415_, v___y_7416_, v___y_7417_, v___y_7418_, v___y_7419_, v___y_7420_, v___y_7421_);
    leanh::lean_dec(v___y_7421_);
    leanh::lean_dec_ref(v___y_7420_);
    leanh::lean_dec(v___y_7419_);
    leanh::lean_dec_ref(v___y_7418_);
    leanh::lean_dec(v___y_7417_);
    leanh::lean_dec_ref(v___y_7416_);
    leanh::lean_dec_ref(v_as_7412_);
    return v_res_7426_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg___boxed(
    mut v_eval_7427_: *mut leanh::LeanObject,
    mut v_logExceptions_7428_: *mut leanh::LeanObject,
    mut v_onErr_7429_: *mut leanh::LeanObject,
    mut v_init_7430_: *mut leanh::LeanObject,
    mut v_cfgs_7431_: *mut leanh::LeanObject,
    mut v___y_7432_: *mut leanh::LeanObject,
    mut v___y_7433_: *mut leanh::LeanObject,
    mut v___y_7434_: *mut leanh::LeanObject,
    mut v___y_7435_: *mut leanh::LeanObject,
    mut v___y_7436_: *mut leanh::LeanObject,
    mut v___y_7437_: *mut leanh::LeanObject,
    mut v___y_7438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_7439_: u8 = 0;
    let mut v_res_7440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7439_ = (leanh::lean_unbox(v_logExceptions_7428_) as u8);
    v_res_7440_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7427_, v_logExceptions_boxed_7439_, v_onErr_7429_, v_init_7430_, v_cfgs_7431_, v___y_7432_, v___y_7433_, v___y_7434_, v___y_7435_, v___y_7436_, v___y_7437_);
    leanh::lean_dec(v___y_7437_);
    leanh::lean_dec_ref(v___y_7436_);
    leanh::lean_dec(v___y_7435_);
    leanh::lean_dec_ref(v___y_7434_);
    leanh::lean_dec(v___y_7433_);
    leanh::lean_dec_ref(v___y_7432_);
    leanh::lean_dec_ref(v_cfgs_7431_);
    return v_res_7440_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___boxed(
    mut v_eval_7441_: *mut leanh::LeanObject,
    mut v_logExceptions_7442_: *mut leanh::LeanObject,
    mut v_onErr_7443_: *mut leanh::LeanObject,
    mut v_init_7444_: *mut leanh::LeanObject,
    mut v_cfg_7445_: *mut leanh::LeanObject,
    mut v___y_7446_: *mut leanh::LeanObject,
    mut v___y_7447_: *mut leanh::LeanObject,
    mut v___y_7448_: *mut leanh::LeanObject,
    mut v___y_7449_: *mut leanh::LeanObject,
    mut v___y_7450_: *mut leanh::LeanObject,
    mut v___y_7451_: *mut leanh::LeanObject,
    mut v___y_7452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_7453_: u8 = 0;
    let mut v_res_7454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7453_ = (leanh::lean_unbox(v_logExceptions_7442_) as u8);
    v_res_7454_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7441_, v_logExceptions_boxed_7453_, v_onErr_7443_, v_init_7444_, v_cfg_7445_, v___y_7446_, v___y_7447_, v___y_7448_, v___y_7449_, v___y_7450_, v___y_7451_);
    leanh::lean_dec(v___y_7451_);
    leanh::lean_dec_ref(v___y_7450_);
    leanh::lean_dec(v___y_7449_);
    leanh::lean_dec_ref(v___y_7448_);
    leanh::lean_dec(v___y_7447_);
    leanh::lean_dec_ref(v___y_7446_);
    return v_res_7454_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(
    mut v_eval_7455_: *mut leanh::LeanObject,
    mut v_init_7456_: *mut leanh::LeanObject,
    mut v_cfg_7457_: *mut leanh::LeanObject,
    mut v_onErr_7458_: *mut leanh::LeanObject,
    mut v_logExceptions_7459_: u8,
    mut v_a_7460_: *mut leanh::LeanObject,
    mut v_a_7461_: *mut leanh::LeanObject,
    mut v_a_7462_: *mut leanh::LeanObject,
    mut v_a_7463_: *mut leanh::LeanObject,
    mut v_a_7464_: *mut leanh::LeanObject,
    mut v_a_7465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7467_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7455_, v_logExceptions_7459_, v_onErr_7458_, v_init_7456_, v_cfg_7457_, v_a_7460_, v_a_7461_, v_a_7462_, v_a_7463_, v_a_7464_, v_a_7465_);
    return v___x_7467_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg___boxed(
    mut v_eval_7468_: *mut leanh::LeanObject,
    mut v_init_7469_: *mut leanh::LeanObject,
    mut v_cfg_7470_: *mut leanh::LeanObject,
    mut v_onErr_7471_: *mut leanh::LeanObject,
    mut v_logExceptions_7472_: *mut leanh::LeanObject,
    mut v_a_7473_: *mut leanh::LeanObject,
    mut v_a_7474_: *mut leanh::LeanObject,
    mut v_a_7475_: *mut leanh::LeanObject,
    mut v_a_7476_: *mut leanh::LeanObject,
    mut v_a_7477_: *mut leanh::LeanObject,
    mut v_a_7478_: *mut leanh::LeanObject,
    mut v_a_7479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_7480_: u8 = 0;
    let mut v_res_7481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7480_ = (leanh::lean_unbox(v_logExceptions_7472_) as u8);
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
    leanh::lean_dec(v_a_7478_);
    leanh::lean_dec_ref(v_a_7477_);
    leanh::lean_dec(v_a_7476_);
    leanh::lean_dec_ref(v_a_7475_);
    leanh::lean_dec(v_a_7474_);
    leanh::lean_dec_ref(v_a_7473_);
    return v_res_7481_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(
    mut v_00_u03b1_7482_: *mut leanh::LeanObject,
    mut v_eval_7483_: *mut leanh::LeanObject,
    mut v_init_7484_: *mut leanh::LeanObject,
    mut v_cfg_7485_: *mut leanh::LeanObject,
    mut v_onErr_7486_: *mut leanh::LeanObject,
    mut v_logExceptions_7487_: u8,
    mut v_a_7488_: *mut leanh::LeanObject,
    mut v_a_7489_: *mut leanh::LeanObject,
    mut v_a_7490_: *mut leanh::LeanObject,
    mut v_a_7491_: *mut leanh::LeanObject,
    mut v_a_7492_: *mut leanh::LeanObject,
    mut v_a_7493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7495_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7483_, v_logExceptions_7487_, v_onErr_7486_, v_init_7484_, v_cfg_7485_, v_a_7488_, v_a_7489_, v_a_7490_, v_a_7491_, v_a_7492_, v_a_7493_);
    return v___x_7495_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___boxed(
    mut v_00_u03b1_7496_: *mut leanh::LeanObject,
    mut v_eval_7497_: *mut leanh::LeanObject,
    mut v_init_7498_: *mut leanh::LeanObject,
    mut v_cfg_7499_: *mut leanh::LeanObject,
    mut v_onErr_7500_: *mut leanh::LeanObject,
    mut v_logExceptions_7501_: *mut leanh::LeanObject,
    mut v_a_7502_: *mut leanh::LeanObject,
    mut v_a_7503_: *mut leanh::LeanObject,
    mut v_a_7504_: *mut leanh::LeanObject,
    mut v_a_7505_: *mut leanh::LeanObject,
    mut v_a_7506_: *mut leanh::LeanObject,
    mut v_a_7507_: *mut leanh::LeanObject,
    mut v_a_7508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_7509_: u8 = 0;
    let mut v_res_7510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7509_ = (leanh::lean_unbox(v_logExceptions_7501_) as u8);
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
    leanh::lean_dec(v_a_7507_);
    leanh::lean_dec_ref(v_a_7506_);
    leanh::lean_dec(v_a_7505_);
    leanh::lean_dec_ref(v_a_7504_);
    leanh::lean_dec(v_a_7503_);
    leanh::lean_dec_ref(v_a_7502_);
    return v_res_7510_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(
    mut v_00_u03b1_7511_: *mut leanh::LeanObject,
    mut v_eval_7512_: *mut leanh::LeanObject,
    mut v_logExceptions_7513_: u8,
    mut v_onErr_7514_: *mut leanh::LeanObject,
    mut v_init_7515_: *mut leanh::LeanObject,
    mut v_cfg_7516_: *mut leanh::LeanObject,
    mut v___y_7517_: *mut leanh::LeanObject,
    mut v___y_7518_: *mut leanh::LeanObject,
    mut v___y_7519_: *mut leanh::LeanObject,
    mut v___y_7520_: *mut leanh::LeanObject,
    mut v___y_7521_: *mut leanh::LeanObject,
    mut v___y_7522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7524_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7512_, v_logExceptions_7513_, v_onErr_7514_, v_init_7515_, v_cfg_7516_, v___y_7517_, v___y_7518_, v___y_7519_, v___y_7520_, v___y_7521_, v___y_7522_);
    return v___x_7524_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___boxed(
    mut v_00_u03b1_7525_: *mut leanh::LeanObject,
    mut v_eval_7526_: *mut leanh::LeanObject,
    mut v_logExceptions_7527_: *mut leanh::LeanObject,
    mut v_onErr_7528_: *mut leanh::LeanObject,
    mut v_init_7529_: *mut leanh::LeanObject,
    mut v_cfg_7530_: *mut leanh::LeanObject,
    mut v___y_7531_: *mut leanh::LeanObject,
    mut v___y_7532_: *mut leanh::LeanObject,
    mut v___y_7533_: *mut leanh::LeanObject,
    mut v___y_7534_: *mut leanh::LeanObject,
    mut v___y_7535_: *mut leanh::LeanObject,
    mut v___y_7536_: *mut leanh::LeanObject,
    mut v___y_7537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_7538_: u8 = 0;
    let mut v_res_7539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7538_ = (leanh::lean_unbox(v_logExceptions_7527_) as u8);
    v_res_7539_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(v_00_u03b1_7525_, v_eval_7526_, v_logExceptions_boxed_7538_, v_onErr_7528_, v_init_7529_, v_cfg_7530_, v___y_7531_, v___y_7532_, v___y_7533_, v___y_7534_, v___y_7535_, v___y_7536_);
    leanh::lean_dec(v___y_7536_);
    leanh::lean_dec_ref(v___y_7535_);
    leanh::lean_dec(v___y_7534_);
    leanh::lean_dec_ref(v___y_7533_);
    leanh::lean_dec(v___y_7532_);
    leanh::lean_dec_ref(v___y_7531_);
    return v_res_7539_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(
    mut v_00_u03b1_7540_: *mut leanh::LeanObject,
    mut v_eval_7541_: *mut leanh::LeanObject,
    mut v_logExceptions_7542_: u8,
    mut v_onErr_7543_: *mut leanh::LeanObject,
    mut v_init_7544_: *mut leanh::LeanObject,
    mut v_cfgs_7545_: *mut leanh::LeanObject,
    mut v___y_7546_: *mut leanh::LeanObject,
    mut v___y_7547_: *mut leanh::LeanObject,
    mut v___y_7548_: *mut leanh::LeanObject,
    mut v___y_7549_: *mut leanh::LeanObject,
    mut v___y_7550_: *mut leanh::LeanObject,
    mut v___y_7551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7553_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7541_, v_logExceptions_7542_, v_onErr_7543_, v_init_7544_, v_cfgs_7545_, v___y_7546_, v___y_7547_, v___y_7548_, v___y_7549_, v___y_7550_, v___y_7551_);
    return v___x_7553_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___boxed(
    mut v_00_u03b1_7554_: *mut leanh::LeanObject,
    mut v_eval_7555_: *mut leanh::LeanObject,
    mut v_logExceptions_7556_: *mut leanh::LeanObject,
    mut v_onErr_7557_: *mut leanh::LeanObject,
    mut v_init_7558_: *mut leanh::LeanObject,
    mut v_cfgs_7559_: *mut leanh::LeanObject,
    mut v___y_7560_: *mut leanh::LeanObject,
    mut v___y_7561_: *mut leanh::LeanObject,
    mut v___y_7562_: *mut leanh::LeanObject,
    mut v___y_7563_: *mut leanh::LeanObject,
    mut v___y_7564_: *mut leanh::LeanObject,
    mut v___y_7565_: *mut leanh::LeanObject,
    mut v___y_7566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_7567_: u8 = 0;
    let mut v_res_7568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7567_ = (leanh::lean_unbox(v_logExceptions_7556_) as u8);
    v_res_7568_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(v_00_u03b1_7554_, v_eval_7555_, v_logExceptions_boxed_7567_, v_onErr_7557_, v_init_7558_, v_cfgs_7559_, v___y_7560_, v___y_7561_, v___y_7562_, v___y_7563_, v___y_7564_, v___y_7565_);
    leanh::lean_dec(v___y_7565_);
    leanh::lean_dec_ref(v___y_7564_);
    leanh::lean_dec(v___y_7563_);
    leanh::lean_dec_ref(v___y_7562_);
    leanh::lean_dec(v___y_7561_);
    leanh::lean_dec_ref(v___y_7560_);
    leanh::lean_dec_ref(v_cfgs_7559_);
    return v_res_7568_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(
    mut v_s_7569_: *mut leanh::LeanObject,
    mut v_inst_7570_: *mut leanh::LeanObject,
    mut v_R_7571_: *mut leanh::LeanObject,
    mut v_a_7572_: *mut leanh::LeanObject,
    mut v_b_7573_: u8,
    mut v_c_7574_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7575_: u8 = 0;
    v___x_7575_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_7569_, v_a_7572_, v_b_7573_);
    return v___x_7575_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___boxed(
    mut v_s_7576_: *mut leanh::LeanObject,
    mut v_inst_7577_: *mut leanh::LeanObject,
    mut v_R_7578_: *mut leanh::LeanObject,
    mut v_a_7579_: *mut leanh::LeanObject,
    mut v_b_7580_: *mut leanh::LeanObject,
    mut v_c_7581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_7582_: u8 = 0;
    let mut v_res_7583_: u8 = 0;
    let mut v_r_7584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_7582_ = (leanh::lean_unbox(v_b_7580_) as u8);
    v_res_7583_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(v_s_7576_, v_inst_7577_, v_R_7578_, v_a_7579_, v_b_boxed_7582_, v_c_7581_);
    leanh::lean_dec_ref(v_s_7576_);
    v_r_7584_ = leanh::lean_box((v_res_7583_) as usize);
    return v_r_7584_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(
    mut v_00_u03b1_7585_: *mut leanh::LeanObject,
    mut v_eval_7586_: *mut leanh::LeanObject,
    mut v_logExceptions_7587_: u8,
    mut v_onErr_7588_: *mut leanh::LeanObject,
    mut v_as_7589_: *mut leanh::LeanObject,
    mut v_i_7590_: usize,
    mut v_stop_7591_: usize,
    mut v_b_7592_: *mut leanh::LeanObject,
    mut v___y_7593_: *mut leanh::LeanObject,
    mut v___y_7594_: *mut leanh::LeanObject,
    mut v___y_7595_: *mut leanh::LeanObject,
    mut v___y_7596_: *mut leanh::LeanObject,
    mut v___y_7597_: *mut leanh::LeanObject,
    mut v___y_7598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_7586_, v_logExceptions_7587_, v_onErr_7588_, v_as_7589_, v_i_7590_, v_stop_7591_, v_b_7592_, v___y_7593_, v___y_7594_, v___y_7595_, v___y_7596_, v___y_7597_, v___y_7598_);
    return v___x_7600_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_7601_: *mut leanh::LeanObject,
    mut v_eval_7602_: *mut leanh::LeanObject,
    mut v_logExceptions_7603_: *mut leanh::LeanObject,
    mut v_onErr_7604_: *mut leanh::LeanObject,
    mut v_as_7605_: *mut leanh::LeanObject,
    mut v_i_7606_: *mut leanh::LeanObject,
    mut v_stop_7607_: *mut leanh::LeanObject,
    mut v_b_7608_: *mut leanh::LeanObject,
    mut v___y_7609_: *mut leanh::LeanObject,
    mut v___y_7610_: *mut leanh::LeanObject,
    mut v___y_7611_: *mut leanh::LeanObject,
    mut v___y_7612_: *mut leanh::LeanObject,
    mut v___y_7613_: *mut leanh::LeanObject,
    mut v___y_7614_: *mut leanh::LeanObject,
    mut v___y_7615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_7616_: u8 = 0;
    let mut v_i_boxed_7617_: usize = 0;
    let mut v_stop_boxed_7618_: usize = 0;
    let mut v_res_7619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7616_ = (leanh::lean_unbox(v_logExceptions_7603_) as u8);
    v_i_boxed_7617_ = leanh::lean_unbox_usize(v_i_7606_);
    leanh::lean_dec(v_i_7606_);
    v_stop_boxed_7618_ = leanh::lean_unbox_usize(v_stop_7607_);
    leanh::lean_dec(v_stop_7607_);
    v_res_7619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(v_00_u03b1_7601_, v_eval_7602_, v_logExceptions_boxed_7616_, v_onErr_7604_, v_as_7605_, v_i_boxed_7617_, v_stop_boxed_7618_, v_b_7608_, v___y_7609_, v___y_7610_, v___y_7611_, v___y_7612_, v___y_7613_, v___y_7614_);
    leanh::lean_dec(v___y_7614_);
    leanh::lean_dec_ref(v___y_7613_);
    leanh::lean_dec(v___y_7612_);
    leanh::lean_dec_ref(v___y_7611_);
    leanh::lean_dec(v___y_7610_);
    leanh::lean_dec_ref(v___y_7609_);
    leanh::lean_dec_ref(v_as_7605_);
    return v_res_7619_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(
    mut v_eval_7620_: *mut leanh::LeanObject,
    mut v_init_7621_: *mut leanh::LeanObject,
    mut v_cfgs_7622_: *mut leanh::LeanObject,
    mut v_onErr_7623_: *mut leanh::LeanObject,
    mut v_logExceptions_7624_: u8,
    mut v_a_7625_: *mut leanh::LeanObject,
    mut v_a_7626_: *mut leanh::LeanObject,
    mut v_a_7627_: *mut leanh::LeanObject,
    mut v_a_7628_: *mut leanh::LeanObject,
    mut v_a_7629_: *mut leanh::LeanObject,
    mut v_a_7630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7632_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7620_, v_logExceptions_7624_, v_onErr_7623_, v_init_7621_, v_cfgs_7622_, v_a_7625_, v_a_7626_, v_a_7627_, v_a_7628_, v_a_7629_, v_a_7630_);
    return v___x_7632_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg___boxed(
    mut v_eval_7633_: *mut leanh::LeanObject,
    mut v_init_7634_: *mut leanh::LeanObject,
    mut v_cfgs_7635_: *mut leanh::LeanObject,
    mut v_onErr_7636_: *mut leanh::LeanObject,
    mut v_logExceptions_7637_: *mut leanh::LeanObject,
    mut v_a_7638_: *mut leanh::LeanObject,
    mut v_a_7639_: *mut leanh::LeanObject,
    mut v_a_7640_: *mut leanh::LeanObject,
    mut v_a_7641_: *mut leanh::LeanObject,
    mut v_a_7642_: *mut leanh::LeanObject,
    mut v_a_7643_: *mut leanh::LeanObject,
    mut v_a_7644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_7645_: u8 = 0;
    let mut v_res_7646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7645_ = (leanh::lean_unbox(v_logExceptions_7637_) as u8);
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
    leanh::lean_dec(v_a_7643_);
    leanh::lean_dec_ref(v_a_7642_);
    leanh::lean_dec(v_a_7641_);
    leanh::lean_dec_ref(v_a_7640_);
    leanh::lean_dec(v_a_7639_);
    leanh::lean_dec_ref(v_a_7638_);
    leanh::lean_dec_ref(v_cfgs_7635_);
    return v_res_7646_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(
    mut v_00_u03b1_7647_: *mut leanh::LeanObject,
    mut v_eval_7648_: *mut leanh::LeanObject,
    mut v_init_7649_: *mut leanh::LeanObject,
    mut v_cfgs_7650_: *mut leanh::LeanObject,
    mut v_onErr_7651_: *mut leanh::LeanObject,
    mut v_logExceptions_7652_: u8,
    mut v_a_7653_: *mut leanh::LeanObject,
    mut v_a_7654_: *mut leanh::LeanObject,
    mut v_a_7655_: *mut leanh::LeanObject,
    mut v_a_7656_: *mut leanh::LeanObject,
    mut v_a_7657_: *mut leanh::LeanObject,
    mut v_a_7658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7660_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7648_, v_logExceptions_7652_, v_onErr_7651_, v_init_7649_, v_cfgs_7650_, v_a_7653_, v_a_7654_, v_a_7655_, v_a_7656_, v_a_7657_, v_a_7658_);
    return v___x_7660_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___boxed(
    mut v_00_u03b1_7661_: *mut leanh::LeanObject,
    mut v_eval_7662_: *mut leanh::LeanObject,
    mut v_init_7663_: *mut leanh::LeanObject,
    mut v_cfgs_7664_: *mut leanh::LeanObject,
    mut v_onErr_7665_: *mut leanh::LeanObject,
    mut v_logExceptions_7666_: *mut leanh::LeanObject,
    mut v_a_7667_: *mut leanh::LeanObject,
    mut v_a_7668_: *mut leanh::LeanObject,
    mut v_a_7669_: *mut leanh::LeanObject,
    mut v_a_7670_: *mut leanh::LeanObject,
    mut v_a_7671_: *mut leanh::LeanObject,
    mut v_a_7672_: *mut leanh::LeanObject,
    mut v_a_7673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_7674_: u8 = 0;
    let mut v_res_7675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7674_ = (leanh::lean_unbox(v_logExceptions_7666_) as u8);
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
    leanh::lean_dec(v_a_7672_);
    leanh::lean_dec_ref(v_a_7671_);
    leanh::lean_dec(v_a_7670_);
    leanh::lean_dec_ref(v_a_7669_);
    leanh::lean_dec(v_a_7668_);
    leanh::lean_dec_ref(v_a_7667_);
    leanh::lean_dec_ref(v_cfgs_7664_);
    return v_res_7675_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(
    mut v_x_7676_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7677_: u8 = 0;
    v___x_7677_ = 0;
    return v___x_7677_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed(
    mut v_x_7678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7679_: u8 = 0;
    let mut v_r_7680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7679_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(v_x_7678_);
    leanh::lean_dec(v_x_7678_);
    v_r_7680_ = leanh::lean_box((v_res_7679_) as usize);
    return v_r_7680_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(
    mut v___x_7681_: *mut leanh::LeanObject,
    mut v_ctx_x3f_7682_: *mut leanh::LeanObject,
    mut v_sz_7683_: usize,
    mut v_i_7684_: usize,
    mut v_bs_7685_: *mut leanh::LeanObject,
    mut v___y_7686_: *mut leanh::LeanObject,
    mut v___y_7687_: *mut leanh::LeanObject,
    mut v___y_7688_: *mut leanh::LeanObject,
    mut v___y_7689_: *mut leanh::LeanObject,
    mut v___y_7690_: *mut leanh::LeanObject,
    mut v___y_7691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7693_: u8 = 0;
    let mut v___x_7694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_7695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: usize = 0;
    let mut v___x_7704_: usize = 0;
    let mut v___x_7705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_7707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7713_: u8 = 0;
    let mut v___x_7715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7693_ = lean_usize_dec_lt(v_i_7684_, v_sz_7683_);
                if v___x_7693_ == 0 {
                    leanh::lean_dec_ref(v_ctx_x3f_7682_);
                    v___x_7694_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7694_, 0, v_bs_7685_);
                    return v___x_7694_;
                } else {
                    v_assignment_7695_ = leanh::lean_ctor_get(v___x_7681_, 0);
                    leanh::lean_inc_ref(v_ctx_x3f_7682_);
                    leanh::lean_inc(v___y_7691_);
                    leanh::lean_inc_ref(v___y_7690_);
                    leanh::lean_inc(v___y_7689_);
                    leanh::lean_inc_ref(v___y_7688_);
                    leanh::lean_inc(v___y_7687_);
                    leanh::lean_inc_ref(v___y_7686_);
                    v___x_7696_ = leanh::lean_apply_7(
                        v_ctx_x3f_7682_,
                        v___y_7686_,
                        v___y_7687_,
                        v___y_7688_,
                        v___y_7689_,
                        v___y_7690_,
                        v___y_7691_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_7696_) == 0 {
                        v_a_7697_ = leanh::lean_ctor_get(v___x_7696_, 0);
                        leanh::lean_inc(v_a_7697_);
                        leanh::lean_dec_ref_known(v___x_7696_, 1);
                        v_v_7698_ = lean_array_uget(v_bs_7685_, v_i_7684_);
                        v___x_7699_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_7700_ = lean_array_uset(v_bs_7685_, v_i_7684_, v___x_7699_);
                        v_tree_7707_ =
                            l_Lean_Elab_InfoTree_substitute(v_v_7698_, v_assignment_7695_);
                        if leanh::lean_obj_tag(v_a_7697_) == 0 {
                            v_a_7702_ = v_tree_7707_;
                            state = 1;
                            continue;
                        } else {
                            v_val_7708_ = leanh::lean_ctor_get(v_a_7697_, 0);
                            leanh::lean_inc(v_val_7708_);
                            leanh::lean_dec_ref_known(v_a_7697_, 1);
                            v___x_7709_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_7709_, 0, v_val_7708_);
                            leanh::lean_ctor_set(v___x_7709_, 1, v_tree_7707_);
                            v_a_7702_ = v___x_7709_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_bs_7685_);
                        leanh::lean_dec_ref(v_ctx_x3f_7682_);
                        v_a_7710_ = leanh::lean_ctor_get(v___x_7696_, 0);
                        v_isSharedCheck_7717_ =
                            (!leanh::lean_is_exclusive(v___x_7696_)) as u8;
                        if v_isSharedCheck_7717_ == 0 {
                            v___x_7712_ = v___x_7696_;
                            v_isShared_7713_ = v_isSharedCheck_7717_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7710_);
                            leanh::lean_dec(v___x_7696_);
                            v___x_7712_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_7716_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 0, v_a_7710_);
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
    mut v___x_7718_: *mut leanh::LeanObject,
    mut v_ctx_x3f_7719_: *mut leanh::LeanObject,
    mut v_sz_7720_: *mut leanh::LeanObject,
    mut v_i_7721_: *mut leanh::LeanObject,
    mut v_bs_7722_: *mut leanh::LeanObject,
    mut v___y_7723_: *mut leanh::LeanObject,
    mut v___y_7724_: *mut leanh::LeanObject,
    mut v___y_7725_: *mut leanh::LeanObject,
    mut v___y_7726_: *mut leanh::LeanObject,
    mut v___y_7727_: *mut leanh::LeanObject,
    mut v___y_7728_: *mut leanh::LeanObject,
    mut v___y_7729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7730_: usize = 0;
    let mut v_i_boxed_7731_: usize = 0;
    let mut v_res_7732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7730_ = leanh::lean_unbox_usize(v_sz_7720_);
    leanh::lean_dec(v_sz_7720_);
    v_i_boxed_7731_ = leanh::lean_unbox_usize(v_i_7721_);
    leanh::lean_dec(v_i_7721_);
    v_res_7732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_7718_, v_ctx_x3f_7719_, v_sz_boxed_7730_, v_i_boxed_7731_, v_bs_7722_, v___y_7723_, v___y_7724_, v___y_7725_, v___y_7726_, v___y_7727_, v___y_7728_);
    leanh::lean_dec(v___y_7728_);
    leanh::lean_dec_ref(v___y_7727_);
    leanh::lean_dec(v___y_7726_);
    leanh::lean_dec_ref(v___y_7725_);
    leanh::lean_dec(v___y_7724_);
    leanh::lean_dec_ref(v___y_7723_);
    leanh::lean_dec_ref(v___x_7718_);
    return v_res_7732_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(
    mut v___x_7733_: *mut leanh::LeanObject,
    mut v_ctx_x3f_7734_: *mut leanh::LeanObject,
    mut v_x_7735_: *mut leanh::LeanObject,
    mut v___y_7736_: *mut leanh::LeanObject,
    mut v___y_7737_: *mut leanh::LeanObject,
    mut v___y_7738_: *mut leanh::LeanObject,
    mut v___y_7739_: *mut leanh::LeanObject,
    mut v___y_7740_: *mut leanh::LeanObject,
    mut v___y_7741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_7743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7746_: u8 = 0;
    let mut v_sz_7747_: usize = 0;
    let mut v___x_7748_: usize = 0;
    let mut v___x_7749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7753_: u8 = 0;
    let mut v___x_7755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7760_: u8 = 0;
    let mut v_a_7761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7764_: u8 = 0;
    let mut v___x_7766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7768_: u8 = 0;
    let mut v_isSharedCheck_7769_: u8 = 0;
    let mut v_vs_7770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7773_: u8 = 0;
    let mut v_sz_7774_: usize = 0;
    let mut v___x_7775_: usize = 0;
    let mut v___x_7776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7780_: u8 = 0;
    let mut v___x_7782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7787_: u8 = 0;
    let mut v_a_7788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7791_: u8 = 0;
    let mut v___x_7793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7795_: u8 = 0;
    let mut v_isSharedCheck_7796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7735_) == 0 {
                    v_cs_7743_ = leanh::lean_ctor_get(v_x_7735_, 0);
                    v_isSharedCheck_7769_ = (!leanh::lean_is_exclusive(v_x_7735_)) as u8;
                    if v_isSharedCheck_7769_ == 0 {
                        v___x_7745_ = v_x_7735_;
                        v_isShared_7746_ = v_isSharedCheck_7769_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_7743_);
                        leanh::lean_dec(v_x_7735_);
                        v___x_7745_ = leanh::lean_box(0);
                        v_isShared_7746_ = v_isSharedCheck_7769_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_7770_ = leanh::lean_ctor_get(v_x_7735_, 0);
                    v_isSharedCheck_7796_ = (!leanh::lean_is_exclusive(v_x_7735_)) as u8;
                    if v_isSharedCheck_7796_ == 0 {
                        v___x_7772_ = v_x_7735_;
                        v_isShared_7773_ = v_isSharedCheck_7796_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_7770_);
                        leanh::lean_dec(v_x_7735_);
                        v___x_7772_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v___x_7749_) == 0 {
                    v_a_7750_ = leanh::lean_ctor_get(v___x_7749_, 0);
                    v_isSharedCheck_7760_ = (!leanh::lean_is_exclusive(v___x_7749_)) as u8;
                    if v_isSharedCheck_7760_ == 0 {
                        v___x_7752_ = v___x_7749_;
                        v_isShared_7753_ = v_isSharedCheck_7760_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7750_);
                        leanh::lean_dec(v___x_7749_);
                        v___x_7752_ = leanh::lean_box(0);
                        v_isShared_7753_ = v_isSharedCheck_7760_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7745_);
                    v_a_7761_ = leanh::lean_ctor_get(v___x_7749_, 0);
                    v_isSharedCheck_7768_ = (!leanh::lean_is_exclusive(v___x_7749_)) as u8;
                    if v_isSharedCheck_7768_ == 0 {
                        v___x_7763_ = v___x_7749_;
                        v_isShared_7764_ = v_isSharedCheck_7768_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7761_);
                        leanh::lean_dec(v___x_7749_);
                        v___x_7763_ = leanh::lean_box(0);
                        v_isShared_7764_ = v_isSharedCheck_7768_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7746_ == 0 {
                    leanh::lean_ctor_set(v___x_7745_, 0, v_a_7750_);
                    v___x_7755_ = v___x_7745_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7759_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7759_, 0, v_a_7750_);
                    v___x_7755_ = v_reuseFailAlloc_7759_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7753_ == 0 {
                    leanh::lean_ctor_set(v___x_7752_, 0, v___x_7755_);
                    v___x_7757_ = v___x_7752_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7758_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7758_, 0, v___x_7755_);
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
                    v_reuseFailAlloc_7767_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7767_, 0, v_a_7761_);
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
                if leanh::lean_obj_tag(v___x_7776_) == 0 {
                    v_a_7777_ = leanh::lean_ctor_get(v___x_7776_, 0);
                    v_isSharedCheck_7787_ = (!leanh::lean_is_exclusive(v___x_7776_)) as u8;
                    if v_isSharedCheck_7787_ == 0 {
                        v___x_7779_ = v___x_7776_;
                        v_isShared_7780_ = v_isSharedCheck_7787_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7777_);
                        leanh::lean_dec(v___x_7776_);
                        v___x_7779_ = leanh::lean_box(0);
                        v_isShared_7780_ = v_isSharedCheck_7787_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7772_);
                    v_a_7788_ = leanh::lean_ctor_get(v___x_7776_, 0);
                    v_isSharedCheck_7795_ = (!leanh::lean_is_exclusive(v___x_7776_)) as u8;
                    if v_isSharedCheck_7795_ == 0 {
                        v___x_7790_ = v___x_7776_;
                        v_isShared_7791_ = v_isSharedCheck_7795_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7788_);
                        leanh::lean_dec(v___x_7776_);
                        v___x_7790_ = leanh::lean_box(0);
                        v_isShared_7791_ = v_isSharedCheck_7795_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_7773_ == 0 {
                    leanh::lean_ctor_set(v___x_7772_, 0, v_a_7777_);
                    v___x_7782_ = v___x_7772_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7786_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7786_, 0, v_a_7777_);
                    v___x_7782_ = v_reuseFailAlloc_7786_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_7780_ == 0 {
                    leanh::lean_ctor_set(v___x_7779_, 0, v___x_7782_);
                    v___x_7784_ = v___x_7779_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7785_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7785_, 0, v___x_7782_);
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
                    v_reuseFailAlloc_7794_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7794_, 0, v_a_7788_);
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
    mut v___x_7797_: *mut leanh::LeanObject,
    mut v_ctx_x3f_7798_: *mut leanh::LeanObject,
    mut v_sz_7799_: usize,
    mut v_i_7800_: usize,
    mut v_bs_7801_: *mut leanh::LeanObject,
    mut v___y_7802_: *mut leanh::LeanObject,
    mut v___y_7803_: *mut leanh::LeanObject,
    mut v___y_7804_: *mut leanh::LeanObject,
    mut v___y_7805_: *mut leanh::LeanObject,
    mut v___y_7806_: *mut leanh::LeanObject,
    mut v___y_7807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7809_: u8 = 0;
    let mut v___x_7810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7816_: usize = 0;
    let mut v___x_7817_: usize = 0;
    let mut v___x_7818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7823_: u8 = 0;
    let mut v___x_7825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7809_ = lean_usize_dec_lt(v_i_7800_, v_sz_7799_);
                if v___x_7809_ == 0 {
                    leanh::lean_dec_ref(v_ctx_x3f_7798_);
                    v___x_7810_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7810_, 0, v_bs_7801_);
                    return v___x_7810_;
                } else {
                    v_v_7811_ = lean_array_uget_borrowed(v_bs_7801_, v_i_7800_);
                    leanh::lean_inc(v_v_7811_);
                    leanh::lean_inc_ref(v_ctx_x3f_7798_);
                    v___x_7812_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_7797_, v_ctx_x3f_7798_, v_v_7811_, v___y_7802_, v___y_7803_, v___y_7804_, v___y_7805_, v___y_7806_, v___y_7807_);
                    if leanh::lean_obj_tag(v___x_7812_) == 0 {
                        v_a_7813_ = leanh::lean_ctor_get(v___x_7812_, 0);
                        leanh::lean_inc(v_a_7813_);
                        leanh::lean_dec_ref_known(v___x_7812_, 1);
                        v___x_7814_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_7815_ = lean_array_uset(v_bs_7801_, v_i_7800_, v___x_7814_);
                        v___x_7816_ = 1usize;
                        v___x_7817_ = lean_usize_add(v_i_7800_, v___x_7816_);
                        v___x_7818_ = lean_array_uset(v_bs_x27_7815_, v_i_7800_, v_a_7813_);
                        v_i_7800_ = v___x_7817_;
                        v_bs_7801_ = v___x_7818_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_7801_);
                        leanh::lean_dec_ref(v_ctx_x3f_7798_);
                        v_a_7820_ = leanh::lean_ctor_get(v___x_7812_, 0);
                        v_isSharedCheck_7827_ =
                            (!leanh::lean_is_exclusive(v___x_7812_)) as u8;
                        if v_isSharedCheck_7827_ == 0 {
                            v___x_7822_ = v___x_7812_;
                            v_isShared_7823_ = v_isSharedCheck_7827_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7820_);
                            leanh::lean_dec(v___x_7812_);
                            v___x_7822_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_7826_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7826_, 0, v_a_7820_);
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
    mut v___x_7828_: *mut leanh::LeanObject,
    mut v_ctx_x3f_7829_: *mut leanh::LeanObject,
    mut v_sz_7830_: *mut leanh::LeanObject,
    mut v_i_7831_: *mut leanh::LeanObject,
    mut v_bs_7832_: *mut leanh::LeanObject,
    mut v___y_7833_: *mut leanh::LeanObject,
    mut v___y_7834_: *mut leanh::LeanObject,
    mut v___y_7835_: *mut leanh::LeanObject,
    mut v___y_7836_: *mut leanh::LeanObject,
    mut v___y_7837_: *mut leanh::LeanObject,
    mut v___y_7838_: *mut leanh::LeanObject,
    mut v___y_7839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7840_: usize = 0;
    let mut v_i_boxed_7841_: usize = 0;
    let mut v_res_7842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7840_ = leanh::lean_unbox_usize(v_sz_7830_);
    leanh::lean_dec(v_sz_7830_);
    v_i_boxed_7841_ = leanh::lean_unbox_usize(v_i_7831_);
    leanh::lean_dec(v_i_7831_);
    v_res_7842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_7828_, v_ctx_x3f_7829_, v_sz_boxed_7840_, v_i_boxed_7841_, v_bs_7832_, v___y_7833_, v___y_7834_, v___y_7835_, v___y_7836_, v___y_7837_, v___y_7838_);
    leanh::lean_dec(v___y_7838_);
    leanh::lean_dec_ref(v___y_7837_);
    leanh::lean_dec(v___y_7836_);
    leanh::lean_dec_ref(v___y_7835_);
    leanh::lean_dec(v___y_7834_);
    leanh::lean_dec_ref(v___y_7833_);
    leanh::lean_dec_ref(v___x_7828_);
    return v_res_7842_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5___boxed(
    mut v___x_7843_: *mut leanh::LeanObject,
    mut v_ctx_x3f_7844_: *mut leanh::LeanObject,
    mut v_x_7845_: *mut leanh::LeanObject,
    mut v___y_7846_: *mut leanh::LeanObject,
    mut v___y_7847_: *mut leanh::LeanObject,
    mut v___y_7848_: *mut leanh::LeanObject,
    mut v___y_7849_: *mut leanh::LeanObject,
    mut v___y_7850_: *mut leanh::LeanObject,
    mut v___y_7851_: *mut leanh::LeanObject,
    mut v___y_7852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7853_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_7843_, v_ctx_x3f_7844_, v_x_7845_, v___y_7846_, v___y_7847_, v___y_7848_, v___y_7849_, v___y_7850_, v___y_7851_);
    leanh::lean_dec(v___y_7851_);
    leanh::lean_dec_ref(v___y_7850_);
    leanh::lean_dec(v___y_7849_);
    leanh::lean_dec_ref(v___y_7848_);
    leanh::lean_dec(v___y_7847_);
    leanh::lean_dec_ref(v___y_7846_);
    leanh::lean_dec_ref(v___x_7843_);
    return v_res_7853_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(
    mut v___x_7854_: *mut leanh::LeanObject,
    mut v_ctx_x3f_7855_: *mut leanh::LeanObject,
    mut v_t_7856_: *mut leanh::LeanObject,
    mut v___y_7857_: *mut leanh::LeanObject,
    mut v___y_7858_: *mut leanh::LeanObject,
    mut v___y_7859_: *mut leanh::LeanObject,
    mut v___y_7860_: *mut leanh::LeanObject,
    mut v___y_7861_: *mut leanh::LeanObject,
    mut v___y_7862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_7864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_7867_: usize = 0;
    let mut v_tailOff_7868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7871_: u8 = 0;
    let mut v___x_7872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7874_: usize = 0;
    let mut v___x_7875_: usize = 0;
    let mut v___x_7876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7880_: u8 = 0;
    let mut v___x_7882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7887_: u8 = 0;
    let mut v_a_7888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7891_: u8 = 0;
    let mut v___x_7893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7895_: u8 = 0;
    let mut v_a_7896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7899_: u8 = 0;
    let mut v___x_7901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7903_: u8 = 0;
    let mut v_isSharedCheck_7904_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_7864_ = leanh::lean_ctor_get(v_t_7856_, 0);
                v_tail_7865_ = leanh::lean_ctor_get(v_t_7856_, 1);
                v_size_7866_ = leanh::lean_ctor_get(v_t_7856_, 2);
                v_shift_7867_ = leanh::lean_ctor_get_usize(v_t_7856_, 4);
                v_tailOff_7868_ = leanh::lean_ctor_get(v_t_7856_, 3);
                v_isSharedCheck_7904_ = (!leanh::lean_is_exclusive(v_t_7856_)) as u8;
                if v_isSharedCheck_7904_ == 0 {
                    v___x_7870_ = v_t_7856_;
                    v_isShared_7871_ = v_isSharedCheck_7904_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_7868_);
                    leanh::lean_inc(v_size_7866_);
                    leanh::lean_inc(v_tail_7865_);
                    leanh::lean_inc(v_root_7864_);
                    leanh::lean_dec(v_t_7856_);
                    v___x_7870_ = leanh::lean_box(0);
                    v_isShared_7871_ = v_isSharedCheck_7904_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_ctx_x3f_7855_);
                v___x_7872_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_7854_, v_ctx_x3f_7855_, v_root_7864_, v___y_7857_, v___y_7858_, v___y_7859_, v___y_7860_, v___y_7861_, v___y_7862_);
                if leanh::lean_obj_tag(v___x_7872_) == 0 {
                    v_a_7873_ = leanh::lean_ctor_get(v___x_7872_, 0);
                    leanh::lean_inc(v_a_7873_);
                    leanh::lean_dec_ref_known(v___x_7872_, 1);
                    v_sz_7874_ = lean_array_size(v_tail_7865_);
                    v___x_7875_ = 0usize;
                    v___x_7876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_7854_, v_ctx_x3f_7855_, v_sz_7874_, v___x_7875_, v_tail_7865_, v___y_7857_, v___y_7858_, v___y_7859_, v___y_7860_, v___y_7861_, v___y_7862_);
                    if leanh::lean_obj_tag(v___x_7876_) == 0 {
                        v_a_7877_ = leanh::lean_ctor_get(v___x_7876_, 0);
                        v_isSharedCheck_7887_ =
                            (!leanh::lean_is_exclusive(v___x_7876_)) as u8;
                        if v_isSharedCheck_7887_ == 0 {
                            v___x_7879_ = v___x_7876_;
                            v_isShared_7880_ = v_isSharedCheck_7887_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7877_);
                            leanh::lean_dec(v___x_7876_);
                            v___x_7879_ = leanh::lean_box(0);
                            v_isShared_7880_ = v_isSharedCheck_7887_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_7873_);
                        leanh::lean_del_object(v___x_7870_);
                        leanh::lean_dec(v_tailOff_7868_);
                        leanh::lean_dec(v_size_7866_);
                        v_a_7888_ = leanh::lean_ctor_get(v___x_7876_, 0);
                        v_isSharedCheck_7895_ =
                            (!leanh::lean_is_exclusive(v___x_7876_)) as u8;
                        if v_isSharedCheck_7895_ == 0 {
                            v___x_7890_ = v___x_7876_;
                            v_isShared_7891_ = v_isSharedCheck_7895_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7888_);
                            leanh::lean_dec(v___x_7876_);
                            v___x_7890_ = leanh::lean_box(0);
                            v_isShared_7891_ = v_isSharedCheck_7895_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7870_);
                    leanh::lean_dec(v_tailOff_7868_);
                    leanh::lean_dec(v_size_7866_);
                    leanh::lean_dec_ref(v_tail_7865_);
                    leanh::lean_dec_ref(v_ctx_x3f_7855_);
                    v_a_7896_ = leanh::lean_ctor_get(v___x_7872_, 0);
                    v_isSharedCheck_7903_ = (!leanh::lean_is_exclusive(v___x_7872_)) as u8;
                    if v_isSharedCheck_7903_ == 0 {
                        v___x_7898_ = v___x_7872_;
                        v_isShared_7899_ = v_isSharedCheck_7903_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7896_);
                        leanh::lean_dec(v___x_7872_);
                        v___x_7898_ = leanh::lean_box(0);
                        v_isShared_7899_ = v_isSharedCheck_7903_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7871_ == 0 {
                    leanh::lean_ctor_set(v___x_7870_, 1, v_a_7877_);
                    leanh::lean_ctor_set(v___x_7870_, 0, v_a_7873_);
                    v___x_7882_ = v___x_7870_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7886_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_7886_, 0, v_a_7873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7886_, 1, v_a_7877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7886_, 2, v_size_7866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7886_, 3, v_tailOff_7868_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_7886_, 4, v_shift_7867_);
                    v___x_7882_ = v_reuseFailAlloc_7886_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7880_ == 0 {
                    leanh::lean_ctor_set(v___x_7879_, 0, v___x_7882_);
                    v___x_7884_ = v___x_7879_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7885_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7885_, 0, v___x_7882_);
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
                    v_reuseFailAlloc_7894_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7894_, 0, v_a_7888_);
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
                    v_reuseFailAlloc_7902_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7902_, 0, v_a_7896_);
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
    mut v___x_7905_: *mut leanh::LeanObject,
    mut v_ctx_x3f_7906_: *mut leanh::LeanObject,
    mut v_t_7907_: *mut leanh::LeanObject,
    mut v___y_7908_: *mut leanh::LeanObject,
    mut v___y_7909_: *mut leanh::LeanObject,
    mut v___y_7910_: *mut leanh::LeanObject,
    mut v___y_7911_: *mut leanh::LeanObject,
    mut v___y_7912_: *mut leanh::LeanObject,
    mut v___y_7913_: *mut leanh::LeanObject,
    mut v___y_7914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7915_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v___x_7905_, v_ctx_x3f_7906_, v_t_7907_, v___y_7908_, v___y_7909_, v___y_7910_, v___y_7911_, v___y_7912_, v___y_7913_);
    leanh::lean_dec(v___y_7913_);
    leanh::lean_dec_ref(v___y_7912_);
    leanh::lean_dec(v___y_7911_);
    leanh::lean_dec_ref(v___y_7910_);
    leanh::lean_dec(v___y_7909_);
    leanh::lean_dec_ref(v___y_7908_);
    leanh::lean_dec_ref(v___x_7905_);
    return v_res_7915_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(
    mut v___y_7916_: *mut leanh::LeanObject,
    mut v_ctx_x3f_7917_: *mut leanh::LeanObject,
    mut v___y_7918_: *mut leanh::LeanObject,
    mut v___y_7919_: *mut leanh::LeanObject,
    mut v___y_7920_: *mut leanh::LeanObject,
    mut v___y_7921_: *mut leanh::LeanObject,
    mut v___y_7922_: *mut leanh::LeanObject,
    mut v_a_7923_: *mut leanh::LeanObject,
    mut v_a_x3f_7924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_7928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7933_: u8 = 0;
    let mut v___x_7934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7946_: u8 = 0;
    let mut v_enabled_7947_: u8 = 0;
    let mut v_assignment_7948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_7949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7952_: u8 = 0;
    let mut v___x_7953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7965_: u8 = 0;
    let mut v_unused_7966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7967_: u8 = 0;
    let mut v_isSharedCheck_7968_: u8 = 0;
    let mut v_a_7969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7972_: u8 = 0;
    let mut v___x_7974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7926_ = lean_st_ref_get(v___y_7916_);
                v_infoState_7927_ = leanh::lean_ctor_get(v___x_7926_, 7);
                leanh::lean_inc_ref(v_infoState_7927_);
                leanh::lean_dec(v___x_7926_);
                v_trees_7928_ = leanh::lean_ctor_get(v_infoState_7927_, 2);
                leanh::lean_inc_ref(v_trees_7928_);
                v___x_7929_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v_infoState_7927_, v_ctx_x3f_7917_, v_trees_7928_, v___y_7918_, v___y_7919_, v___y_7920_, v___y_7921_, v___y_7922_, v___y_7916_);
                leanh::lean_dec_ref(v_infoState_7927_);
                if leanh::lean_obj_tag(v___x_7929_) == 0 {
                    v_a_7930_ = leanh::lean_ctor_get(v___x_7929_, 0);
                    v_isSharedCheck_7968_ = (!leanh::lean_is_exclusive(v___x_7929_)) as u8;
                    if v_isSharedCheck_7968_ == 0 {
                        v___x_7932_ = v___x_7929_;
                        v_isShared_7933_ = v_isSharedCheck_7968_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7930_);
                        leanh::lean_dec(v___x_7929_);
                        v___x_7932_ = leanh::lean_box(0);
                        v_isShared_7933_ = v_isSharedCheck_7968_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_7923_);
                    v_a_7969_ = leanh::lean_ctor_get(v___x_7929_, 0);
                    v_isSharedCheck_7976_ = (!leanh::lean_is_exclusive(v___x_7929_)) as u8;
                    if v_isSharedCheck_7976_ == 0 {
                        v___x_7971_ = v___x_7929_;
                        v_isShared_7972_ = v_isSharedCheck_7976_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7969_);
                        leanh::lean_dec(v___x_7929_);
                        v___x_7971_ = leanh::lean_box(0);
                        v_isShared_7972_ = v_isSharedCheck_7976_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7934_ = lean_st_ref_take(v___y_7916_);
                v_infoState_7935_ = leanh::lean_ctor_get(v___x_7934_, 7);
                v_env_7936_ = leanh::lean_ctor_get(v___x_7934_, 0);
                v_nextMacroScope_7937_ = leanh::lean_ctor_get(v___x_7934_, 1);
                v_ngen_7938_ = leanh::lean_ctor_get(v___x_7934_, 2);
                v_auxDeclNGen_7939_ = leanh::lean_ctor_get(v___x_7934_, 3);
                v_traceState_7940_ = leanh::lean_ctor_get(v___x_7934_, 4);
                v_cache_7941_ = leanh::lean_ctor_get(v___x_7934_, 5);
                v_messages_7942_ = leanh::lean_ctor_get(v___x_7934_, 6);
                v_snapshotTasks_7943_ = leanh::lean_ctor_get(v___x_7934_, 8);
                v_isSharedCheck_7967_ = (!leanh::lean_is_exclusive(v___x_7934_)) as u8;
                if v_isSharedCheck_7967_ == 0 {
                    v___x_7945_ = v___x_7934_;
                    v_isShared_7946_ = v_isSharedCheck_7967_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_7943_);
                    leanh::lean_inc(v_infoState_7935_);
                    leanh::lean_inc(v_messages_7942_);
                    leanh::lean_inc(v_cache_7941_);
                    leanh::lean_inc(v_traceState_7940_);
                    leanh::lean_inc(v_auxDeclNGen_7939_);
                    leanh::lean_inc(v_ngen_7938_);
                    leanh::lean_inc(v_nextMacroScope_7937_);
                    leanh::lean_inc(v_env_7936_);
                    leanh::lean_dec(v___x_7934_);
                    v___x_7945_ = leanh::lean_box(0);
                    v_isShared_7946_ = v_isSharedCheck_7967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_7947_ = leanh::lean_ctor_get_uint8(
                    v_infoState_7935_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_7948_ = leanh::lean_ctor_get(v_infoState_7935_, 0);
                v_lazyAssignment_7949_ = leanh::lean_ctor_get(v_infoState_7935_, 1);
                v_isSharedCheck_7965_ = (!leanh::lean_is_exclusive(v_infoState_7935_)) as u8;
                if v_isSharedCheck_7965_ == 0 {
                    v_unused_7966_ = leanh::lean_ctor_get(v_infoState_7935_, 2);
                    leanh::lean_dec(v_unused_7966_);
                    v___x_7951_ = v_infoState_7935_;
                    v_isShared_7952_ = v_isSharedCheck_7965_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_lazyAssignment_7949_);
                    leanh::lean_inc(v_assignment_7948_);
                    leanh::lean_dec(v_infoState_7935_);
                    v___x_7951_ = leanh::lean_box(0);
                    v_isShared_7952_ = v_isSharedCheck_7965_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7953_ = l_Lean_PersistentArray_append___redArg(v_a_7923_, v_a_7930_);
                leanh::lean_dec(v_a_7930_);
                if v_isShared_7952_ == 0 {
                    leanh::lean_ctor_set(v___x_7951_, 2, v___x_7953_);
                    v___x_7955_ = v___x_7951_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7964_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7964_, 0, v_assignment_7948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7964_, 1, v_lazyAssignment_7949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7964_, 2, v___x_7953_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7964_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_7947_,
                    );
                    v___x_7955_ = v_reuseFailAlloc_7964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7946_ == 0 {
                    leanh::lean_ctor_set(v___x_7945_, 7, v___x_7955_);
                    v___x_7957_ = v___x_7945_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7963_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 0, v_env_7936_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 1, v_nextMacroScope_7937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 2, v_ngen_7938_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 3, v_auxDeclNGen_7939_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 4, v_traceState_7940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 5, v_cache_7941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 6, v_messages_7942_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 7, v___x_7955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 8, v_snapshotTasks_7943_);
                    v___x_7957_ = v_reuseFailAlloc_7963_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7958_ = lean_st_ref_set(v___y_7916_, v___x_7957_);
                v___x_7959_ = leanh::lean_box(0);
                if v_isShared_7933_ == 0 {
                    leanh::lean_ctor_set(v___x_7932_, 0, v___x_7959_);
                    v___x_7961_ = v___x_7932_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7962_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7962_, 0, v___x_7959_);
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
                    v_reuseFailAlloc_7975_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7975_, 0, v_a_7969_);
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
    mut v___y_7977_: *mut leanh::LeanObject,
    mut v_ctx_x3f_7978_: *mut leanh::LeanObject,
    mut v___y_7979_: *mut leanh::LeanObject,
    mut v___y_7980_: *mut leanh::LeanObject,
    mut v___y_7981_: *mut leanh::LeanObject,
    mut v___y_7982_: *mut leanh::LeanObject,
    mut v___y_7983_: *mut leanh::LeanObject,
    mut v_a_7984_: *mut leanh::LeanObject,
    mut v_a_x3f_7985_: *mut leanh::LeanObject,
    mut v___y_7986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7987_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_7977_, v_ctx_x3f_7978_, v___y_7979_, v___y_7980_, v___y_7981_, v___y_7982_, v___y_7983_, v_a_7984_, v_a_x3f_7985_);
    leanh::lean_dec(v_a_x3f_7985_);
    leanh::lean_dec_ref(v___y_7983_);
    leanh::lean_dec(v___y_7982_);
    leanh::lean_dec_ref(v___y_7981_);
    leanh::lean_dec(v___y_7980_);
    leanh::lean_dec_ref(v___y_7979_);
    leanh::lean_dec(v___y_7977_);
    return v_res_7987_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(
    mut v___y_7988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_7992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_8001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_8002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8005_: u8 = 0;
    let mut v_enabled_8006_: u8 = 0;
    let mut v_assignment_8007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_8008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8011_: u8 = 0;
    let mut v___x_8012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8023_: u8 = 0;
    let mut v_unused_8024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7990_ = lean_st_ref_get(v___y_7988_);
                v_infoState_7991_ = leanh::lean_ctor_get(v___x_7990_, 7);
                leanh::lean_inc_ref(v_infoState_7991_);
                leanh::lean_dec(v___x_7990_);
                v_trees_7992_ = leanh::lean_ctor_get(v_infoState_7991_, 2);
                leanh::lean_inc_ref(v_trees_7992_);
                leanh::lean_dec_ref(v_infoState_7991_);
                v___x_7993_ = lean_st_ref_take(v___y_7988_);
                v_infoState_7994_ = leanh::lean_ctor_get(v___x_7993_, 7);
                v_env_7995_ = leanh::lean_ctor_get(v___x_7993_, 0);
                v_nextMacroScope_7996_ = leanh::lean_ctor_get(v___x_7993_, 1);
                v_ngen_7997_ = leanh::lean_ctor_get(v___x_7993_, 2);
                v_auxDeclNGen_7998_ = leanh::lean_ctor_get(v___x_7993_, 3);
                v_traceState_7999_ = leanh::lean_ctor_get(v___x_7993_, 4);
                v_cache_8000_ = leanh::lean_ctor_get(v___x_7993_, 5);
                v_messages_8001_ = leanh::lean_ctor_get(v___x_7993_, 6);
                v_snapshotTasks_8002_ = leanh::lean_ctor_get(v___x_7993_, 8);
                v_isSharedCheck_8025_ = (!leanh::lean_is_exclusive(v___x_7993_)) as u8;
                if v_isSharedCheck_8025_ == 0 {
                    v___x_8004_ = v___x_7993_;
                    v_isShared_8005_ = v_isSharedCheck_8025_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_8002_);
                    leanh::lean_inc(v_infoState_7994_);
                    leanh::lean_inc(v_messages_8001_);
                    leanh::lean_inc(v_cache_8000_);
                    leanh::lean_inc(v_traceState_7999_);
                    leanh::lean_inc(v_auxDeclNGen_7998_);
                    leanh::lean_inc(v_ngen_7997_);
                    leanh::lean_inc(v_nextMacroScope_7996_);
                    leanh::lean_inc(v_env_7995_);
                    leanh::lean_dec(v___x_7993_);
                    v___x_8004_ = leanh::lean_box(0);
                    v_isShared_8005_ = v_isSharedCheck_8025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_8006_ = leanh::lean_ctor_get_uint8(
                    v_infoState_7994_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_8007_ = leanh::lean_ctor_get(v_infoState_7994_, 0);
                v_lazyAssignment_8008_ = leanh::lean_ctor_get(v_infoState_7994_, 1);
                v_isSharedCheck_8023_ = (!leanh::lean_is_exclusive(v_infoState_7994_)) as u8;
                if v_isSharedCheck_8023_ == 0 {
                    v_unused_8024_ = leanh::lean_ctor_get(v_infoState_7994_, 2);
                    leanh::lean_dec(v_unused_8024_);
                    v___x_8010_ = v_infoState_7994_;
                    v_isShared_8011_ = v_isSharedCheck_8023_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lazyAssignment_8008_);
                    leanh::lean_inc(v_assignment_8007_);
                    leanh::lean_dec(v_infoState_7994_);
                    v___x_8010_ = leanh::lean_box(0);
                    v_isShared_8011_ = v_isSharedCheck_8023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8012_ = leanh::lean_unsigned_to_nat(32);
                v___x_8013_ = lean_mk_empty_array_with_capacity(v___x_8012_);
                leanh::lean_dec_ref(v___x_8013_);
                v___x_8014_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
                if v_isShared_8011_ == 0 {
                    leanh::lean_ctor_set(v___x_8010_, 2, v___x_8014_);
                    v___x_8016_ = v___x_8010_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8022_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8022_, 0, v_assignment_8007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8022_, 1, v_lazyAssignment_8008_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8022_, 2, v___x_8014_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8022_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_8006_,
                    );
                    v___x_8016_ = v_reuseFailAlloc_8022_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8005_ == 0 {
                    leanh::lean_ctor_set(v___x_8004_, 7, v___x_8016_);
                    v___x_8018_ = v___x_8004_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8021_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 0, v_env_7995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 1, v_nextMacroScope_7996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 2, v_ngen_7997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 3, v_auxDeclNGen_7998_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 4, v_traceState_7999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 5, v_cache_8000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 6, v_messages_8001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 7, v___x_8016_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 8, v_snapshotTasks_8002_);
                    v___x_8018_ = v_reuseFailAlloc_8021_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8019_ = lean_st_ref_set(v___y_7988_, v___x_8018_);
                v___x_8020_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8020_, 0, v_trees_7992_);
                return v___x_8020_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg___boxed(
    mut v___y_8026_: *mut leanh::LeanObject,
    mut v___y_8027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8028_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_8026_);
    leanh::lean_dec(v___y_8026_);
    return v_res_8028_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(
    mut v_x_8029_: *mut leanh::LeanObject,
    mut v_ctx_x3f_8030_: *mut leanh::LeanObject,
    mut v___y_8031_: *mut leanh::LeanObject,
    mut v___y_8032_: *mut leanh::LeanObject,
    mut v___y_8033_: *mut leanh::LeanObject,
    mut v___y_8034_: *mut leanh::LeanObject,
    mut v___y_8035_: *mut leanh::LeanObject,
    mut v___y_8036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_8039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_8040_: u8 = 0;
    let mut v___x_8041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8048_: u8 = 0;
    let mut v___x_8050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8054_: u8 = 0;
    let mut v___x_8056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8058_: u8 = 0;
    let mut v_unused_8059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8063_: u8 = 0;
    let mut v___x_8065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8067_: u8 = 0;
    let mut v_reuseFailAlloc_8068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8069_: u8 = 0;
    let mut v_a_8070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8075_: u8 = 0;
    let mut v___x_8077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8079_: u8 = 0;
    let mut v_unused_8080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8084_: u8 = 0;
    let mut v___x_8086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8038_ = lean_st_ref_get(v___y_8036_);
                v_infoState_8039_ = leanh::lean_ctor_get(v___x_8038_, 7);
                leanh::lean_inc_ref(v_infoState_8039_);
                leanh::lean_dec(v___x_8038_);
                v_enabled_8040_ = leanh::lean_ctor_get_uint8(
                    v_infoState_8039_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_8039_);
                if v_enabled_8040_ == 0 {
                    leanh::lean_dec_ref(v_ctx_x3f_8030_);
                    leanh::lean_inc(v___y_8036_);
                    leanh::lean_inc_ref(v___y_8035_);
                    leanh::lean_inc(v___y_8034_);
                    leanh::lean_inc_ref(v___y_8033_);
                    leanh::lean_inc(v___y_8032_);
                    leanh::lean_inc_ref(v___y_8031_);
                    v___x_8041_ = leanh::lean_apply_7(
                        v_x_8029_,
                        v___y_8031_,
                        v___y_8032_,
                        v___y_8033_,
                        v___y_8034_,
                        v___y_8035_,
                        v___y_8036_,
                        leanh::lean_box(0),
                    );
                    return v___x_8041_;
                } else {
                    v___x_8042_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_8036_);
                    v_a_8043_ = leanh::lean_ctor_get(v___x_8042_, 0);
                    leanh::lean_inc(v_a_8043_);
                    leanh::lean_dec_ref(v___x_8042_);
                    leanh::lean_inc(v___y_8036_);
                    leanh::lean_inc_ref(v___y_8035_);
                    leanh::lean_inc(v___y_8034_);
                    leanh::lean_inc_ref(v___y_8033_);
                    leanh::lean_inc(v___y_8032_);
                    leanh::lean_inc_ref(v___y_8031_);
                    v_r_8044_ = leanh::lean_apply_7(
                        v_x_8029_,
                        v___y_8031_,
                        v___y_8032_,
                        v___y_8033_,
                        v___y_8034_,
                        v___y_8035_,
                        v___y_8036_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v_r_8044_) == 0 {
                        v_a_8045_ = leanh::lean_ctor_get(v_r_8044_, 0);
                        v_isSharedCheck_8069_ = (!leanh::lean_is_exclusive(v_r_8044_)) as u8;
                        if v_isSharedCheck_8069_ == 0 {
                            v___x_8047_ = v_r_8044_;
                            v_isShared_8048_ = v_isSharedCheck_8069_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8045_);
                            leanh::lean_dec(v_r_8044_);
                            v___x_8047_ = leanh::lean_box(0);
                            v_isShared_8048_ = v_isSharedCheck_8069_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_8070_ = leanh::lean_ctor_get(v_r_8044_, 0);
                        leanh::lean_inc(v_a_8070_);
                        leanh::lean_dec_ref_known(v_r_8044_, 1);
                        v___x_8071_ = leanh::lean_box(0);
                        v___x_8072_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_8036_, v_ctx_x3f_8030_, v___y_8031_, v___y_8032_, v___y_8033_, v___y_8034_, v___y_8035_, v_a_8043_, v___x_8071_);
                        if leanh::lean_obj_tag(v___x_8072_) == 0 {
                            v_isSharedCheck_8079_ =
                                (!leanh::lean_is_exclusive(v___x_8072_)) as u8;
                            if v_isSharedCheck_8079_ == 0 {
                                v_unused_8080_ = leanh::lean_ctor_get(v___x_8072_, 0);
                                leanh::lean_dec(v_unused_8080_);
                                v___x_8074_ = v___x_8072_;
                                v_isShared_8075_ = v_isSharedCheck_8079_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_8072_);
                                v___x_8074_ = leanh::lean_box(0);
                                v_isShared_8075_ = v_isSharedCheck_8079_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_8070_);
                            v_a_8081_ = leanh::lean_ctor_get(v___x_8072_, 0);
                            v_isSharedCheck_8088_ =
                                (!leanh::lean_is_exclusive(v___x_8072_)) as u8;
                            if v_isSharedCheck_8088_ == 0 {
                                v___x_8083_ = v___x_8072_;
                                v_isShared_8084_ = v_isSharedCheck_8088_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8081_);
                                leanh::lean_dec(v___x_8072_);
                                v___x_8083_ = leanh::lean_box(0);
                                v_isShared_8084_ = v_isSharedCheck_8088_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_8045_);
                if v_isShared_8048_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_8047_, 1);
                    v___x_8050_ = v___x_8047_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8068_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8068_, 0, v_a_8045_);
                    v___x_8050_ = v_reuseFailAlloc_8068_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8051_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_8036_, v_ctx_x3f_8030_, v___y_8031_, v___y_8032_, v___y_8033_, v___y_8034_, v___y_8035_, v_a_8043_, v___x_8050_);
                leanh::lean_dec_ref(v___x_8050_);
                if leanh::lean_obj_tag(v___x_8051_) == 0 {
                    v_isSharedCheck_8058_ = (!leanh::lean_is_exclusive(v___x_8051_)) as u8;
                    if v_isSharedCheck_8058_ == 0 {
                        v_unused_8059_ = leanh::lean_ctor_get(v___x_8051_, 0);
                        leanh::lean_dec(v_unused_8059_);
                        v___x_8053_ = v___x_8051_;
                        v_isShared_8054_ = v_isSharedCheck_8058_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_8051_);
                        v___x_8053_ = leanh::lean_box(0);
                        v_isShared_8054_ = v_isSharedCheck_8058_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_8045_);
                    v_a_8060_ = leanh::lean_ctor_get(v___x_8051_, 0);
                    v_isSharedCheck_8067_ = (!leanh::lean_is_exclusive(v___x_8051_)) as u8;
                    if v_isSharedCheck_8067_ == 0 {
                        v___x_8062_ = v___x_8051_;
                        v_isShared_8063_ = v_isSharedCheck_8067_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8060_);
                        leanh::lean_dec(v___x_8051_);
                        v___x_8062_ = leanh::lean_box(0);
                        v_isShared_8063_ = v_isSharedCheck_8067_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_8054_ == 0 {
                    leanh::lean_ctor_set(v___x_8053_, 0, v_a_8045_);
                    v___x_8056_ = v___x_8053_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8057_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8057_, 0, v_a_8045_);
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
                    v_reuseFailAlloc_8066_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8066_, 0, v_a_8060_);
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
                    leanh::lean_ctor_set_tag(v___x_8074_, 1);
                    leanh::lean_ctor_set(v___x_8074_, 0, v_a_8070_);
                    v___x_8077_ = v___x_8074_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8078_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8078_, 0, v_a_8070_);
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
                    v_reuseFailAlloc_8087_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8087_, 0, v_a_8081_);
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
    mut v_x_8089_: *mut leanh::LeanObject,
    mut v_ctx_x3f_8090_: *mut leanh::LeanObject,
    mut v___y_8091_: *mut leanh::LeanObject,
    mut v___y_8092_: *mut leanh::LeanObject,
    mut v___y_8093_: *mut leanh::LeanObject,
    mut v___y_8094_: *mut leanh::LeanObject,
    mut v___y_8095_: *mut leanh::LeanObject,
    mut v___y_8096_: *mut leanh::LeanObject,
    mut v___y_8097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8098_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_8089_, v_ctx_x3f_8090_, v___y_8091_, v___y_8092_, v___y_8093_, v___y_8094_, v___y_8095_, v___y_8096_);
    leanh::lean_dec(v___y_8096_);
    leanh::lean_dec_ref(v___y_8095_);
    leanh::lean_dec(v___y_8094_);
    leanh::lean_dec_ref(v___y_8093_);
    leanh::lean_dec(v___y_8092_);
    leanh::lean_dec_ref(v___y_8091_);
    return v_res_8098_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(
    mut v___y_8099_: *mut leanh::LeanObject,
    mut v___y_8100_: *mut leanh::LeanObject,
    mut v___y_8101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_8104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_8106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_8107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_8108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_8109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_8111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8103_ = lean_st_ref_get(v___y_8101_);
    v_env_8104_ = leanh::lean_ctor_get(v___x_8103_, 0);
    leanh::lean_inc_ref(v_env_8104_);
    leanh::lean_dec(v___x_8103_);
    v___x_8105_ = lean_st_ref_get(v___y_8099_);
    v_mctx_8106_ = leanh::lean_ctor_get(v___x_8105_, 0);
    leanh::lean_inc_ref(v_mctx_8106_);
    leanh::lean_dec(v___x_8105_);
    v_options_8107_ = leanh::lean_ctor_get(v___y_8100_, 2);
    v_currNamespace_8108_ = leanh::lean_ctor_get(v___y_8100_, 6);
    v_openDecls_8109_ = leanh::lean_ctor_get(v___y_8100_, 7);
    v___x_8110_ = lean_st_ref_get(v___y_8101_);
    v_ngen_8111_ = leanh::lean_ctor_get(v___x_8110_, 2);
    leanh::lean_inc_ref(v_ngen_8111_);
    leanh::lean_dec(v___x_8110_);
    v___x_8112_ = leanh::lean_box(0);
    v___x_8113_ = l_Lean_instInhabitedFileMap_default;
    leanh::lean_inc(v_openDecls_8109_);
    leanh::lean_inc(v_currNamespace_8108_);
    leanh::lean_inc_ref(v_options_8107_);
    v___x_8114_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v___x_8114_, 0, v_env_8104_);
    leanh::lean_ctor_set(v___x_8114_, 1, v___x_8112_);
    leanh::lean_ctor_set(v___x_8114_, 2, v___x_8113_);
    leanh::lean_ctor_set(v___x_8114_, 3, v_mctx_8106_);
    leanh::lean_ctor_set(v___x_8114_, 4, v_options_8107_);
    leanh::lean_ctor_set(v___x_8114_, 5, v_currNamespace_8108_);
    leanh::lean_ctor_set(v___x_8114_, 6, v_openDecls_8109_);
    leanh::lean_ctor_set(v___x_8114_, 7, v_ngen_8111_);
    v___x_8115_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_8115_, 0, v___x_8114_);
    return v___x_8115_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg___boxed(
    mut v___y_8116_: *mut leanh::LeanObject,
    mut v___y_8117_: *mut leanh::LeanObject,
    mut v___y_8118_: *mut leanh::LeanObject,
    mut v___y_8119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8120_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_8116_, v___y_8117_, v___y_8118_);
    leanh::lean_dec(v___y_8118_);
    leanh::lean_dec_ref(v___y_8117_);
    leanh::lean_dec(v___y_8116_);
    return v_res_8120_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(
    mut v___y_8121_: *mut leanh::LeanObject,
    mut v___y_8122_: *mut leanh::LeanObject,
    mut v___y_8123_: *mut leanh::LeanObject,
    mut v___y_8124_: *mut leanh::LeanObject,
    mut v___y_8125_: *mut leanh::LeanObject,
    mut v___y_8126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8132_: u8 = 0;
    let mut v_fileMap_8133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_8134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_8135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_8136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_8137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_8138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_8139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8142_: u8 = 0;
    let mut v___x_8143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8150_: u8 = 0;
    let mut v_unused_8151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8128_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_8124_, v___y_8125_, v___y_8126_);
                v_a_8129_ = leanh::lean_ctor_get(v___x_8128_, 0);
                v_isSharedCheck_8153_ = (!leanh::lean_is_exclusive(v___x_8128_)) as u8;
                if v_isSharedCheck_8153_ == 0 {
                    v___x_8131_ = v___x_8128_;
                    v_isShared_8132_ = v_isSharedCheck_8153_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_8129_);
                    leanh::lean_dec(v___x_8128_);
                    v___x_8131_ = leanh::lean_box(0);
                    v_isShared_8132_ = v_isSharedCheck_8153_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_8133_ = leanh::lean_ctor_get(v___y_8125_, 1);
                v_env_8134_ = leanh::lean_ctor_get(v_a_8129_, 0);
                v_mctx_8135_ = leanh::lean_ctor_get(v_a_8129_, 3);
                v_options_8136_ = leanh::lean_ctor_get(v_a_8129_, 4);
                v_currNamespace_8137_ = leanh::lean_ctor_get(v_a_8129_, 5);
                v_openDecls_8138_ = leanh::lean_ctor_get(v_a_8129_, 6);
                v_ngen_8139_ = leanh::lean_ctor_get(v_a_8129_, 7);
                v_isSharedCheck_8150_ = (!leanh::lean_is_exclusive(v_a_8129_)) as u8;
                if v_isSharedCheck_8150_ == 0 {
                    v_unused_8151_ = leanh::lean_ctor_get(v_a_8129_, 2);
                    leanh::lean_dec(v_unused_8151_);
                    v_unused_8152_ = leanh::lean_ctor_get(v_a_8129_, 1);
                    leanh::lean_dec(v_unused_8152_);
                    v___x_8141_ = v_a_8129_;
                    v_isShared_8142_ = v_isSharedCheck_8150_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_ngen_8139_);
                    leanh::lean_inc(v_openDecls_8138_);
                    leanh::lean_inc(v_currNamespace_8137_);
                    leanh::lean_inc(v_options_8136_);
                    leanh::lean_inc(v_mctx_8135_);
                    leanh::lean_inc(v_env_8134_);
                    leanh::lean_dec(v_a_8129_);
                    v___x_8141_ = leanh::lean_box(0);
                    v_isShared_8142_ = v_isSharedCheck_8150_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8143_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_fileMap_8133_);
                if v_isShared_8142_ == 0 {
                    leanh::lean_ctor_set(v___x_8141_, 2, v_fileMap_8133_);
                    leanh::lean_ctor_set(v___x_8141_, 1, v___x_8143_);
                    v___x_8145_ = v___x_8141_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8149_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 0, v_env_8134_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 1, v___x_8143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 2, v_fileMap_8133_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 3, v_mctx_8135_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 4, v_options_8136_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 5, v_currNamespace_8137_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 6, v_openDecls_8138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8149_, 7, v_ngen_8139_);
                    v___x_8145_ = v_reuseFailAlloc_8149_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8132_ == 0 {
                    leanh::lean_ctor_set(v___x_8131_, 0, v___x_8145_);
                    v___x_8147_ = v___x_8131_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8148_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8148_, 0, v___x_8145_);
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
    mut v___y_8154_: *mut leanh::LeanObject,
    mut v___y_8155_: *mut leanh::LeanObject,
    mut v___y_8156_: *mut leanh::LeanObject,
    mut v___y_8157_: *mut leanh::LeanObject,
    mut v___y_8158_: *mut leanh::LeanObject,
    mut v___y_8159_: *mut leanh::LeanObject,
    mut v___y_8160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8161_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_8154_, v___y_8155_, v___y_8156_, v___y_8157_, v___y_8158_, v___y_8159_);
    leanh::lean_dec(v___y_8159_);
    leanh::lean_dec_ref(v___y_8158_);
    leanh::lean_dec(v___y_8157_);
    leanh::lean_dec_ref(v___y_8156_);
    leanh::lean_dec(v___y_8155_);
    leanh::lean_dec_ref(v___y_8154_);
    return v_res_8161_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(
    mut v___y_8162_: *mut leanh::LeanObject,
    mut v___y_8163_: *mut leanh::LeanObject,
    mut v___y_8164_: *mut leanh::LeanObject,
    mut v___y_8165_: *mut leanh::LeanObject,
    mut v___y_8166_: *mut leanh::LeanObject,
    mut v___y_8167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8173_: u8 = 0;
    let mut v___x_8174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8169_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_8162_, v___y_8163_, v___y_8164_, v___y_8165_, v___y_8166_, v___y_8167_);
                v_a_8170_ = leanh::lean_ctor_get(v___x_8169_, 0);
                v_isSharedCheck_8179_ = (!leanh::lean_is_exclusive(v___x_8169_)) as u8;
                if v_isSharedCheck_8179_ == 0 {
                    v___x_8172_ = v___x_8169_;
                    v_isShared_8173_ = v_isSharedCheck_8179_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_8170_);
                    leanh::lean_dec(v___x_8169_);
                    v___x_8172_ = leanh::lean_box(0);
                    v_isShared_8173_ = v_isSharedCheck_8179_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8174_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8174_, 0, v_a_8170_);
                v___x_8175_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8175_, 0, v___x_8174_);
                if v_isShared_8173_ == 0 {
                    leanh::lean_ctor_set(v___x_8172_, 0, v___x_8175_);
                    v___x_8177_ = v___x_8172_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8178_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8178_, 0, v___x_8175_);
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
    mut v___y_8180_: *mut leanh::LeanObject,
    mut v___y_8181_: *mut leanh::LeanObject,
    mut v___y_8182_: *mut leanh::LeanObject,
    mut v___y_8183_: *mut leanh::LeanObject,
    mut v___y_8184_: *mut leanh::LeanObject,
    mut v___y_8185_: *mut leanh::LeanObject,
    mut v___y_8186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8187_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(v___y_8180_, v___y_8181_, v___y_8182_, v___y_8183_, v___y_8184_, v___y_8185_);
    leanh::lean_dec(v___y_8185_);
    leanh::lean_dec_ref(v___y_8184_);
    leanh::lean_dec(v___y_8183_);
    leanh::lean_dec_ref(v___y_8182_);
    leanh::lean_dec(v___y_8181_);
    leanh::lean_dec_ref(v___y_8180_);
    return v_res_8187_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(
    mut v_x_8189_: *mut leanh::LeanObject,
    mut v___y_8190_: *mut leanh::LeanObject,
    mut v___y_8191_: *mut leanh::LeanObject,
    mut v___y_8192_: *mut leanh::LeanObject,
    mut v___y_8193_: *mut leanh::LeanObject,
    mut v___y_8194_: *mut leanh::LeanObject,
    mut v___y_8195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_8197_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0;
    v___x_8198_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_8189_, v___f_8197_, v___y_8190_, v___y_8191_, v___y_8192_, v___y_8193_, v___y_8194_, v___y_8195_);
    return v___x_8198_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___boxed(
    mut v_x_8199_: *mut leanh::LeanObject,
    mut v___y_8200_: *mut leanh::LeanObject,
    mut v___y_8201_: *mut leanh::LeanObject,
    mut v___y_8202_: *mut leanh::LeanObject,
    mut v___y_8203_: *mut leanh::LeanObject,
    mut v___y_8204_: *mut leanh::LeanObject,
    mut v___y_8205_: *mut leanh::LeanObject,
    mut v___y_8206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8207_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_8199_, v___y_8200_, v___y_8201_, v___y_8202_, v___y_8203_, v___y_8204_, v___y_8205_);
    leanh::lean_dec(v___y_8205_);
    leanh::lean_dec_ref(v___y_8204_);
    leanh::lean_dec(v___y_8203_);
    leanh::lean_dec_ref(v___y_8202_);
    leanh::lean_dec(v___y_8201_);
    leanh::lean_dec_ref(v___y_8200_);
    return v_res_8207_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(
    mut v_00_u03b1_8208_: *mut leanh::LeanObject,
    mut v_x_8209_: *mut leanh::LeanObject,
    mut v___y_8210_: *mut leanh::LeanObject,
    mut v___y_8211_: *mut leanh::LeanObject,
    mut v___y_8212_: *mut leanh::LeanObject,
    mut v___y_8213_: *mut leanh::LeanObject,
    mut v___y_8214_: *mut leanh::LeanObject,
    mut v___y_8215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8217_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_8209_, v___y_8210_, v___y_8211_, v___y_8212_, v___y_8213_, v___y_8214_, v___y_8215_);
    return v___x_8217_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed(
    mut v_00_u03b1_8218_: *mut leanh::LeanObject,
    mut v_x_8219_: *mut leanh::LeanObject,
    mut v___y_8220_: *mut leanh::LeanObject,
    mut v___y_8221_: *mut leanh::LeanObject,
    mut v___y_8222_: *mut leanh::LeanObject,
    mut v___y_8223_: *mut leanh::LeanObject,
    mut v___y_8224_: *mut leanh::LeanObject,
    mut v___y_8225_: *mut leanh::LeanObject,
    mut v___y_8226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8227_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_8225_);
    leanh::lean_dec_ref(v___y_8224_);
    leanh::lean_dec(v___y_8223_);
    leanh::lean_dec_ref(v___y_8222_);
    leanh::lean_dec(v___y_8221_);
    leanh::lean_dec_ref(v___y_8220_);
    return v_res_8227_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4() -> u64 {
    let mut v___x_8245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8246_: u64 = 0;
    v___x_8245_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3;
    v___x_8246_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_8245_);
    return v___x_8246_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_8247_: u64 = 0;
    let mut v___x_8248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8247_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4,
    );
    v___x_8248_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3;
    v___x_8249_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_8249_, 0, v___x_8248_);
    leanh::lean_ctor_set_uint64(
        v___x_8249_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_8247_,
    );
    return v___x_8249_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_8250_: u8 = 0;
    let mut v___x_8251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8256_: u8 = 0;
    let mut v___x_8257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8250_ = 1;
    v___x_8251_ = leanh::lean_unsigned_to_nat(0);
    v___x_8252_ = leanh::lean_box(0);
    v___x_8253_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1;
    v___x_8254_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2,
    );
    v___x_8255_ = leanh::lean_box(1);
    v___x_8256_ = 0;
    v___x_8257_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5,
    );
    v___x_8258_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
    leanh::lean_ctor_set(v___x_8258_, 0, v___x_8257_);
    leanh::lean_ctor_set(v___x_8258_, 1, v___x_8255_);
    leanh::lean_ctor_set(v___x_8258_, 2, v___x_8254_);
    leanh::lean_ctor_set(v___x_8258_, 3, v___x_8253_);
    leanh::lean_ctor_set(v___x_8258_, 4, v___x_8252_);
    leanh::lean_ctor_set(v___x_8258_, 5, v___x_8251_);
    leanh::lean_ctor_set(v___x_8258_, 6, v___x_8252_);
    leanh::lean_ctor_set_uint8(
        v___x_8258_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
        v___x_8256_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_8258_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
        v___x_8256_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_8258_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
        v___x_8256_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_8258_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
        v___x_8250_,
    );
    return v___x_8258_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_8259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8259_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1,
    );
    v___x_8260_ = leanh::lean_unsigned_to_nat(0);
    v___x_8261_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_8261_, 0, v___x_8260_);
    leanh::lean_ctor_set(v___x_8261_, 1, v___x_8260_);
    leanh::lean_ctor_set(v___x_8261_, 2, v___x_8260_);
    leanh::lean_ctor_set(v___x_8261_, 3, v___x_8260_);
    leanh::lean_ctor_set(v___x_8261_, 4, v___x_8259_);
    leanh::lean_ctor_set(v___x_8261_, 5, v___x_8259_);
    leanh::lean_ctor_set(v___x_8261_, 6, v___x_8259_);
    leanh::lean_ctor_set(v___x_8261_, 7, v___x_8259_);
    leanh::lean_ctor_set(v___x_8261_, 8, v___x_8259_);
    leanh::lean_ctor_set(v___x_8261_, 9, v___x_8259_);
    return v___x_8261_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_8262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8262_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1,
    );
    v___x_8263_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_8263_, 0, v___x_8262_);
    leanh::lean_ctor_set(v___x_8263_, 1, v___x_8262_);
    leanh::lean_ctor_set(v___x_8263_, 2, v___x_8262_);
    leanh::lean_ctor_set(v___x_8263_, 3, v___x_8262_);
    leanh::lean_ctor_set(v___x_8263_, 4, v___x_8262_);
    leanh::lean_ctor_set(v___x_8263_, 5, v___x_8262_);
    return v___x_8263_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_8264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8264_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1,
    );
    v___x_8265_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_8265_, 0, v___x_8264_);
    leanh::lean_ctor_set(v___x_8265_, 1, v___x_8264_);
    leanh::lean_ctor_set(v___x_8265_, 2, v___x_8264_);
    leanh::lean_ctor_set(v___x_8265_, 3, v___x_8264_);
    leanh::lean_ctor_set(v___x_8265_, 4, v___x_8264_);
    return v___x_8265_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_8266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8266_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9,
    );
    v___x_8267_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_8268_ = leanh::lean_box(1);
    v___x_8269_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8,
    );
    v___x_8270_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7,
    );
    v___x_8271_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_8271_, 0, v___x_8270_);
    leanh::lean_ctor_set(v___x_8271_, 1, v___x_8269_);
    leanh::lean_ctor_set(v___x_8271_, 2, v___x_8268_);
    leanh::lean_ctor_set(v___x_8271_, 3, v___x_8267_);
    leanh::lean_ctor_set(v___x_8271_, 4, v___x_8266_);
    return v___x_8271_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___redArg(
    mut v_mx_8275_: *mut leanh::LeanObject,
    mut v_a_8276_: *mut leanh::LeanObject,
    mut v_a_8277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8289_: u8 = 0;
    let mut v___x_8290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8295_: u8 = 0;
    let mut v_a_8296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8299_: u8 = 0;
    let mut v___x_8301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8279_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2;
                v___x_8280_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6,
                );
                v___x_8281_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10,
                );
                v___x_8282_ = lean_st_mk_ref(v___x_8281_);
                v___x_8283_ = leanh::lean_alloc_closure(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed as *mut core::ffi::c_void, 9, 2);
                leanh::lean_closure_set(v___x_8283_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_8283_, 1, v_mx_8275_);
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
                if leanh::lean_obj_tag(v___x_8285_) == 0 {
                    v_a_8286_ = leanh::lean_ctor_get(v___x_8285_, 0);
                    v_isSharedCheck_8295_ = (!leanh::lean_is_exclusive(v___x_8285_)) as u8;
                    if v_isSharedCheck_8295_ == 0 {
                        v___x_8288_ = v___x_8285_;
                        v_isShared_8289_ = v_isSharedCheck_8295_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8286_);
                        leanh::lean_dec(v___x_8285_);
                        v___x_8288_ = leanh::lean_box(0);
                        v_isShared_8289_ = v_isSharedCheck_8295_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_8282_);
                    v_a_8296_ = leanh::lean_ctor_get(v___x_8285_, 0);
                    v_isSharedCheck_8303_ = (!leanh::lean_is_exclusive(v___x_8285_)) as u8;
                    if v_isSharedCheck_8303_ == 0 {
                        v___x_8298_ = v___x_8285_;
                        v_isShared_8299_ = v_isSharedCheck_8303_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8296_);
                        leanh::lean_dec(v___x_8285_);
                        v___x_8298_ = leanh::lean_box(0);
                        v_isShared_8299_ = v_isSharedCheck_8303_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8290_ = lean_st_ref_get(v___x_8282_);
                leanh::lean_dec(v___x_8282_);
                leanh::lean_dec(v___x_8290_);
                v_fst_8291_ = leanh::lean_ctor_get(v_a_8286_, 0);
                leanh::lean_inc(v_fst_8291_);
                leanh::lean_dec(v_a_8286_);
                if v_isShared_8289_ == 0 {
                    leanh::lean_ctor_set(v___x_8288_, 0, v_fst_8291_);
                    v___x_8293_ = v___x_8288_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8294_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8294_, 0, v_fst_8291_);
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
                    v_reuseFailAlloc_8302_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8302_, 0, v_a_8296_);
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
    mut v_mx_8304_: *mut leanh::LeanObject,
    mut v_a_8305_: *mut leanh::LeanObject,
    mut v_a_8306_: *mut leanh::LeanObject,
    mut v_a_8307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8308_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_8304_, v_a_8305_, v_a_8306_);
    leanh::lean_dec(v_a_8306_);
    leanh::lean_dec_ref(v_a_8305_);
    return v_res_8308_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab(
    mut v_00_u03b1_8309_: *mut leanh::LeanObject,
    mut v_mx_8310_: *mut leanh::LeanObject,
    mut v_a_8311_: *mut leanh::LeanObject,
    mut v_a_8312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8314_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_8310_, v_a_8311_, v_a_8312_);
    return v___x_8314_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___boxed(
    mut v_00_u03b1_8315_: *mut leanh::LeanObject,
    mut v_mx_8316_: *mut leanh::LeanObject,
    mut v_a_8317_: *mut leanh::LeanObject,
    mut v_a_8318_: *mut leanh::LeanObject,
    mut v_a_8319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8320_ =
        l_Lean_Elab_ConfigEval_runConfigElab(v_00_u03b1_8315_, v_mx_8316_, v_a_8317_, v_a_8318_);
    leanh::lean_dec(v_a_8318_);
    leanh::lean_dec_ref(v_a_8317_);
    return v_res_8320_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(
    mut v___y_8321_: *mut leanh::LeanObject,
    mut v___y_8322_: *mut leanh::LeanObject,
    mut v___y_8323_: *mut leanh::LeanObject,
    mut v___y_8324_: *mut leanh::LeanObject,
    mut v___y_8325_: *mut leanh::LeanObject,
    mut v___y_8326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8328_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_8324_, v___y_8325_, v___y_8326_);
    return v___x_8328_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___boxed(
    mut v___y_8329_: *mut leanh::LeanObject,
    mut v___y_8330_: *mut leanh::LeanObject,
    mut v___y_8331_: *mut leanh::LeanObject,
    mut v___y_8332_: *mut leanh::LeanObject,
    mut v___y_8333_: *mut leanh::LeanObject,
    mut v___y_8334_: *mut leanh::LeanObject,
    mut v___y_8335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8336_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(v___y_8329_, v___y_8330_, v___y_8331_, v___y_8332_, v___y_8333_, v___y_8334_);
    leanh::lean_dec(v___y_8334_);
    leanh::lean_dec_ref(v___y_8333_);
    leanh::lean_dec(v___y_8332_);
    leanh::lean_dec_ref(v___y_8331_);
    leanh::lean_dec(v___y_8330_);
    leanh::lean_dec_ref(v___y_8329_);
    return v_res_8336_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(
    mut v___y_8337_: *mut leanh::LeanObject,
    mut v___y_8338_: *mut leanh::LeanObject,
    mut v___y_8339_: *mut leanh::LeanObject,
    mut v___y_8340_: *mut leanh::LeanObject,
    mut v___y_8341_: *mut leanh::LeanObject,
    mut v___y_8342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8344_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_8342_);
    return v___x_8344_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___boxed(
    mut v___y_8345_: *mut leanh::LeanObject,
    mut v___y_8346_: *mut leanh::LeanObject,
    mut v___y_8347_: *mut leanh::LeanObject,
    mut v___y_8348_: *mut leanh::LeanObject,
    mut v___y_8349_: *mut leanh::LeanObject,
    mut v___y_8350_: *mut leanh::LeanObject,
    mut v___y_8351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8352_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(v___y_8345_, v___y_8346_, v___y_8347_, v___y_8348_, v___y_8349_, v___y_8350_);
    leanh::lean_dec(v___y_8350_);
    leanh::lean_dec_ref(v___y_8349_);
    leanh::lean_dec(v___y_8348_);
    leanh::lean_dec_ref(v___y_8347_);
    leanh::lean_dec(v___y_8346_);
    leanh::lean_dec_ref(v___y_8345_);
    return v_res_8352_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(
    mut v_00_u03b1_8353_: *mut leanh::LeanObject,
    mut v_x_8354_: *mut leanh::LeanObject,
    mut v_ctx_x3f_8355_: *mut leanh::LeanObject,
    mut v___y_8356_: *mut leanh::LeanObject,
    mut v___y_8357_: *mut leanh::LeanObject,
    mut v___y_8358_: *mut leanh::LeanObject,
    mut v___y_8359_: *mut leanh::LeanObject,
    mut v___y_8360_: *mut leanh::LeanObject,
    mut v___y_8361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8363_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_8354_, v_ctx_x3f_8355_, v___y_8356_, v___y_8357_, v___y_8358_, v___y_8359_, v___y_8360_, v___y_8361_);
    return v___x_8363_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___boxed(
    mut v_00_u03b1_8364_: *mut leanh::LeanObject,
    mut v_x_8365_: *mut leanh::LeanObject,
    mut v_ctx_x3f_8366_: *mut leanh::LeanObject,
    mut v___y_8367_: *mut leanh::LeanObject,
    mut v___y_8368_: *mut leanh::LeanObject,
    mut v___y_8369_: *mut leanh::LeanObject,
    mut v___y_8370_: *mut leanh::LeanObject,
    mut v___y_8371_: *mut leanh::LeanObject,
    mut v___y_8372_: *mut leanh::LeanObject,
    mut v___y_8373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8374_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(v_00_u03b1_8364_, v_x_8365_, v_ctx_x3f_8366_, v___y_8367_, v___y_8368_, v___y_8369_, v___y_8370_, v___y_8371_, v___y_8372_);
    leanh::lean_dec(v___y_8372_);
    leanh::lean_dec_ref(v___y_8371_);
    leanh::lean_dec(v___y_8370_);
    leanh::lean_dec_ref(v___y_8369_);
    leanh::lean_dec(v___y_8368_);
    leanh::lean_dec_ref(v___y_8367_);
    return v_res_8374_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(
    mut v_eval_8375_: *mut leanh::LeanObject,
    mut v_logExceptions_8376_: u8,
    mut v_onErr_8377_: *mut leanh::LeanObject,
    mut v_init_8378_: *mut leanh::LeanObject,
    mut v_cfg_8379_: *mut leanh::LeanObject,
    mut v___y_8380_: *mut leanh::LeanObject,
    mut v___y_8381_: *mut leanh::LeanObject,
    mut v___y_8382_: *mut leanh::LeanObject,
    mut v___y_8383_: *mut leanh::LeanObject,
    mut v___y_8384_: *mut leanh::LeanObject,
    mut v___y_8385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8387_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_8375_, v_logExceptions_8376_, v_onErr_8377_, v_init_8378_, v_cfg_8379_, v___y_8380_, v___y_8381_, v___y_8382_, v___y_8383_, v___y_8384_, v___y_8385_);
    return v___x_8387_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed(
    mut v_eval_8388_: *mut leanh::LeanObject,
    mut v_logExceptions_8389_: *mut leanh::LeanObject,
    mut v_onErr_8390_: *mut leanh::LeanObject,
    mut v_init_8391_: *mut leanh::LeanObject,
    mut v_cfg_8392_: *mut leanh::LeanObject,
    mut v___y_8393_: *mut leanh::LeanObject,
    mut v___y_8394_: *mut leanh::LeanObject,
    mut v___y_8395_: *mut leanh::LeanObject,
    mut v___y_8396_: *mut leanh::LeanObject,
    mut v___y_8397_: *mut leanh::LeanObject,
    mut v___y_8398_: *mut leanh::LeanObject,
    mut v___y_8399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_8400_: u8 = 0;
    let mut v_res_8401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8400_ = (leanh::lean_unbox(v_logExceptions_8389_) as u8);
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
    leanh::lean_dec(v___y_8398_);
    leanh::lean_dec_ref(v___y_8397_);
    leanh::lean_dec(v___y_8396_);
    leanh::lean_dec_ref(v___y_8395_);
    leanh::lean_dec(v___y_8394_);
    leanh::lean_dec_ref(v___y_8393_);
    return v_res_8401_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
    mut v_eval_8402_: *mut leanh::LeanObject,
    mut v_init_8403_: *mut leanh::LeanObject,
    mut v_cfg_8404_: *mut leanh::LeanObject,
    mut v_onErr_8405_: *mut leanh::LeanObject,
    mut v_logExceptions_8406_: u8,
    mut v_a_8407_: *mut leanh::LeanObject,
    mut v_a_8408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8413_: u8 = 0;
    let mut v___x_8414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8417_: u8 = 0;
    let mut v___x_8418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8420_: u8 = 0;
    let mut v___x_8421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8410_ = leanh::lean_box((v_logExceptions_8406_) as usize);
                leanh::lean_inc_n(v_cfg_8404_, 2);
                leanh::lean_inc(v_init_8403_);
                v___f_8411_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    5,
                );
                leanh::lean_closure_set(v___f_8411_, 0, v_eval_8402_);
                leanh::lean_closure_set(v___f_8411_, 1, v___x_8410_);
                leanh::lean_closure_set(v___f_8411_, 2, v_onErr_8405_);
                leanh::lean_closure_set(v___f_8411_, 3, v_init_8403_);
                leanh::lean_closure_set(v___f_8411_, 4, v_cfg_8404_);
                v___x_8416_ = leanh::lean_unsigned_to_nat(0);
                v___x_8417_ = l_Lean_Syntax_matchesNull(v_cfg_8404_, v___x_8416_);
                if v___x_8417_ == 0 {
                    v___x_8418_ = l_Lean_Syntax_getNumArgs(v_cfg_8404_);
                    v___x_8419_ = leanh::lean_unsigned_to_nat(1);
                    v___x_8420_ = lean_nat_dec_eq(v___x_8418_, v___x_8419_);
                    leanh::lean_dec(v___x_8418_);
                    if v___x_8420_ == 0 {
                        leanh::lean_dec(v_cfg_8404_);
                        v___y_8413_ = v___x_8420_;
                        state = 1;
                        continue;
                    } else {
                        v___x_8421_ = l_Lean_Syntax_getArg(v_cfg_8404_, v___x_8416_);
                        leanh::lean_dec(v_cfg_8404_);
                        v___x_8422_ = l_Lean_Syntax_matchesNull(v___x_8421_, v___x_8416_);
                        v___y_8413_ = v___x_8422_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_cfg_8404_);
                    v___y_8413_ = v___x_8417_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_8413_ == 0 {
                    leanh::lean_dec(v_init_8403_);
                    v___x_8414_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(
                        v___f_8411_,
                        v_a_8407_,
                        v_a_8408_,
                    );
                    return v___x_8414_;
                } else {
                    leanh::lean_dec_ref(v___f_8411_);
                    v___x_8415_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8415_, 0, v_init_8403_);
                    return v___x_8415_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___boxed(
    mut v_eval_8423_: *mut leanh::LeanObject,
    mut v_init_8424_: *mut leanh::LeanObject,
    mut v_cfg_8425_: *mut leanh::LeanObject,
    mut v_onErr_8426_: *mut leanh::LeanObject,
    mut v_logExceptions_8427_: *mut leanh::LeanObject,
    mut v_a_8428_: *mut leanh::LeanObject,
    mut v_a_8429_: *mut leanh::LeanObject,
    mut v_a_8430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_8431_: u8 = 0;
    let mut v_res_8432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8431_ = (leanh::lean_unbox(v_logExceptions_8427_) as u8);
    v_res_8432_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
        v_eval_8423_,
        v_init_8424_,
        v_cfg_8425_,
        v_onErr_8426_,
        v_logExceptions_boxed_8431_,
        v_a_8428_,
        v_a_8429_,
    );
    leanh::lean_dec(v_a_8429_);
    leanh::lean_dec_ref(v_a_8428_);
    return v_res_8432_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(
    mut v_00_u03b1_8433_: *mut leanh::LeanObject,
    mut v_eval_8434_: *mut leanh::LeanObject,
    mut v_init_8435_: *mut leanh::LeanObject,
    mut v_cfg_8436_: *mut leanh::LeanObject,
    mut v_onErr_8437_: *mut leanh::LeanObject,
    mut v_logExceptions_8438_: u8,
    mut v_a_8439_: *mut leanh::LeanObject,
    mut v_a_8440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8442_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_8443_: *mut leanh::LeanObject,
    mut v_eval_8444_: *mut leanh::LeanObject,
    mut v_init_8445_: *mut leanh::LeanObject,
    mut v_cfg_8446_: *mut leanh::LeanObject,
    mut v_onErr_8447_: *mut leanh::LeanObject,
    mut v_logExceptions_8448_: *mut leanh::LeanObject,
    mut v_a_8449_: *mut leanh::LeanObject,
    mut v_a_8450_: *mut leanh::LeanObject,
    mut v_a_8451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_8452_: u8 = 0;
    let mut v_res_8453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8452_ = (leanh::lean_unbox(v_logExceptions_8448_) as u8);
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
    leanh::lean_dec(v_a_8450_);
    leanh::lean_dec_ref(v_a_8449_);
    return v_res_8453_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(
    mut v_eval_8454_: *mut leanh::LeanObject,
    mut v_logExceptions_8455_: u8,
    mut v_onErr_8456_: *mut leanh::LeanObject,
    mut v_init_8457_: *mut leanh::LeanObject,
    mut v_cfgs_8458_: *mut leanh::LeanObject,
    mut v___y_8459_: *mut leanh::LeanObject,
    mut v___y_8460_: *mut leanh::LeanObject,
    mut v___y_8461_: *mut leanh::LeanObject,
    mut v___y_8462_: *mut leanh::LeanObject,
    mut v___y_8463_: *mut leanh::LeanObject,
    mut v___y_8464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8466_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_8454_, v_logExceptions_8455_, v_onErr_8456_, v_init_8457_, v_cfgs_8458_, v___y_8459_, v___y_8460_, v___y_8461_, v___y_8462_, v___y_8463_, v___y_8464_);
    return v___x_8466_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed(
    mut v_eval_8467_: *mut leanh::LeanObject,
    mut v_logExceptions_8468_: *mut leanh::LeanObject,
    mut v_onErr_8469_: *mut leanh::LeanObject,
    mut v_init_8470_: *mut leanh::LeanObject,
    mut v_cfgs_8471_: *mut leanh::LeanObject,
    mut v___y_8472_: *mut leanh::LeanObject,
    mut v___y_8473_: *mut leanh::LeanObject,
    mut v___y_8474_: *mut leanh::LeanObject,
    mut v___y_8475_: *mut leanh::LeanObject,
    mut v___y_8476_: *mut leanh::LeanObject,
    mut v___y_8477_: *mut leanh::LeanObject,
    mut v___y_8478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_8479_: u8 = 0;
    let mut v_res_8480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8479_ = (leanh::lean_unbox(v_logExceptions_8468_) as u8);
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
    leanh::lean_dec(v___y_8477_);
    leanh::lean_dec_ref(v___y_8476_);
    leanh::lean_dec(v___y_8475_);
    leanh::lean_dec_ref(v___y_8474_);
    leanh::lean_dec(v___y_8473_);
    leanh::lean_dec_ref(v___y_8472_);
    leanh::lean_dec_ref(v_cfgs_8471_);
    return v_res_8480_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(
    mut v_eval_8481_: *mut leanh::LeanObject,
    mut v_init_8482_: *mut leanh::LeanObject,
    mut v_cfgs_8483_: *mut leanh::LeanObject,
    mut v_onErr_8484_: *mut leanh::LeanObject,
    mut v_logExceptions_8485_: u8,
    mut v_a_8486_: *mut leanh::LeanObject,
    mut v_a_8487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8491_: u8 = 0;
    v___x_8489_ = lean_array_get_size(v_cfgs_8483_);
    v___x_8490_ = leanh::lean_unsigned_to_nat(0);
    v___x_8491_ = lean_nat_dec_eq(v___x_8489_, v___x_8490_);
    if v___x_8491_ == 0 {
        let mut v___x_8492_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_8493_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8494_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_8492_ = leanh::lean_box((v_logExceptions_8485_) as usize);
        v___f_8493_ = leanh::lean_alloc_closure(
            l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            12,
            5,
        );
        leanh::lean_closure_set(v___f_8493_, 0, v_eval_8481_);
        leanh::lean_closure_set(v___f_8493_, 1, v___x_8492_);
        leanh::lean_closure_set(v___f_8493_, 2, v_onErr_8484_);
        leanh::lean_closure_set(v___f_8493_, 3, v_init_8482_);
        leanh::lean_closure_set(v___f_8493_, 4, v_cfgs_8483_);
        v___x_8494_ =
            l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_8493_, v_a_8486_, v_a_8487_);
        return v___x_8494_;
    } else {
        let mut v___x_8495_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_onErr_8484_);
        leanh::lean_dec_ref(v_cfgs_8483_);
        leanh::lean_dec_ref(v_eval_8481_);
        v___x_8495_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_8495_, 0, v_init_8482_);
        return v___x_8495_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___boxed(
    mut v_eval_8496_: *mut leanh::LeanObject,
    mut v_init_8497_: *mut leanh::LeanObject,
    mut v_cfgs_8498_: *mut leanh::LeanObject,
    mut v_onErr_8499_: *mut leanh::LeanObject,
    mut v_logExceptions_8500_: *mut leanh::LeanObject,
    mut v_a_8501_: *mut leanh::LeanObject,
    mut v_a_8502_: *mut leanh::LeanObject,
    mut v_a_8503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_8504_: u8 = 0;
    let mut v_res_8505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8504_ = (leanh::lean_unbox(v_logExceptions_8500_) as u8);
    v_res_8505_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(
        v_eval_8496_,
        v_init_8497_,
        v_cfgs_8498_,
        v_onErr_8499_,
        v_logExceptions_boxed_8504_,
        v_a_8501_,
        v_a_8502_,
    );
    leanh::lean_dec(v_a_8502_);
    leanh::lean_dec_ref(v_a_8501_);
    return v_res_8505_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(
    mut v_00_u03b1_8506_: *mut leanh::LeanObject,
    mut v_eval_8507_: *mut leanh::LeanObject,
    mut v_init_8508_: *mut leanh::LeanObject,
    mut v_cfgs_8509_: *mut leanh::LeanObject,
    mut v_onErr_8510_: *mut leanh::LeanObject,
    mut v_logExceptions_8511_: u8,
    mut v_a_8512_: *mut leanh::LeanObject,
    mut v_a_8513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8515_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_8516_: *mut leanh::LeanObject,
    mut v_eval_8517_: *mut leanh::LeanObject,
    mut v_init_8518_: *mut leanh::LeanObject,
    mut v_cfgs_8519_: *mut leanh::LeanObject,
    mut v_onErr_8520_: *mut leanh::LeanObject,
    mut v_logExceptions_8521_: *mut leanh::LeanObject,
    mut v_a_8522_: *mut leanh::LeanObject,
    mut v_a_8523_: *mut leanh::LeanObject,
    mut v_a_8524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_logExceptions_boxed_8525_: u8 = 0;
    let mut v_res_8526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8525_ = (leanh::lean_unbox(v_logExceptions_8521_) as u8);
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
    leanh::lean_dec(v_a_8523_);
    leanh::lean_dec_ref(v_a_8522_);
    return v_res_8526_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ConfigEval_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval_Basic(
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
pub unsafe fn initialize_Lean_Elab_ConfigEval_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ConfigEval_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_SyntheticMVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval_Basic(builtin);
}