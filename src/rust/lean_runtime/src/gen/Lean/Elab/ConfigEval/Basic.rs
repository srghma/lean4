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
    l_Lean_Name_appendCore, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_Name_str___override, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId,
    l_Lean_Syntax_getNumArgs, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isMissing, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesIdent,
    l_Lean_Syntax_matchesNull, l_Lean_replaceRef,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_uint32_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_whnf;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_6, lean_apply_7, lean_apply_8,
    lean_apply_9, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_uint32, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 11,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9_value: LeanClosureObject<
    3,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23_value: LeanStringObject<
    34,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29_value: LeanStringObject<
    1,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31_value: LeanStringObject<
    29,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5_value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0_value: LeanStringObject<
    35,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            79, 112, 116, 105, 111, 110, 32, 105, 115, 32, 110, 111, 116, 32, 98, 111, 111, 108,
            101, 97, 110, 45, 118, 97, 108, 117, 101, 100, 44, 32, 115, 111, 32, 96, 40, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0_value:
    LeanStringObject<29> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2_value:
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
    m_data: [32, 102, 111, 114, 32, 96, 0],
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4_value:
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
    m_data: [32, 96, 0],
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2_value:
    LeanStringObject<29> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2 as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6_value: LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value: LeanStringObject<5> =
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
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6_value)
                as *mut LeanObject,
            9255189395584251158 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9_value: LeanStringObject<6> =
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
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value: LeanCtorObject<3> =
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
                l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9_value)
                as *mut LeanObject,
            15761733860085307253 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11_value: LeanStringObject<2> =
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
        m_data: [43, 0],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12_value: LeanStringObject<2> =
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
        m_data: [45, 0],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13_value: LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 58, 32, 0]};
static mut l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0_value:
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
    m_data: [105, 100, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1_value:
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
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0_value
        ) as *mut LeanObject,
        6041859491766292191 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5_value:
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
    m_data: [95, 99, 102, 103, 95, 100, 117, 109, 109, 121, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6_value:
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
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5_value
        ) as *mut LeanObject,
        16753651297112092462 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8_value:
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
    m_data: [67, 111, 110, 102, 105, 103, 69, 118, 97, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9_value:
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
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8_value
        ) as *mut LeanObject,
        17728754291599005030 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2_value: LeanCtorObject<10> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 8
                + 16) as u16,
            other: 8,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value)
                as *mut LeanObject,
            16843009 as *mut LeanObject,
            65537 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
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
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4: u64 = 0;
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_value: LeanCtorObject<7> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 7
                + 0) as u16,
            other: 7,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(
    mut v_inst_4264_: *mut LeanObject,
    mut v_stx_4265_: *mut LeanObject,
    mut v_a_4266_: *mut LeanObject,
    mut v_a_4267_: *mut LeanObject,
    mut v_a_4268_: *mut LeanObject,
    mut v_a_4269_: *mut LeanObject,
    mut v_a_4270_: *mut LeanObject,
    mut v_a_4271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_evalTerm_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4286_: u8 = 0;
    let mut v_cancelTk_x3f_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4288_: u8 = 0;
    let mut v_inheritedTraceOptions_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4296_: u8 = 0;
    let mut v_fst_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v_a_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalTerm_4273_ = lean_ctor_get(v_inst_4264_, 0);
                lean_inc_ref(v_evalTerm_4273_);
                lean_dec_ref(v_inst_4264_);
                v_fileName_4274_ = lean_ctor_get(v_a_4270_, 0);
                v_fileMap_4275_ = lean_ctor_get(v_a_4270_, 1);
                v_options_4276_ = lean_ctor_get(v_a_4270_, 2);
                v_currRecDepth_4277_ = lean_ctor_get(v_a_4270_, 3);
                v_maxRecDepth_4278_ = lean_ctor_get(v_a_4270_, 4);
                v_ref_4279_ = lean_ctor_get(v_a_4270_, 5);
                v_currNamespace_4280_ = lean_ctor_get(v_a_4270_, 6);
                v_openDecls_4281_ = lean_ctor_get(v_a_4270_, 7);
                v_initHeartbeats_4282_ = lean_ctor_get(v_a_4270_, 8);
                v_maxHeartbeats_4283_ = lean_ctor_get(v_a_4270_, 9);
                v_quotContext_4284_ = lean_ctor_get(v_a_4270_, 10);
                v_currMacroScope_4285_ = lean_ctor_get(v_a_4270_, 11);
                v_diag_4286_ = lean_ctor_get_uint8(
                    v_a_4270_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4287_ = lean_ctor_get(v_a_4270_, 12);
                v_suppressElabErrors_4288_ = lean_ctor_get_uint8(
                    v_a_4270_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4289_ = lean_ctor_get(v_a_4270_, 13);
                v_ref_4290_ = l_Lean_replaceRef(v_stx_4265_, v_ref_4279_);
                lean_inc_ref(v_inheritedTraceOptions_4289_);
                lean_inc(v_cancelTk_x3f_4287_);
                lean_inc(v_currMacroScope_4285_);
                lean_inc(v_quotContext_4284_);
                lean_inc(v_maxHeartbeats_4283_);
                lean_inc(v_initHeartbeats_4282_);
                lean_inc(v_openDecls_4281_);
                lean_inc(v_currNamespace_4280_);
                lean_inc(v_maxRecDepth_4278_);
                lean_inc(v_currRecDepth_4277_);
                lean_inc_ref(v_options_4276_);
                lean_inc_ref(v_fileMap_4275_);
                lean_inc_ref(v_fileName_4274_);
                v___x_4291_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4291_, 0, v_fileName_4274_);
                lean_ctor_set(v___x_4291_, 1, v_fileMap_4275_);
                lean_ctor_set(v___x_4291_, 2, v_options_4276_);
                lean_ctor_set(v___x_4291_, 3, v_currRecDepth_4277_);
                lean_ctor_set(v___x_4291_, 4, v_maxRecDepth_4278_);
                lean_ctor_set(v___x_4291_, 5, v_ref_4290_);
                lean_ctor_set(v___x_4291_, 6, v_currNamespace_4280_);
                lean_ctor_set(v___x_4291_, 7, v_openDecls_4281_);
                lean_ctor_set(v___x_4291_, 8, v_initHeartbeats_4282_);
                lean_ctor_set(v___x_4291_, 9, v_maxHeartbeats_4283_);
                lean_ctor_set(v___x_4291_, 10, v_quotContext_4284_);
                lean_ctor_set(v___x_4291_, 11, v_currMacroScope_4285_);
                lean_ctor_set(v___x_4291_, 12, v_cancelTk_x3f_4287_);
                lean_ctor_set(v___x_4291_, 13, v_inheritedTraceOptions_4289_);
                lean_ctor_set_uint8(
                    v___x_4291_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_4286_,
                );
                lean_ctor_set_uint8(
                    v___x_4291_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4288_,
                );
                lean_inc(v_a_4271_);
                lean_inc(v_a_4269_);
                lean_inc_ref(v_a_4268_);
                lean_inc(v_a_4267_);
                lean_inc_ref(v_a_4266_);
                v___x_4292_ = lean_apply_8(
                    v_evalTerm_4273_,
                    v_stx_4265_,
                    v_a_4266_,
                    v_a_4267_,
                    v_a_4268_,
                    v_a_4269_,
                    v___x_4291_,
                    v_a_4271_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4292_) == 0 {
                    v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
                    v_isSharedCheck_4301_ = (!lean_is_exclusive(v___x_4292_)) as u8;
                    if v_isSharedCheck_4301_ == 0 {
                        v___x_4295_ = v___x_4292_;
                        v_isShared_4296_ = v_isSharedCheck_4301_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4293_);
                        lean_dec(v___x_4292_);
                        v___x_4295_ = lean_box(0);
                        v_isShared_4296_ = v_isSharedCheck_4301_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4302_ = lean_ctor_get(v___x_4292_, 0);
                    v_isSharedCheck_4309_ = (!lean_is_exclusive(v___x_4292_)) as u8;
                    if v_isSharedCheck_4309_ == 0 {
                        v___x_4304_ = v___x_4292_;
                        v_isShared_4305_ = v_isSharedCheck_4309_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4302_);
                        lean_dec(v___x_4292_);
                        v___x_4304_ = lean_box(0);
                        v_isShared_4305_ = v_isSharedCheck_4309_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4297_ = lean_ctor_get(v_a_4293_, 0);
                lean_inc(v_fst_4297_);
                lean_dec(v_a_4293_);
                if v_isShared_4296_ == 0 {
                    lean_ctor_set(v___x_4295_, 0, v_fst_4297_);
                    v___x_4299_ = v___x_4295_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_fst_4297_);
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
                    v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
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
    mut v_inst_4310_: *mut LeanObject,
    mut v_stx_4311_: *mut LeanObject,
    mut v_a_4312_: *mut LeanObject,
    mut v_a_4313_: *mut LeanObject,
    mut v_a_4314_: *mut LeanObject,
    mut v_a_4315_: *mut LeanObject,
    mut v_a_4316_: *mut LeanObject,
    mut v_a_4317_: *mut LeanObject,
    mut v_a_4318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4319_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4317_);
    lean_dec_ref(v_a_4316_);
    lean_dec(v_a_4315_);
    lean_dec_ref(v_a_4314_);
    lean_dec(v_a_4313_);
    lean_dec_ref(v_a_4312_);
    return v_res_4319_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermWithRef(
    mut v_00_u03b1_4320_: *mut LeanObject,
    mut v_inst_4321_: *mut LeanObject,
    mut v_stx_4322_: *mut LeanObject,
    mut v_a_4323_: *mut LeanObject,
    mut v_a_4324_: *mut LeanObject,
    mut v_a_4325_: *mut LeanObject,
    mut v_a_4326_: *mut LeanObject,
    mut v_a_4327_: *mut LeanObject,
    mut v_a_4328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4331_: *mut LeanObject,
    mut v_inst_4332_: *mut LeanObject,
    mut v_stx_4333_: *mut LeanObject,
    mut v_a_4334_: *mut LeanObject,
    mut v_a_4335_: *mut LeanObject,
    mut v_a_4336_: *mut LeanObject,
    mut v_a_4337_: *mut LeanObject,
    mut v_a_4338_: *mut LeanObject,
    mut v_a_4339_: *mut LeanObject,
    mut v_a_4340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4341_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4339_);
    lean_dec_ref(v_a_4338_);
    lean_dec(v_a_4337_);
    lean_dec_ref(v_a_4336_);
    lean_dec(v_a_4335_);
    lean_dec_ref(v_a_4334_);
    return v_res_4341_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0() -> *mut LeanObject
{
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    v___x_4342_ = l_instMonadEIO(lean_box(0));
    return v___x_4342_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1() -> *mut LeanObject
{
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    v___x_4343_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0,
    );
    v___x_4344_ = l_StateRefT_x27_instMonad___redArg(v___x_4343_);
    return v___x_4344_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10()
-> *mut LeanObject {
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4354_: *mut LeanObject = core::ptr::null_mut();
    v___x_4353_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_4354_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4354_, 0, v___x_4353_);
    return v___f_4354_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4356_: *mut LeanObject = core::ptr::null_mut();
    v___x_4355_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_4356_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4356_, 0, v___x_4355_);
    return v___f_4356_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12()
-> *mut LeanObject {
    let mut v___f_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    v___f_4357_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11,
    );
    v___f_4358_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10,
    );
    v___x_4359_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4359_, 0, v___f_4358_);
    lean_ctor_set(v___x_4359_, 1, v___f_4357_);
    return v___x_4359_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4361_: *mut LeanObject = core::ptr::null_mut();
    v___x_4360_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12,
    );
    v___f_4361_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4361_, 0, v___x_4360_);
    return v___f_4361_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14()
-> *mut LeanObject {
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4363_: *mut LeanObject = core::ptr::null_mut();
    v___x_4362_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12,
    );
    v___f_4363_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4363_, 0, v___x_4362_);
    return v___f_4363_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15()
-> *mut LeanObject {
    let mut v___f_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    v___f_4364_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14,
    );
    v___f_4365_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13,
    );
    v___x_4366_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4366_, 0, v___f_4365_);
    lean_ctor_set(v___x_4366_, 1, v___f_4364_);
    return v___x_4366_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16()
-> *mut LeanObject {
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4368_: *mut LeanObject = core::ptr::null_mut();
    v___x_4367_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15,
    );
    v___f_4368_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4368_, 0, v___x_4367_);
    return v___f_4368_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4370_: *mut LeanObject = core::ptr::null_mut();
    v___x_4369_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15,
    );
    v___f_4370_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4370_, 0, v___x_4369_);
    return v___f_4370_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18()
-> *mut LeanObject {
    let mut v___f_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    v___f_4371_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17,
    );
    v___f_4372_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16,
    );
    v___x_4373_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4373_, 0, v___f_4372_);
    lean_ctor_set(v___x_4373_, 1, v___f_4371_);
    return v___x_4373_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4375_: *mut LeanObject = core::ptr::null_mut();
    v___x_4374_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18,
    );
    v___f_4375_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_4375_, 0, v___x_4374_);
    return v___f_4375_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20()
-> *mut LeanObject {
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4377_: *mut LeanObject = core::ptr::null_mut();
    v___x_4376_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18,
    );
    v___f_4377_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_4377_, 0, v___x_4376_);
    return v___f_4377_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21()
-> *mut LeanObject {
    let mut v___f_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    v___f_4378_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20,
    );
    v___f_4379_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19,
    );
    v___x_4380_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4380_, 0, v___f_4379_);
    lean_ctor_set(v___x_4380_, 1, v___f_4378_);
    return v___x_4380_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22()
-> *mut LeanObject {
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    v___x_4381_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21,
    );
    v___x_4382_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_4381_);
    return v___x_4382_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24()
-> *mut LeanObject {
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    v___x_4384_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23;
    v___x_4385_ = l_Lean_stringToMessageData(v___x_4384_);
    return v___x_4385_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26()
-> *mut LeanObject {
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    v___x_4387_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25;
    v___x_4388_ = l_Lean_stringToMessageData(v___x_4387_);
    return v___x_4388_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28()
-> *mut LeanObject {
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    v___x_4390_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27;
    v___x_4391_ = l_Lean_stringToMessageData(v___x_4390_);
    return v___x_4391_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30()
-> *mut LeanObject {
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    v___x_4393_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29;
    v___x_4394_ = l_Lean_stringToMessageData(v___x_4393_);
    return v___x_4394_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32()
-> *mut LeanObject {
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    v___x_4396_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31;
    v___x_4397_ = l_Lean_stringToMessageData(v___x_4396_);
    return v___x_4397_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(
    mut v_inst_4398_: *mut LeanObject,
    mut v_stx_4399_: *mut LeanObject,
    mut v_a_4400_: *mut LeanObject,
    mut v_a_4401_: *mut LeanObject,
    mut v_a_4402_: *mut LeanObject,
    mut v_a_4403_: *mut LeanObject,
    mut v_a_4404_: *mut LeanObject,
    mut v_a_4405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4427_: u8 = 0;
    let mut v_toFunctor_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4434_: u8 = 0;
    let mut v___f_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4451_: u8 = 0;
    let mut v_toFunctor_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4458_: u8 = 0;
    let mut v___f_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadQuotation_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getMCtx_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyMCtx_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_evalExpr_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4492_: u8 = 0;
    let mut v___x_4493_: u8 = 0;
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4510_: u8 = 0;
    let mut v_cancelTk_x3f_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4512_: u8 = 0;
    let mut v_inheritedTraceOptions_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: u8 = 0;
    let mut v_ref_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751__overap_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802__overap_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4548_: u8 = 0;
    let mut v_id_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4552_: u8 = 0;
    let mut v___x_4553_: u8 = 0;
    let mut v_val_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4563_: u8 = 0;
    let mut v_unused_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: u8 = 0;
    let mut v___x_4576_: u8 = 0;
    let mut v___y_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: u8 = 0;
    let mut v___x_4071__overap_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4594_: u8 = 0;
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4598_: u8 = 0;
    let mut v_a_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4602_: u8 = 0;
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4606_: u8 = 0;
    let mut v_a_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4610_: u8 = 0;
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4614_: u8 = 0;
    let mut v___y_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938__overap_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4630_: u8 = 0;
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4634_: u8 = 0;
    let mut v___x_4635_: u8 = 0;
    let mut v___x_4636_: u8 = 0;
    let mut v___x_3959__overap_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4642_: u8 = 0;
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4646_: u8 = 0;
    let mut v_a_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4650_: u8 = 0;
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4654_: u8 = 0;
    let mut v_a_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4658_: u8 = 0;
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_isSharedCheck_4663_: u8 = 0;
    let mut v_reuseFailAlloc_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4666_: u8 = 0;
    let mut v_unused_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4668_: u8 = 0;
    let mut v_unused_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4672_: u8 = 0;
    let mut v_unused_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4674_: u8 = 0;
    let mut v_unused_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4407_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1,
                );
                v_toApplicative_4408_ = lean_ctor_get(v___x_4407_, 0);
                v_toFunctor_4409_ = lean_ctor_get(v_toApplicative_4408_, 0);
                v_toSeq_4410_ = lean_ctor_get(v_toApplicative_4408_, 2);
                v_toSeqLeft_4411_ = lean_ctor_get(v_toApplicative_4408_, 3);
                v_toSeqRight_4412_ = lean_ctor_get(v_toApplicative_4408_, 4);
                v___f_4413_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2;
                v___f_4414_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3;
                lean_inc_ref_n(v_toFunctor_4409_, 2);
                v___f_4415_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4415_, 0, v_toFunctor_4409_);
                v___f_4416_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4416_, 0, v_toFunctor_4409_);
                v___x_4417_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4417_, 0, v___f_4415_);
                lean_ctor_set(v___x_4417_, 1, v___f_4416_);
                lean_inc(v_toSeqRight_4412_);
                v___f_4418_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4418_, 0, v_toSeqRight_4412_);
                lean_inc(v_toSeqLeft_4411_);
                v___f_4419_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4419_, 0, v_toSeqLeft_4411_);
                lean_inc(v_toSeq_4410_);
                v___f_4420_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4420_, 0, v_toSeq_4410_);
                v___x_4421_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_4421_, 0, v___x_4417_);
                lean_ctor_set(v___x_4421_, 1, v___f_4413_);
                lean_ctor_set(v___x_4421_, 2, v___f_4420_);
                lean_ctor_set(v___x_4421_, 3, v___f_4419_);
                lean_ctor_set(v___x_4421_, 4, v___f_4418_);
                v___x_4422_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4422_, 0, v___x_4421_);
                lean_ctor_set(v___x_4422_, 1, v___f_4414_);
                v___x_4423_ = l_StateRefT_x27_instMonad___redArg(v___x_4422_);
                v_toApplicative_4424_ = lean_ctor_get(v___x_4423_, 0);
                v_isSharedCheck_4674_ = (!lean_is_exclusive(v___x_4423_)) as u8;
                if v_isSharedCheck_4674_ == 0 {
                    v_unused_4675_ = lean_ctor_get(v___x_4423_, 1);
                    lean_dec(v_unused_4675_);
                    v___x_4426_ = v___x_4423_;
                    v_isShared_4427_ = v_isSharedCheck_4674_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4424_);
                    lean_dec(v___x_4423_);
                    v___x_4426_ = lean_box(0);
                    v_isShared_4427_ = v_isSharedCheck_4674_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4428_ = lean_ctor_get(v_toApplicative_4424_, 0);
                v_toSeq_4429_ = lean_ctor_get(v_toApplicative_4424_, 2);
                v_toSeqLeft_4430_ = lean_ctor_get(v_toApplicative_4424_, 3);
                v_toSeqRight_4431_ = lean_ctor_get(v_toApplicative_4424_, 4);
                v_isSharedCheck_4672_ = (!lean_is_exclusive(v_toApplicative_4424_)) as u8;
                if v_isSharedCheck_4672_ == 0 {
                    v_unused_4673_ = lean_ctor_get(v_toApplicative_4424_, 1);
                    lean_dec(v_unused_4673_);
                    v___x_4433_ = v_toApplicative_4424_;
                    v_isShared_4434_ = v_isSharedCheck_4672_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4431_);
                    lean_inc(v_toSeqLeft_4430_);
                    lean_inc(v_toSeq_4429_);
                    lean_inc(v_toFunctor_4428_);
                    lean_dec(v_toApplicative_4424_);
                    v___x_4433_ = lean_box(0);
                    v_isShared_4434_ = v_isSharedCheck_4672_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4435_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4;
                v___f_4436_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5;
                lean_inc_ref(v_toFunctor_4428_);
                v___f_4437_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4437_, 0, v_toFunctor_4428_);
                v___f_4438_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4438_, 0, v_toFunctor_4428_);
                v___x_4439_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4439_, 0, v___f_4437_);
                lean_ctor_set(v___x_4439_, 1, v___f_4438_);
                v___f_4440_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4440_, 0, v_toSeqRight_4431_);
                v___f_4441_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4441_, 0, v_toSeqLeft_4430_);
                v___f_4442_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4442_, 0, v_toSeq_4429_);
                if v_isShared_4434_ == 0 {
                    lean_ctor_set(v___x_4433_, 4, v___f_4440_);
                    lean_ctor_set(v___x_4433_, 3, v___f_4441_);
                    lean_ctor_set(v___x_4433_, 2, v___f_4442_);
                    lean_ctor_set(v___x_4433_, 1, v___f_4435_);
                    lean_ctor_set(v___x_4433_, 0, v___x_4439_);
                    v___x_4444_ = v___x_4433_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4671_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4671_, 0, v___x_4439_);
                    lean_ctor_set(v_reuseFailAlloc_4671_, 1, v___f_4435_);
                    lean_ctor_set(v_reuseFailAlloc_4671_, 2, v___f_4442_);
                    lean_ctor_set(v_reuseFailAlloc_4671_, 3, v___f_4441_);
                    lean_ctor_set(v_reuseFailAlloc_4671_, 4, v___f_4440_);
                    v___x_4444_ = v_reuseFailAlloc_4671_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4427_ == 0 {
                    lean_ctor_set(v___x_4426_, 1, v___f_4436_);
                    lean_ctor_set(v___x_4426_, 0, v___x_4444_);
                    v___x_4446_ = v___x_4426_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4444_);
                    lean_ctor_set(v_reuseFailAlloc_4670_, 1, v___f_4436_);
                    v___x_4446_ = v_reuseFailAlloc_4670_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4447_ = l_StateRefT_x27_instMonad___redArg(v___x_4446_);
                v_toApplicative_4448_ = lean_ctor_get(v___x_4447_, 0);
                v_isSharedCheck_4668_ = (!lean_is_exclusive(v___x_4447_)) as u8;
                if v_isSharedCheck_4668_ == 0 {
                    v_unused_4669_ = lean_ctor_get(v___x_4447_, 1);
                    lean_dec(v_unused_4669_);
                    v___x_4450_ = v___x_4447_;
                    v_isShared_4451_ = v_isSharedCheck_4668_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4448_);
                    lean_dec(v___x_4447_);
                    v___x_4450_ = lean_box(0);
                    v_isShared_4451_ = v_isSharedCheck_4668_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4452_ = lean_ctor_get(v_toApplicative_4448_, 0);
                v_toSeq_4453_ = lean_ctor_get(v_toApplicative_4448_, 2);
                v_toSeqLeft_4454_ = lean_ctor_get(v_toApplicative_4448_, 3);
                v_toSeqRight_4455_ = lean_ctor_get(v_toApplicative_4448_, 4);
                v_isSharedCheck_4666_ = (!lean_is_exclusive(v_toApplicative_4448_)) as u8;
                if v_isSharedCheck_4666_ == 0 {
                    v_unused_4667_ = lean_ctor_get(v_toApplicative_4448_, 1);
                    lean_dec(v_unused_4667_);
                    v___x_4457_ = v_toApplicative_4448_;
                    v_isShared_4458_ = v_isSharedCheck_4666_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4455_);
                    lean_inc(v_toSeqLeft_4454_);
                    lean_inc(v_toSeq_4453_);
                    lean_inc(v_toFunctor_4452_);
                    lean_dec(v_toApplicative_4448_);
                    v___x_4457_ = lean_box(0);
                    v_isShared_4458_ = v_isSharedCheck_4666_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4459_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6;
                v___f_4460_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7;
                lean_inc_ref(v_toFunctor_4452_);
                v___f_4461_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4461_, 0, v_toFunctor_4452_);
                v___f_4462_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4462_, 0, v_toFunctor_4452_);
                v___x_4463_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4463_, 0, v___f_4461_);
                lean_ctor_set(v___x_4463_, 1, v___f_4462_);
                v___f_4464_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4464_, 0, v_toSeqRight_4455_);
                v___f_4465_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4465_, 0, v_toSeqLeft_4454_);
                v___f_4466_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4466_, 0, v_toSeq_4453_);
                if v_isShared_4458_ == 0 {
                    lean_ctor_set(v___x_4457_, 4, v___f_4464_);
                    lean_ctor_set(v___x_4457_, 3, v___f_4465_);
                    lean_ctor_set(v___x_4457_, 2, v___f_4466_);
                    lean_ctor_set(v___x_4457_, 1, v___f_4459_);
                    lean_ctor_set(v___x_4457_, 0, v___x_4463_);
                    v___x_4468_ = v___x_4457_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4463_);
                    lean_ctor_set(v_reuseFailAlloc_4665_, 1, v___f_4459_);
                    lean_ctor_set(v_reuseFailAlloc_4665_, 2, v___f_4466_);
                    lean_ctor_set(v_reuseFailAlloc_4665_, 3, v___f_4465_);
                    lean_ctor_set(v_reuseFailAlloc_4665_, 4, v___f_4464_);
                    v___x_4468_ = v_reuseFailAlloc_4665_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4451_ == 0 {
                    lean_ctor_set(v___x_4450_, 1, v___f_4460_);
                    lean_ctor_set(v___x_4450_, 0, v___x_4468_);
                    v___x_4470_ = v___x_4450_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4468_);
                    lean_ctor_set(v_reuseFailAlloc_4664_, 1, v___f_4460_);
                    v___x_4470_ = v_reuseFailAlloc_4664_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4471_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
                v_toMonadQuotation_4472_ = lean_ctor_get(v___x_4471_, 0);
                v_toMonadRef_4473_ = lean_ctor_get(v_toMonadQuotation_4472_, 0);
                v___x_4474_ = l_Lean_Meta_instMonadMCtxMetaM;
                v_getMCtx_4475_ = lean_ctor_get(v___x_4474_, 0);
                v_modifyMCtx_4476_ = lean_ctor_get(v___x_4474_, 1);
                v___f_4477_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8;
                v___x_4478_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9;
                lean_inc(v_modifyMCtx_4476_);
                v___f_4479_ = lean_alloc_closure(
                    l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_4479_, 0, v_modifyMCtx_4476_);
                lean_closure_set(v___f_4479_, 1, v___x_4478_);
                lean_inc(v_getMCtx_4475_);
                v___x_4480_ = lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___x_4480_, 0, lean_box(0));
                lean_closure_set(v___x_4480_, 1, lean_box(0));
                lean_closure_set(v___x_4480_, 2, lean_box(0));
                lean_closure_set(v___x_4480_, 3, lean_box(0));
                lean_closure_set(v___x_4480_, 4, v_getMCtx_4475_);
                v___f_4481_ = lean_alloc_closure(
                    l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_4481_, 0, v___f_4479_);
                lean_closure_set(v___f_4481_, 1, v___f_4477_);
                v___x_4482_ = lean_alloc_closure(
                    l_ReaderT_instMonadLift___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_4482_, 0, lean_box(0));
                lean_closure_set(v___x_4482_, 1, v___x_4480_);
                v___x_4483_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4483_, 0, v___x_4482_);
                lean_ctor_set(v___x_4483_, 1, v___f_4481_);
                v___x_4484_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21,
                );
                v___x_4485_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
                lean_inc_ref(v_toMonadRef_4473_);
                v___x_4486_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4486_, 0, v___x_4484_);
                lean_ctor_set(v___x_4486_, 1, v_toMonadRef_4473_);
                lean_ctor_set(v___x_4486_, 2, v___x_4485_);
                v___x_4487_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22,
                );
                v_evalExpr_4488_ = lean_ctor_get(v_inst_4398_, 0);
                v_expectedType_x3f_4489_ = lean_ctor_get(v_inst_4398_, 1);
                v_isSharedCheck_4663_ = (!lean_is_exclusive(v_inst_4398_)) as u8;
                if v_isSharedCheck_4663_ == 0 {
                    v___x_4491_ = v_inst_4398_;
                    v_isShared_4492_ = v_isSharedCheck_4663_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_expectedType_x3f_4489_);
                    lean_inc(v_evalExpr_4488_);
                    lean_dec(v_inst_4398_);
                    v___x_4491_ = lean_box(0);
                    v_isShared_4492_ = v_isSharedCheck_4663_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4493_ = 1;
                v___x_4494_ = lean_box(0);
                v___x_4495_ = lean_box((v___x_4493_) as usize);
                v___x_4496_ = lean_box((v___x_4493_) as usize);
                lean_inc(v_expectedType_x3f_4489_);
                lean_inc(v_stx_4399_);
                v___x_4497_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___x_4497_, 0, v_stx_4399_);
                lean_closure_set(v___x_4497_, 1, v_expectedType_x3f_4489_);
                lean_closure_set(v___x_4497_, 2, v___x_4495_);
                lean_closure_set(v___x_4497_, 3, v___x_4496_);
                lean_closure_set(v___x_4497_, 4, v___x_4494_);
                v_fileName_4498_ = lean_ctor_get(v_a_4404_, 0);
                v_fileMap_4499_ = lean_ctor_get(v_a_4404_, 1);
                v_options_4500_ = lean_ctor_get(v_a_4404_, 2);
                v_currRecDepth_4501_ = lean_ctor_get(v_a_4404_, 3);
                v_maxRecDepth_4502_ = lean_ctor_get(v_a_4404_, 4);
                v_ref_4503_ = lean_ctor_get(v_a_4404_, 5);
                v_currNamespace_4504_ = lean_ctor_get(v_a_4404_, 6);
                v_openDecls_4505_ = lean_ctor_get(v_a_4404_, 7);
                v_initHeartbeats_4506_ = lean_ctor_get(v_a_4404_, 8);
                v_maxHeartbeats_4507_ = lean_ctor_get(v_a_4404_, 9);
                v_quotContext_4508_ = lean_ctor_get(v_a_4404_, 10);
                v_currMacroScope_4509_ = lean_ctor_get(v_a_4404_, 11);
                v_diag_4510_ = lean_ctor_get_uint8(
                    v_a_4404_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4511_ = lean_ctor_get(v_a_4404_, 12);
                v_suppressElabErrors_4512_ = lean_ctor_get_uint8(
                    v_a_4404_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4513_ = lean_ctor_get(v_a_4404_, 13);
                v___x_4514_ = 1;
                v_ref_4515_ = l_Lean_replaceRef(v_stx_4399_, v_ref_4503_);
                lean_dec(v_stx_4399_);
                lean_inc_ref(v_inheritedTraceOptions_4513_);
                lean_inc(v_cancelTk_x3f_4511_);
                lean_inc(v_currMacroScope_4509_);
                lean_inc(v_quotContext_4508_);
                lean_inc(v_maxHeartbeats_4507_);
                lean_inc(v_initHeartbeats_4506_);
                lean_inc(v_openDecls_4505_);
                lean_inc(v_currNamespace_4504_);
                lean_inc(v_maxRecDepth_4502_);
                lean_inc(v_currRecDepth_4501_);
                lean_inc_ref(v_options_4500_);
                lean_inc_ref(v_fileMap_4499_);
                lean_inc_ref(v_fileName_4498_);
                v___x_4516_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4516_, 0, v_fileName_4498_);
                lean_ctor_set(v___x_4516_, 1, v_fileMap_4499_);
                lean_ctor_set(v___x_4516_, 2, v_options_4500_);
                lean_ctor_set(v___x_4516_, 3, v_currRecDepth_4501_);
                lean_ctor_set(v___x_4516_, 4, v_maxRecDepth_4502_);
                lean_ctor_set(v___x_4516_, 5, v_ref_4515_);
                lean_ctor_set(v___x_4516_, 6, v_currNamespace_4504_);
                lean_ctor_set(v___x_4516_, 7, v_openDecls_4505_);
                lean_ctor_set(v___x_4516_, 8, v_initHeartbeats_4506_);
                lean_ctor_set(v___x_4516_, 9, v_maxHeartbeats_4507_);
                lean_ctor_set(v___x_4516_, 10, v_quotContext_4508_);
                lean_ctor_set(v___x_4516_, 11, v_currMacroScope_4509_);
                lean_ctor_set(v___x_4516_, 12, v_cancelTk_x3f_4511_);
                lean_ctor_set(v___x_4516_, 13, v_inheritedTraceOptions_4513_);
                lean_ctor_set_uint8(
                    v___x_4516_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_4510_,
                );
                lean_ctor_set_uint8(
                    v___x_4516_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4512_,
                );
                v___x_4517_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_4497_,
                        v___x_4514_,
                        v_a_4400_,
                        v_a_4401_,
                        v_a_4402_,
                        v_a_4403_,
                        v___x_4516_,
                        v_a_4405_,
                    );
                if lean_obj_tag(v___x_4517_) == 0 {
                    v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
                    lean_inc(v_a_4518_);
                    lean_dec_ref_known(v___x_4517_, 1);
                    lean_inc_ref(v___x_4470_);
                    v___x_3751__overap_4519_ =
                        l_Lean_instantiateMVars___redArg(v___x_4470_, v___x_4483_, v_a_4518_);
                    lean_inc(v_a_4405_);
                    lean_inc_ref(v___x_4516_);
                    lean_inc(v_a_4403_);
                    lean_inc_ref(v_a_4402_);
                    lean_inc(v_a_4401_);
                    lean_inc_ref(v_a_4400_);
                    v___x_4520_ = lean_apply_7(
                        v___x_3751__overap_4519_,
                        v_a_4400_,
                        v_a_4401_,
                        v_a_4402_,
                        v_a_4403_,
                        v___x_4516_,
                        v_a_4405_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4520_) == 0 {
                        v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
                        lean_inc(v_a_4521_);
                        lean_dec_ref_known(v___x_4520_, 1);
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
                                lean_inc(v_a_4405_);
                                lean_inc_ref(v___x_4516_);
                                lean_inc(v_a_4403_);
                                lean_inc_ref(v_a_4402_);
                                lean_inc(v_a_4401_);
                                lean_inc_ref(v_a_4400_);
                                v___x_4638_ = lean_apply_7(
                                    v___x_3959__overap_4637_,
                                    v_a_4400_,
                                    v_a_4401_,
                                    v_a_4402_,
                                    v_a_4403_,
                                    v___x_4516_,
                                    v_a_4405_,
                                    lean_box(0),
                                );
                                if lean_obj_tag(v___x_4638_) == 0 {
                                    lean_dec_ref_known(v___x_4638_, 1);
                                    v___y_4616_ = v_a_4400_;
                                    v___y_4617_ = v_a_4401_;
                                    v___y_4618_ = v_a_4402_;
                                    v___y_4619_ = v_a_4403_;
                                    v___y_4620_ = v___x_4516_;
                                    v___y_4621_ = v_a_4405_;
                                    state = 23;
                                    continue;
                                } else {
                                    lean_dec(v_a_4521_);
                                    lean_dec_ref_known(v___x_4516_, 14);
                                    lean_del_object(v___x_4491_);
                                    lean_dec(v_expectedType_x3f_4489_);
                                    lean_dec_ref(v_evalExpr_4488_);
                                    lean_dec_ref_known(v___x_4486_, 3);
                                    lean_dec_ref(v___x_4470_);
                                    v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
                                    v_isSharedCheck_4646_ = (!lean_is_exclusive(v___x_4638_)) as u8;
                                    if v_isSharedCheck_4646_ == 0 {
                                        v___x_4641_ = v___x_4638_;
                                        v_isShared_4642_ = v_isSharedCheck_4646_;
                                        state = 26;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4639_);
                                        lean_dec(v___x_4638_);
                                        v___x_4641_ = lean_box(0);
                                        v_isShared_4642_ = v_isSharedCheck_4646_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref_known(v___x_4516_, 14);
                        lean_del_object(v___x_4491_);
                        lean_dec(v_expectedType_x3f_4489_);
                        lean_dec_ref(v_evalExpr_4488_);
                        lean_dec_ref_known(v___x_4486_, 3);
                        lean_dec_ref(v___x_4470_);
                        v_a_4647_ = lean_ctor_get(v___x_4520_, 0);
                        v_isSharedCheck_4654_ = (!lean_is_exclusive(v___x_4520_)) as u8;
                        if v_isSharedCheck_4654_ == 0 {
                            v___x_4649_ = v___x_4520_;
                            v_isShared_4650_ = v_isSharedCheck_4654_;
                            state = 28;
                            continue;
                        } else {
                            lean_inc(v_a_4647_);
                            lean_dec(v___x_4520_);
                            v___x_4649_ = lean_box(0);
                            v_isShared_4650_ = v_isSharedCheck_4654_;
                            state = 28;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_4516_, 14);
                    lean_del_object(v___x_4491_);
                    lean_dec(v_expectedType_x3f_4489_);
                    lean_dec_ref(v_evalExpr_4488_);
                    lean_dec_ref_known(v___x_4486_, 3);
                    lean_dec_ref_known(v___x_4483_, 2);
                    lean_dec_ref(v___x_4470_);
                    v_a_4655_ = lean_ctor_get(v___x_4517_, 0);
                    v_isSharedCheck_4662_ = (!lean_is_exclusive(v___x_4517_)) as u8;
                    if v_isSharedCheck_4662_ == 0 {
                        v___x_4657_ = v___x_4517_;
                        v_isShared_4658_ = v_isSharedCheck_4662_;
                        state = 30;
                        continue;
                    } else {
                        lean_inc(v_a_4655_);
                        lean_dec(v___x_4517_);
                        v___x_4657_ = lean_box(0);
                        v_isShared_4658_ = v_isSharedCheck_4662_;
                        state = 30;
                        continue;
                    }
                }
            }
            10 => {
                v___x_4530_ = lean_obj_once(
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
                    lean_ctor_set_tag(v___x_4491_, 7);
                    lean_ctor_set(v___x_4491_, 1, v___x_4531_);
                    lean_ctor_set(v___x_4491_, 0, v___x_4530_);
                    v___x_4533_ = v___x_4491_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4530_);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 1, v___x_4531_);
                    v___x_4533_ = v_reuseFailAlloc_4537_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4534_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4534_, 0, v___x_4533_);
                lean_ctor_set(v___x_4534_, 1, v___y_4529_);
                v___x_3802__overap_4535_ =
                    l_Lean_throwError___redArg(v___x_4470_, v___x_4486_, v___x_4534_);
                lean_inc(v___y_4525_);
                lean_inc(v___y_4526_);
                lean_inc_ref(v___y_4524_);
                lean_inc(v___y_4528_);
                lean_inc_ref(v___y_4527_);
                v___x_4536_ = lean_apply_7(
                    v___x_3802__overap_4535_,
                    v___y_4527_,
                    v___y_4528_,
                    v___y_4524_,
                    v___y_4526_,
                    v___y_4523_,
                    v___y_4525_,
                    lean_box(0),
                );
                return v___x_4536_;
            }
            12 => {
                if v___y_4548_ == 0 {
                    if lean_obj_tag(v___y_4539_) == 0 {
                        lean_dec_ref_known(v___y_4539_, 2);
                        lean_dec_ref(v___y_4541_);
                        lean_dec(v_a_4521_);
                        lean_del_object(v___x_4491_);
                        lean_dec(v_expectedType_x3f_4489_);
                        lean_dec_ref_known(v___x_4486_, 3);
                        lean_dec_ref(v___x_4470_);
                        return v___y_4542_;
                    } else {
                        v_id_4549_ = lean_ctor_get(v___y_4539_, 0);
                        v_isSharedCheck_4563_ = (!lean_is_exclusive(v___y_4539_)) as u8;
                        if v_isSharedCheck_4563_ == 0 {
                            v_unused_4564_ = lean_ctor_get(v___y_4539_, 1);
                            lean_dec(v_unused_4564_);
                            v___x_4551_ = v___y_4539_;
                            v_isShared_4552_ = v_isSharedCheck_4563_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_id_4549_);
                            lean_dec(v___y_4539_);
                            v___x_4551_ = lean_box(0);
                            v_isShared_4552_ = v_isSharedCheck_4563_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_4541_);
                    lean_dec_ref(v___y_4539_);
                    lean_dec(v_a_4521_);
                    lean_del_object(v___x_4491_);
                    lean_dec(v_expectedType_x3f_4489_);
                    lean_dec_ref_known(v___x_4486_, 3);
                    lean_dec_ref(v___x_4470_);
                    return v___y_4542_;
                }
            }
            13 => {
                v___x_4553_ = l_Lean_instBEqInternalExceptionId_beq(v___y_4543_, v_id_4549_);
                lean_dec(v_id_4549_);
                if v___x_4553_ == 0 {
                    lean_del_object(v___x_4551_);
                    lean_dec_ref(v___y_4541_);
                    lean_dec(v_a_4521_);
                    lean_del_object(v___x_4491_);
                    lean_dec(v_expectedType_x3f_4489_);
                    lean_dec_ref_known(v___x_4486_, 3);
                    lean_dec_ref(v___x_4470_);
                    return v___y_4542_;
                } else {
                    lean_dec_ref(v___y_4542_);
                    if lean_obj_tag(v_expectedType_x3f_4489_) == 1 {
                        v_val_4554_ = lean_ctor_get(v_expectedType_x3f_4489_, 0);
                        lean_inc(v_val_4554_);
                        lean_dec_ref_known(v_expectedType_x3f_4489_, 1);
                        v___x_4555_ = lean_obj_once(
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
                            lean_ctor_set_tag(v___x_4551_, 7);
                            lean_ctor_set(v___x_4551_, 1, v___x_4556_);
                            lean_ctor_set(v___x_4551_, 0, v___x_4555_);
                            v___x_4558_ = v___x_4551_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_4561_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4561_, 0, v___x_4555_);
                            lean_ctor_set(v_reuseFailAlloc_4561_, 1, v___x_4556_);
                            v___x_4558_ = v_reuseFailAlloc_4561_;
                            state = 14;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4551_);
                        lean_dec(v_expectedType_x3f_4489_);
                        v___x_4562_ = lean_obj_once(
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
                v___x_4559_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                );
                v___x_4560_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4560_, 0, v___x_4558_);
                lean_ctor_set(v___x_4560_, 1, v___x_4559_);
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
                lean_inc(v___y_4571_);
                lean_inc_ref(v___y_4570_);
                lean_inc(v___y_4569_);
                lean_inc_ref(v___y_4568_);
                lean_inc(v_a_4521_);
                v___x_4572_ = lean_apply_6(
                    v_evalExpr_4488_,
                    v_a_4521_,
                    v___y_4568_,
                    v___y_4569_,
                    v___y_4570_,
                    v___y_4571_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4572_) == 0 {
                    lean_dec_ref(v___y_4570_);
                    lean_dec(v_a_4521_);
                    lean_del_object(v___x_4491_);
                    lean_dec(v_expectedType_x3f_4489_);
                    lean_dec_ref_known(v___x_4486_, 3);
                    lean_dec_ref(v___x_4470_);
                    return v___x_4572_;
                } else {
                    v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
                    lean_inc(v_a_4573_);
                    v___x_4574_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_4575_ = l_Lean_Exception_isInterrupt(v_a_4573_);
                    if v___x_4575_ == 0 {
                        lean_inc(v_a_4573_);
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
                lean_inc(v_a_4521_);
                v___x_4584_ = l_Lean_Meta_getMVars(
                    v_a_4521_,
                    v___y_4580_,
                    v___y_4581_,
                    v___y_4582_,
                    v___y_4583_,
                );
                if lean_obj_tag(v___x_4584_) == 0 {
                    v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
                    lean_inc(v_a_4585_);
                    lean_dec_ref_known(v___x_4584_, 1);
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
                    lean_dec(v_a_4585_);
                    if lean_obj_tag(v___x_4586_) == 0 {
                        v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
                        lean_inc(v_a_4587_);
                        lean_dec_ref_known(v___x_4586_, 1);
                        v___x_4588_ = (lean_unbox(v_a_4587_) as u8);
                        lean_dec(v_a_4587_);
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
                            lean_inc(v___y_4583_);
                            lean_inc_ref(v___y_4582_);
                            lean_inc(v___y_4581_);
                            lean_inc_ref(v___y_4580_);
                            lean_inc(v___y_4579_);
                            lean_inc_ref(v___y_4578_);
                            v___x_4590_ = lean_apply_7(
                                v___x_4071__overap_4589_,
                                v___y_4578_,
                                v___y_4579_,
                                v___y_4580_,
                                v___y_4581_,
                                v___y_4582_,
                                v___y_4583_,
                                lean_box(0),
                            );
                            if lean_obj_tag(v___x_4590_) == 0 {
                                lean_dec_ref_known(v___x_4590_, 1);
                                v___y_4566_ = v___y_4578_;
                                v___y_4567_ = v___y_4579_;
                                v___y_4568_ = v___y_4580_;
                                v___y_4569_ = v___y_4581_;
                                v___y_4570_ = v___y_4582_;
                                v___y_4571_ = v___y_4583_;
                                state = 15;
                                continue;
                            } else {
                                lean_dec_ref(v___y_4582_);
                                lean_dec(v_a_4521_);
                                lean_del_object(v___x_4491_);
                                lean_dec(v_expectedType_x3f_4489_);
                                lean_dec_ref(v_evalExpr_4488_);
                                lean_dec_ref_known(v___x_4486_, 3);
                                lean_dec_ref(v___x_4470_);
                                v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
                                v_isSharedCheck_4598_ = (!lean_is_exclusive(v___x_4590_)) as u8;
                                if v_isSharedCheck_4598_ == 0 {
                                    v___x_4593_ = v___x_4590_;
                                    v_isShared_4594_ = v_isSharedCheck_4598_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_4591_);
                                    lean_dec(v___x_4590_);
                                    v___x_4593_ = lean_box(0);
                                    v_isShared_4594_ = v_isSharedCheck_4598_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_4582_);
                        lean_dec(v_a_4521_);
                        lean_del_object(v___x_4491_);
                        lean_dec(v_expectedType_x3f_4489_);
                        lean_dec_ref(v_evalExpr_4488_);
                        lean_dec_ref_known(v___x_4486_, 3);
                        lean_dec_ref(v___x_4470_);
                        v_a_4599_ = lean_ctor_get(v___x_4586_, 0);
                        v_isSharedCheck_4606_ = (!lean_is_exclusive(v___x_4586_)) as u8;
                        if v_isSharedCheck_4606_ == 0 {
                            v___x_4601_ = v___x_4586_;
                            v_isShared_4602_ = v_isSharedCheck_4606_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_4599_);
                            lean_dec(v___x_4586_);
                            v___x_4601_ = lean_box(0);
                            v_isShared_4602_ = v_isSharedCheck_4606_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_4582_);
                    lean_dec(v_a_4521_);
                    lean_del_object(v___x_4491_);
                    lean_dec(v_expectedType_x3f_4489_);
                    lean_dec_ref(v_evalExpr_4488_);
                    lean_dec_ref_known(v___x_4486_, 3);
                    lean_dec_ref(v___x_4470_);
                    v_a_4607_ = lean_ctor_get(v___x_4584_, 0);
                    v_isSharedCheck_4614_ = (!lean_is_exclusive(v___x_4584_)) as u8;
                    if v_isSharedCheck_4614_ == 0 {
                        v___x_4609_ = v___x_4584_;
                        v_isShared_4610_ = v_isSharedCheck_4614_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_4607_);
                        lean_dec(v___x_4584_);
                        v___x_4609_ = lean_box(0);
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
                    v_reuseFailAlloc_4597_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4591_);
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
                    v_reuseFailAlloc_4605_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
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
                    v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
                    v___x_4612_ = v_reuseFailAlloc_4613_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4612_;
            }
            23 => {
                v___x_4622_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32,
                );
                lean_inc(v_a_4521_);
                v___x_4623_ = l_Lean_indentExpr(v_a_4521_);
                v___x_4624_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4624_, 0, v___x_4622_);
                lean_ctor_set(v___x_4624_, 1, v___x_4623_);
                lean_inc_ref(v___x_4486_);
                lean_inc_ref(v___x_4470_);
                v___x_3938__overap_4625_ =
                    l_Lean_throwError___redArg(v___x_4470_, v___x_4486_, v___x_4624_);
                lean_inc(v___y_4621_);
                lean_inc_ref(v___y_4620_);
                lean_inc(v___y_4619_);
                lean_inc_ref(v___y_4618_);
                lean_inc(v___y_4617_);
                lean_inc_ref(v___y_4616_);
                v___x_4626_ = lean_apply_7(
                    v___x_3938__overap_4625_,
                    v___y_4616_,
                    v___y_4617_,
                    v___y_4618_,
                    v___y_4619_,
                    v___y_4620_,
                    v___y_4621_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4626_) == 0 {
                    lean_dec_ref_known(v___x_4626_, 1);
                    v___y_4578_ = v___y_4616_;
                    v___y_4579_ = v___y_4617_;
                    v___y_4580_ = v___y_4618_;
                    v___y_4581_ = v___y_4619_;
                    v___y_4582_ = v___y_4620_;
                    v___y_4583_ = v___y_4621_;
                    state = 16;
                    continue;
                } else {
                    lean_dec_ref(v___y_4620_);
                    lean_dec(v_a_4521_);
                    lean_del_object(v___x_4491_);
                    lean_dec(v_expectedType_x3f_4489_);
                    lean_dec_ref(v_evalExpr_4488_);
                    lean_dec_ref_known(v___x_4486_, 3);
                    lean_dec_ref(v___x_4470_);
                    v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
                    v_isSharedCheck_4634_ = (!lean_is_exclusive(v___x_4626_)) as u8;
                    if v_isSharedCheck_4634_ == 0 {
                        v___x_4629_ = v___x_4626_;
                        v_isShared_4630_ = v_isSharedCheck_4634_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_4627_);
                        lean_dec(v___x_4626_);
                        v___x_4629_ = lean_box(0);
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
                    v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4627_);
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
                    v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
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
                    v_reuseFailAlloc_4653_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
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
                    v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
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
    mut v_inst_4676_: *mut LeanObject,
    mut v_stx_4677_: *mut LeanObject,
    mut v_a_4678_: *mut LeanObject,
    mut v_a_4679_: *mut LeanObject,
    mut v_a_4680_: *mut LeanObject,
    mut v_a_4681_: *mut LeanObject,
    mut v_a_4682_: *mut LeanObject,
    mut v_a_4683_: *mut LeanObject,
    mut v_a_4684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4685_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4683_);
    lean_dec_ref(v_a_4682_);
    lean_dec(v_a_4681_);
    lean_dec_ref(v_a_4680_);
    lean_dec(v_a_4679_);
    lean_dec_ref(v_a_4678_);
    return v_res_4685_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab(
    mut v_00_u03b1_4686_: *mut LeanObject,
    mut v_inst_4687_: *mut LeanObject,
    mut v_stx_4688_: *mut LeanObject,
    mut v_a_4689_: *mut LeanObject,
    mut v_a_4690_: *mut LeanObject,
    mut v_a_4691_: *mut LeanObject,
    mut v_a_4692_: *mut LeanObject,
    mut v_a_4693_: *mut LeanObject,
    mut v_a_4694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4697_: *mut LeanObject,
    mut v_inst_4698_: *mut LeanObject,
    mut v_stx_4699_: *mut LeanObject,
    mut v_a_4700_: *mut LeanObject,
    mut v_a_4701_: *mut LeanObject,
    mut v_a_4702_: *mut LeanObject,
    mut v_a_4703_: *mut LeanObject,
    mut v_a_4704_: *mut LeanObject,
    mut v_a_4705_: *mut LeanObject,
    mut v_a_4706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4707_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4705_);
    lean_dec_ref(v_a_4704_);
    lean_dec(v_a_4703_);
    lean_dec_ref(v_a_4702_);
    lean_dec(v_a_4701_);
    lean_dec_ref(v_a_4700_);
    return v_res_4707_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(
    mut v_inst_4708_: *mut LeanObject,
    mut v_inst_4709_: *mut LeanObject,
    mut v_stx_4710_: *mut LeanObject,
    mut v_a_4711_: *mut LeanObject,
    mut v_a_4712_: *mut LeanObject,
    mut v_a_4713_: *mut LeanObject,
    mut v_a_4714_: *mut LeanObject,
    mut v_a_4715_: *mut LeanObject,
    mut v_a_4716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_evalTerm_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4731_: u8 = 0;
    let mut v_cancelTk_x3f_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4733_: u8 = 0;
    let mut v_inheritedTraceOptions_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4741_: u8 = 0;
    let mut v_fst_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4746_: u8 = 0;
    let mut v_a_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4750_: u8 = 0;
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4755_: u8 = 0;
    let mut v_id_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: u8 = 0;
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: u8 = 0;
    let mut v___x_4760_: u8 = 0;
    let mut v_reuseFailAlloc_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalTerm_4718_ = lean_ctor_get(v_inst_4708_, 0);
                lean_inc_ref(v_evalTerm_4718_);
                lean_dec_ref(v_inst_4708_);
                v_fileName_4719_ = lean_ctor_get(v_a_4715_, 0);
                v_fileMap_4720_ = lean_ctor_get(v_a_4715_, 1);
                v_options_4721_ = lean_ctor_get(v_a_4715_, 2);
                v_currRecDepth_4722_ = lean_ctor_get(v_a_4715_, 3);
                v_maxRecDepth_4723_ = lean_ctor_get(v_a_4715_, 4);
                v_ref_4724_ = lean_ctor_get(v_a_4715_, 5);
                v_currNamespace_4725_ = lean_ctor_get(v_a_4715_, 6);
                v_openDecls_4726_ = lean_ctor_get(v_a_4715_, 7);
                v_initHeartbeats_4727_ = lean_ctor_get(v_a_4715_, 8);
                v_maxHeartbeats_4728_ = lean_ctor_get(v_a_4715_, 9);
                v_quotContext_4729_ = lean_ctor_get(v_a_4715_, 10);
                v_currMacroScope_4730_ = lean_ctor_get(v_a_4715_, 11);
                v_diag_4731_ = lean_ctor_get_uint8(
                    v_a_4715_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4732_ = lean_ctor_get(v_a_4715_, 12);
                v_suppressElabErrors_4733_ = lean_ctor_get_uint8(
                    v_a_4715_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4734_ = lean_ctor_get(v_a_4715_, 13);
                v_ref_4735_ = l_Lean_replaceRef(v_stx_4710_, v_ref_4724_);
                lean_inc_ref(v_inheritedTraceOptions_4734_);
                lean_inc(v_cancelTk_x3f_4732_);
                lean_inc(v_currMacroScope_4730_);
                lean_inc(v_quotContext_4729_);
                lean_inc(v_maxHeartbeats_4728_);
                lean_inc(v_initHeartbeats_4727_);
                lean_inc(v_openDecls_4726_);
                lean_inc(v_currNamespace_4725_);
                lean_inc(v_maxRecDepth_4723_);
                lean_inc(v_currRecDepth_4722_);
                lean_inc_ref(v_options_4721_);
                lean_inc_ref(v_fileMap_4720_);
                lean_inc_ref(v_fileName_4719_);
                v___x_4736_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4736_, 0, v_fileName_4719_);
                lean_ctor_set(v___x_4736_, 1, v_fileMap_4720_);
                lean_ctor_set(v___x_4736_, 2, v_options_4721_);
                lean_ctor_set(v___x_4736_, 3, v_currRecDepth_4722_);
                lean_ctor_set(v___x_4736_, 4, v_maxRecDepth_4723_);
                lean_ctor_set(v___x_4736_, 5, v_ref_4735_);
                lean_ctor_set(v___x_4736_, 6, v_currNamespace_4725_);
                lean_ctor_set(v___x_4736_, 7, v_openDecls_4726_);
                lean_ctor_set(v___x_4736_, 8, v_initHeartbeats_4727_);
                lean_ctor_set(v___x_4736_, 9, v_maxHeartbeats_4728_);
                lean_ctor_set(v___x_4736_, 10, v_quotContext_4729_);
                lean_ctor_set(v___x_4736_, 11, v_currMacroScope_4730_);
                lean_ctor_set(v___x_4736_, 12, v_cancelTk_x3f_4732_);
                lean_ctor_set(v___x_4736_, 13, v_inheritedTraceOptions_4734_);
                lean_ctor_set_uint8(
                    v___x_4736_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_4731_,
                );
                lean_ctor_set_uint8(
                    v___x_4736_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4733_,
                );
                lean_inc(v_a_4716_);
                lean_inc_ref(v___x_4736_);
                lean_inc(v_a_4714_);
                lean_inc_ref(v_a_4713_);
                lean_inc(v_a_4712_);
                lean_inc_ref(v_a_4711_);
                lean_inc(v_stx_4710_);
                v___x_4737_ = lean_apply_8(
                    v_evalTerm_4718_,
                    v_stx_4710_,
                    v_a_4711_,
                    v_a_4712_,
                    v_a_4713_,
                    v_a_4714_,
                    v___x_4736_,
                    v_a_4716_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4737_) == 0 {
                    lean_dec_ref_known(v___x_4736_, 14);
                    lean_dec(v_stx_4710_);
                    lean_dec_ref(v_inst_4709_);
                    v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
                    v_isSharedCheck_4746_ = (!lean_is_exclusive(v___x_4737_)) as u8;
                    if v_isSharedCheck_4746_ == 0 {
                        v___x_4740_ = v___x_4737_;
                        v_isShared_4741_ = v_isSharedCheck_4746_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4738_);
                        lean_dec(v___x_4737_);
                        v___x_4740_ = lean_box(0);
                        v_isShared_4741_ = v_isSharedCheck_4746_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4747_ = lean_ctor_get(v___x_4737_, 0);
                    v_isSharedCheck_4762_ = (!lean_is_exclusive(v___x_4737_)) as u8;
                    if v_isSharedCheck_4762_ == 0 {
                        v___x_4749_ = v___x_4737_;
                        v_isShared_4750_ = v_isSharedCheck_4762_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4747_);
                        lean_dec(v___x_4737_);
                        v___x_4749_ = lean_box(0);
                        v_isShared_4750_ = v_isSharedCheck_4762_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4742_ = lean_ctor_get(v_a_4738_, 0);
                lean_inc(v_fst_4742_);
                lean_dec(v_a_4738_);
                if v_isShared_4741_ == 0 {
                    lean_ctor_set(v___x_4740_, 0, v_fst_4742_);
                    v___x_4744_ = v___x_4740_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_fst_4742_);
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
                lean_inc(v_a_4747_);
                if v_isShared_4750_ == 0 {
                    v___x_4753_ = v___x_4749_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4747_);
                    v___x_4753_ = v_reuseFailAlloc_4761_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4759_ = l_Lean_Exception_isInterrupt(v_a_4747_);
                if v___x_4759_ == 0 {
                    lean_inc(v_a_4747_);
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
                    if lean_obj_tag(v_a_4747_) == 0 {
                        lean_dec_ref_known(v_a_4747_, 2);
                        lean_dec_ref_known(v___x_4736_, 14);
                        lean_dec(v_stx_4710_);
                        lean_dec_ref(v_inst_4709_);
                        return v___x_4753_;
                    } else {
                        v_id_4756_ = lean_ctor_get(v_a_4747_, 0);
                        lean_inc(v_id_4756_);
                        lean_dec_ref_known(v_a_4747_, 2);
                        v___x_4757_ =
                            l_Lean_instBEqInternalExceptionId_beq(v___x_4751_, v_id_4756_);
                        lean_dec(v_id_4756_);
                        if v___x_4757_ == 0 {
                            lean_dec_ref_known(v___x_4736_, 14);
                            lean_dec(v_stx_4710_);
                            lean_dec_ref(v_inst_4709_);
                            return v___x_4753_;
                        } else {
                            lean_dec_ref(v___x_4753_);
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
                            lean_dec_ref_known(v___x_4736_, 14);
                            return v___x_4758_;
                        }
                    }
                } else {
                    lean_dec(v_a_4747_);
                    lean_dec_ref_known(v___x_4736_, 14);
                    lean_dec(v_stx_4710_);
                    lean_dec_ref(v_inst_4709_);
                    return v___x_4753_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg___boxed(
    mut v_inst_4763_: *mut LeanObject,
    mut v_inst_4764_: *mut LeanObject,
    mut v_stx_4765_: *mut LeanObject,
    mut v_a_4766_: *mut LeanObject,
    mut v_a_4767_: *mut LeanObject,
    mut v_a_4768_: *mut LeanObject,
    mut v_a_4769_: *mut LeanObject,
    mut v_a_4770_: *mut LeanObject,
    mut v_a_4771_: *mut LeanObject,
    mut v_a_4772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4773_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4771_);
    lean_dec_ref(v_a_4770_);
    lean_dec(v_a_4769_);
    lean_dec_ref(v_a_4768_);
    lean_dec(v_a_4767_);
    lean_dec_ref(v_a_4766_);
    return v_res_4773_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(
    mut v_00_u03b1_4774_: *mut LeanObject,
    mut v_inst_4775_: *mut LeanObject,
    mut v_inst_4776_: *mut LeanObject,
    mut v_stx_4777_: *mut LeanObject,
    mut v_a_4778_: *mut LeanObject,
    mut v_a_4779_: *mut LeanObject,
    mut v_a_4780_: *mut LeanObject,
    mut v_a_4781_: *mut LeanObject,
    mut v_a_4782_: *mut LeanObject,
    mut v_a_4783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4786_: *mut LeanObject,
    mut v_inst_4787_: *mut LeanObject,
    mut v_inst_4788_: *mut LeanObject,
    mut v_stx_4789_: *mut LeanObject,
    mut v_a_4790_: *mut LeanObject,
    mut v_a_4791_: *mut LeanObject,
    mut v_a_4792_: *mut LeanObject,
    mut v_a_4793_: *mut LeanObject,
    mut v_a_4794_: *mut LeanObject,
    mut v_a_4795_: *mut LeanObject,
    mut v_a_4796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4797_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4795_);
    lean_dec_ref(v_a_4794_);
    lean_dec(v_a_4793_);
    lean_dec_ref(v_a_4792_);
    lean_dec(v_a_4791_);
    lean_dec_ref(v_a_4790_);
    return v_res_4797_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
    mut v_x_4816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: u8 = 0;
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: u8 = 0;
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: u8 = 0;
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: u8 = 0;
    let mut v_t_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4817_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4;
                lean_inc(v_x_4816_);
                v___x_4818_ = l_Lean_Syntax_isOfKind(v_x_4816_, v___x_4817_);
                if v___x_4818_ == 0 {
                    return v_x_4816_;
                } else {
                    v___x_4819_ = lean_unsigned_to_nat(0);
                    v___x_4820_ = l_Lean_Syntax_getArg(v_x_4816_, v___x_4819_);
                    v___x_4821_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6;
                    lean_inc(v___x_4820_);
                    v___x_4822_ = l_Lean_Syntax_isOfKind(v___x_4820_, v___x_4821_);
                    if v___x_4822_ == 0 {
                        lean_dec(v___x_4820_);
                        return v_x_4816_;
                    } else {
                        v___x_4823_ = lean_unsigned_to_nat(1);
                        v___x_4824_ = l_Lean_Syntax_getArg(v___x_4820_, v___x_4823_);
                        lean_dec(v___x_4820_);
                        v___x_4825_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8;
                        lean_inc(v___x_4824_);
                        v___x_4826_ = l_Lean_Syntax_isOfKind(v___x_4824_, v___x_4825_);
                        if v___x_4826_ == 0 {
                            lean_dec(v___x_4824_);
                            return v_x_4816_;
                        } else {
                            v___x_4827_ = l_Lean_Syntax_getArg(v___x_4824_, v___x_4819_);
                            lean_dec(v___x_4824_);
                            v___x_4828_ = lean_box(0);
                            v___x_4829_ = l_Lean_Syntax_matchesIdent(v___x_4827_, v___x_4828_);
                            lean_dec(v___x_4827_);
                            if v___x_4829_ == 0 {
                                return v_x_4816_;
                            } else {
                                v_t_4830_ = l_Lean_Syntax_getArg(v_x_4816_, v___x_4823_);
                                lean_dec(v_x_4816_);
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
    mut v_expectedType_x3f_4832_: *mut LeanObject,
    mut v_f_4833_: *mut LeanObject,
    mut v_stx_4834_: *mut LeanObject,
    mut v_a_4835_: *mut LeanObject,
    mut v_a_4836_: *mut LeanObject,
    mut v_a_4837_: *mut LeanObject,
    mut v_a_4838_: *mut LeanObject,
    mut v_a_4839_: *mut LeanObject,
    mut v_a_4840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4854_: u8 = 0;
    let mut v_cancelTk_x3f_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4856_: u8 = 0;
    let mut v_inheritedTraceOptions_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4865_: u8 = 0;
    let mut v_snd_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_4869_: u8 = 0;
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: u8 = 0;
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4879_: u8 = 0;
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4883_: u8 = 0;
    let mut v_unused_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4888_: u8 = 0;
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4892_: u8 = 0;
    let mut v_isSharedCheck_4893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4842_ = lean_ctor_get(v_a_4839_, 0);
                v_fileMap_4843_ = lean_ctor_get(v_a_4839_, 1);
                v_options_4844_ = lean_ctor_get(v_a_4839_, 2);
                v_currRecDepth_4845_ = lean_ctor_get(v_a_4839_, 3);
                v_maxRecDepth_4846_ = lean_ctor_get(v_a_4839_, 4);
                v_ref_4847_ = lean_ctor_get(v_a_4839_, 5);
                v_currNamespace_4848_ = lean_ctor_get(v_a_4839_, 6);
                v_openDecls_4849_ = lean_ctor_get(v_a_4839_, 7);
                v_initHeartbeats_4850_ = lean_ctor_get(v_a_4839_, 8);
                v_maxHeartbeats_4851_ = lean_ctor_get(v_a_4839_, 9);
                v_quotContext_4852_ = lean_ctor_get(v_a_4839_, 10);
                v_currMacroScope_4853_ = lean_ctor_get(v_a_4839_, 11);
                v_diag_4854_ = lean_ctor_get_uint8(
                    v_a_4839_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4855_ = lean_ctor_get(v_a_4839_, 12);
                v_suppressElabErrors_4856_ = lean_ctor_get_uint8(
                    v_a_4839_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4857_ = lean_ctor_get(v_a_4839_, 13);
                lean_inc(v_stx_4834_);
                v___x_4858_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_4834_,
                    );
                v_ref_4859_ = l_Lean_replaceRef(v_stx_4834_, v_ref_4847_);
                lean_inc_ref(v_inheritedTraceOptions_4857_);
                lean_inc(v_cancelTk_x3f_4855_);
                lean_inc(v_currMacroScope_4853_);
                lean_inc(v_quotContext_4852_);
                lean_inc(v_maxHeartbeats_4851_);
                lean_inc(v_initHeartbeats_4850_);
                lean_inc(v_openDecls_4849_);
                lean_inc(v_currNamespace_4848_);
                lean_inc(v_maxRecDepth_4846_);
                lean_inc(v_currRecDepth_4845_);
                lean_inc_ref(v_options_4844_);
                lean_inc_ref(v_fileMap_4843_);
                lean_inc_ref(v_fileName_4842_);
                v___x_4860_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4860_, 0, v_fileName_4842_);
                lean_ctor_set(v___x_4860_, 1, v_fileMap_4843_);
                lean_ctor_set(v___x_4860_, 2, v_options_4844_);
                lean_ctor_set(v___x_4860_, 3, v_currRecDepth_4845_);
                lean_ctor_set(v___x_4860_, 4, v_maxRecDepth_4846_);
                lean_ctor_set(v___x_4860_, 5, v_ref_4859_);
                lean_ctor_set(v___x_4860_, 6, v_currNamespace_4848_);
                lean_ctor_set(v___x_4860_, 7, v_openDecls_4849_);
                lean_ctor_set(v___x_4860_, 8, v_initHeartbeats_4850_);
                lean_ctor_set(v___x_4860_, 9, v_maxHeartbeats_4851_);
                lean_ctor_set(v___x_4860_, 10, v_quotContext_4852_);
                lean_ctor_set(v___x_4860_, 11, v_currMacroScope_4853_);
                lean_ctor_set(v___x_4860_, 12, v_cancelTk_x3f_4855_);
                lean_ctor_set(v___x_4860_, 13, v_inheritedTraceOptions_4857_);
                lean_ctor_set_uint8(
                    v___x_4860_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_4854_,
                );
                lean_ctor_set_uint8(
                    v___x_4860_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4856_,
                );
                lean_inc(v_a_4840_);
                lean_inc(v_a_4838_);
                lean_inc_ref(v_a_4837_);
                lean_inc(v_a_4836_);
                lean_inc_ref(v_a_4835_);
                v___x_4861_ = lean_apply_8(
                    v_f_4833_,
                    v___x_4858_,
                    v_a_4835_,
                    v_a_4836_,
                    v_a_4837_,
                    v_a_4838_,
                    v___x_4860_,
                    v_a_4840_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4861_) == 0 {
                    v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
                    v_isSharedCheck_4893_ = (!lean_is_exclusive(v___x_4861_)) as u8;
                    if v_isSharedCheck_4893_ == 0 {
                        v___x_4864_ = v___x_4861_;
                        v_isShared_4865_ = v_isSharedCheck_4893_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4862_);
                        lean_dec(v___x_4861_);
                        v___x_4864_ = lean_box(0);
                        v_isShared_4865_ = v_isSharedCheck_4893_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_stx_4834_);
                    lean_dec(v_expectedType_x3f_4832_);
                    return v___x_4861_;
                }
            }
            1 => {
                v_snd_4866_ = lean_ctor_get(v_a_4862_, 1);
                v___x_4867_ = lean_st_ref_get(v_a_4840_);
                v_infoState_4868_ = lean_ctor_get(v___x_4867_, 7);
                lean_inc_ref(v_infoState_4868_);
                lean_dec(v___x_4867_);
                v_enabled_4869_ = lean_ctor_get_uint8(
                    v_infoState_4868_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_4868_);
                if v_enabled_4869_ == 0 {
                    lean_dec(v_stx_4834_);
                    lean_dec(v_expectedType_x3f_4832_);
                    if v_isShared_4865_ == 0 {
                        v___x_4871_ = v___x_4864_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4872_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4862_);
                        v___x_4871_ = v_reuseFailAlloc_4872_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4864_);
                    v___x_4873_ = lean_box(0);
                    v___x_4874_ = lean_box(0);
                    v___x_4875_ = 0;
                    lean_inc(v_snd_4866_);
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
                    if lean_obj_tag(v___x_4876_) == 0 {
                        v_isSharedCheck_4883_ = (!lean_is_exclusive(v___x_4876_)) as u8;
                        if v_isSharedCheck_4883_ == 0 {
                            v_unused_4884_ = lean_ctor_get(v___x_4876_, 0);
                            lean_dec(v_unused_4884_);
                            v___x_4878_ = v___x_4876_;
                            v_isShared_4879_ = v_isSharedCheck_4883_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_4876_);
                            v___x_4878_ = lean_box(0);
                            v_isShared_4879_ = v_isSharedCheck_4883_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4862_);
                        v_a_4885_ = lean_ctor_get(v___x_4876_, 0);
                        v_isSharedCheck_4892_ = (!lean_is_exclusive(v___x_4876_)) as u8;
                        if v_isSharedCheck_4892_ == 0 {
                            v___x_4887_ = v___x_4876_;
                            v_isShared_4888_ = v_isSharedCheck_4892_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4885_);
                            lean_dec(v___x_4876_);
                            v___x_4887_ = lean_box(0);
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
                    lean_ctor_set(v___x_4878_, 0, v_a_4862_);
                    v___x_4881_ = v___x_4878_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_a_4862_);
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
                    v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
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
    mut v_expectedType_x3f_4894_: *mut LeanObject,
    mut v_f_4895_: *mut LeanObject,
    mut v_stx_4896_: *mut LeanObject,
    mut v_a_4897_: *mut LeanObject,
    mut v_a_4898_: *mut LeanObject,
    mut v_a_4899_: *mut LeanObject,
    mut v_a_4900_: *mut LeanObject,
    mut v_a_4901_: *mut LeanObject,
    mut v_a_4902_: *mut LeanObject,
    mut v_a_4903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4904_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4902_);
    lean_dec_ref(v_a_4901_);
    lean_dec(v_a_4900_);
    lean_dec_ref(v_a_4899_);
    lean_dec(v_a_4898_);
    lean_dec_ref(v_a_4897_);
    return v_res_4904_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(
    mut v_00_u03b1_4905_: *mut LeanObject,
    mut v_expectedType_x3f_4906_: *mut LeanObject,
    mut v_f_4907_: *mut LeanObject,
    mut v_stx_4908_: *mut LeanObject,
    mut v_a_4909_: *mut LeanObject,
    mut v_a_4910_: *mut LeanObject,
    mut v_a_4911_: *mut LeanObject,
    mut v_a_4912_: *mut LeanObject,
    mut v_a_4913_: *mut LeanObject,
    mut v_a_4914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4928_: u8 = 0;
    let mut v_cancelTk_x3f_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4930_: u8 = 0;
    let mut v_inheritedTraceOptions_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4939_: u8 = 0;
    let mut v_snd_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_4943_: u8 = 0;
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: u8 = 0;
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4953_: u8 = 0;
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4957_: u8 = 0;
    let mut v_unused_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4962_: u8 = 0;
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4966_: u8 = 0;
    let mut v_isSharedCheck_4967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4916_ = lean_ctor_get(v_a_4913_, 0);
                v_fileMap_4917_ = lean_ctor_get(v_a_4913_, 1);
                v_options_4918_ = lean_ctor_get(v_a_4913_, 2);
                v_currRecDepth_4919_ = lean_ctor_get(v_a_4913_, 3);
                v_maxRecDepth_4920_ = lean_ctor_get(v_a_4913_, 4);
                v_ref_4921_ = lean_ctor_get(v_a_4913_, 5);
                v_currNamespace_4922_ = lean_ctor_get(v_a_4913_, 6);
                v_openDecls_4923_ = lean_ctor_get(v_a_4913_, 7);
                v_initHeartbeats_4924_ = lean_ctor_get(v_a_4913_, 8);
                v_maxHeartbeats_4925_ = lean_ctor_get(v_a_4913_, 9);
                v_quotContext_4926_ = lean_ctor_get(v_a_4913_, 10);
                v_currMacroScope_4927_ = lean_ctor_get(v_a_4913_, 11);
                v_diag_4928_ = lean_ctor_get_uint8(
                    v_a_4913_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4929_ = lean_ctor_get(v_a_4913_, 12);
                v_suppressElabErrors_4930_ = lean_ctor_get_uint8(
                    v_a_4913_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4931_ = lean_ctor_get(v_a_4913_, 13);
                lean_inc(v_stx_4908_);
                v___x_4932_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_4908_,
                    );
                v_ref_4933_ = l_Lean_replaceRef(v_stx_4908_, v_ref_4921_);
                lean_inc_ref(v_inheritedTraceOptions_4931_);
                lean_inc(v_cancelTk_x3f_4929_);
                lean_inc(v_currMacroScope_4927_);
                lean_inc(v_quotContext_4926_);
                lean_inc(v_maxHeartbeats_4925_);
                lean_inc(v_initHeartbeats_4924_);
                lean_inc(v_openDecls_4923_);
                lean_inc(v_currNamespace_4922_);
                lean_inc(v_maxRecDepth_4920_);
                lean_inc(v_currRecDepth_4919_);
                lean_inc_ref(v_options_4918_);
                lean_inc_ref(v_fileMap_4917_);
                lean_inc_ref(v_fileName_4916_);
                v___x_4934_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4934_, 0, v_fileName_4916_);
                lean_ctor_set(v___x_4934_, 1, v_fileMap_4917_);
                lean_ctor_set(v___x_4934_, 2, v_options_4918_);
                lean_ctor_set(v___x_4934_, 3, v_currRecDepth_4919_);
                lean_ctor_set(v___x_4934_, 4, v_maxRecDepth_4920_);
                lean_ctor_set(v___x_4934_, 5, v_ref_4933_);
                lean_ctor_set(v___x_4934_, 6, v_currNamespace_4922_);
                lean_ctor_set(v___x_4934_, 7, v_openDecls_4923_);
                lean_ctor_set(v___x_4934_, 8, v_initHeartbeats_4924_);
                lean_ctor_set(v___x_4934_, 9, v_maxHeartbeats_4925_);
                lean_ctor_set(v___x_4934_, 10, v_quotContext_4926_);
                lean_ctor_set(v___x_4934_, 11, v_currMacroScope_4927_);
                lean_ctor_set(v___x_4934_, 12, v_cancelTk_x3f_4929_);
                lean_ctor_set(v___x_4934_, 13, v_inheritedTraceOptions_4931_);
                lean_ctor_set_uint8(
                    v___x_4934_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_4928_,
                );
                lean_ctor_set_uint8(
                    v___x_4934_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4930_,
                );
                lean_inc(v_a_4914_);
                lean_inc(v_a_4912_);
                lean_inc_ref(v_a_4911_);
                lean_inc(v_a_4910_);
                lean_inc_ref(v_a_4909_);
                v___x_4935_ = lean_apply_8(
                    v_f_4907_,
                    v___x_4932_,
                    v_a_4909_,
                    v_a_4910_,
                    v_a_4911_,
                    v_a_4912_,
                    v___x_4934_,
                    v_a_4914_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4935_) == 0 {
                    v_a_4936_ = lean_ctor_get(v___x_4935_, 0);
                    v_isSharedCheck_4967_ = (!lean_is_exclusive(v___x_4935_)) as u8;
                    if v_isSharedCheck_4967_ == 0 {
                        v___x_4938_ = v___x_4935_;
                        v_isShared_4939_ = v_isSharedCheck_4967_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4936_);
                        lean_dec(v___x_4935_);
                        v___x_4938_ = lean_box(0);
                        v_isShared_4939_ = v_isSharedCheck_4967_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_stx_4908_);
                    lean_dec(v_expectedType_x3f_4906_);
                    return v___x_4935_;
                }
            }
            1 => {
                v_snd_4940_ = lean_ctor_get(v_a_4936_, 1);
                v___x_4941_ = lean_st_ref_get(v_a_4914_);
                v_infoState_4942_ = lean_ctor_get(v___x_4941_, 7);
                lean_inc_ref(v_infoState_4942_);
                lean_dec(v___x_4941_);
                v_enabled_4943_ = lean_ctor_get_uint8(
                    v_infoState_4942_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_4942_);
                if v_enabled_4943_ == 0 {
                    lean_dec(v_stx_4908_);
                    lean_dec(v_expectedType_x3f_4906_);
                    if v_isShared_4939_ == 0 {
                        v___x_4945_ = v___x_4938_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4946_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4936_);
                        v___x_4945_ = v_reuseFailAlloc_4946_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4938_);
                    v___x_4947_ = lean_box(0);
                    v___x_4948_ = lean_box(0);
                    v___x_4949_ = 0;
                    lean_inc(v_snd_4940_);
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
                    if lean_obj_tag(v___x_4950_) == 0 {
                        v_isSharedCheck_4957_ = (!lean_is_exclusive(v___x_4950_)) as u8;
                        if v_isSharedCheck_4957_ == 0 {
                            v_unused_4958_ = lean_ctor_get(v___x_4950_, 0);
                            lean_dec(v_unused_4958_);
                            v___x_4952_ = v___x_4950_;
                            v_isShared_4953_ = v_isSharedCheck_4957_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_4950_);
                            v___x_4952_ = lean_box(0);
                            v_isShared_4953_ = v_isSharedCheck_4957_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4936_);
                        v_a_4959_ = lean_ctor_get(v___x_4950_, 0);
                        v_isSharedCheck_4966_ = (!lean_is_exclusive(v___x_4950_)) as u8;
                        if v_isSharedCheck_4966_ == 0 {
                            v___x_4961_ = v___x_4950_;
                            v_isShared_4962_ = v_isSharedCheck_4966_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4959_);
                            lean_dec(v___x_4950_);
                            v___x_4961_ = lean_box(0);
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
                    lean_ctor_set(v___x_4952_, 0, v_a_4936_);
                    v___x_4955_ = v___x_4952_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4956_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4936_);
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
                    v_reuseFailAlloc_4965_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
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
    mut v_00_u03b1_4968_: *mut LeanObject,
    mut v_expectedType_x3f_4969_: *mut LeanObject,
    mut v_f_4970_: *mut LeanObject,
    mut v_stx_4971_: *mut LeanObject,
    mut v_a_4972_: *mut LeanObject,
    mut v_a_4973_: *mut LeanObject,
    mut v_a_4974_: *mut LeanObject,
    mut v_a_4975_: *mut LeanObject,
    mut v_a_4976_: *mut LeanObject,
    mut v_a_4977_: *mut LeanObject,
    mut v_a_4978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4979_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4977_);
    lean_dec_ref(v_a_4976_);
    lean_dec(v_a_4975_);
    lean_dec_ref(v_a_4974_);
    lean_dec(v_a_4973_);
    lean_dec_ref(v_a_4972_);
    return v_res_4979_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(
    mut v_inst_4980_: *mut LeanObject,
    mut v_f_4981_: *mut LeanObject,
    mut v_stx_4982_: *mut LeanObject,
    mut v_a_4983_: *mut LeanObject,
    mut v_a_4984_: *mut LeanObject,
    mut v_a_4985_: *mut LeanObject,
    mut v_a_4986_: *mut LeanObject,
    mut v_a_4987_: *mut LeanObject,
    mut v_a_4988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toExpr_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4994_: u8 = 0;
    let mut v_fileName_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5007_: u8 = 0;
    let mut v_cancelTk_x3f_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5009_: u8 = 0;
    let mut v_inheritedTraceOptions_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5018_: u8 = 0;
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_5021_: u8 = 0;
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: u8 = 0;
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5039_: u8 = 0;
    let mut v_unused_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5044_: u8 = 0;
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5048_: u8 = 0;
    let mut v_reuseFailAlloc_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5050_: u8 = 0;
    let mut v_a_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5054_: u8 = 0;
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5058_: u8 = 0;
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toExpr_4990_ = lean_ctor_get(v_inst_4980_, 0);
                v_toTypeExpr_4991_ = lean_ctor_get(v_inst_4980_, 1);
                v_isSharedCheck_5059_ = (!lean_is_exclusive(v_inst_4980_)) as u8;
                if v_isSharedCheck_5059_ == 0 {
                    v___x_4993_ = v_inst_4980_;
                    v_isShared_4994_ = v_isSharedCheck_5059_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toTypeExpr_4991_);
                    lean_inc(v_toExpr_4990_);
                    lean_dec(v_inst_4980_);
                    v___x_4993_ = lean_box(0);
                    v_isShared_4994_ = v_isSharedCheck_5059_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileName_4995_ = lean_ctor_get(v_a_4987_, 0);
                v_fileMap_4996_ = lean_ctor_get(v_a_4987_, 1);
                v_options_4997_ = lean_ctor_get(v_a_4987_, 2);
                v_currRecDepth_4998_ = lean_ctor_get(v_a_4987_, 3);
                v_maxRecDepth_4999_ = lean_ctor_get(v_a_4987_, 4);
                v_ref_5000_ = lean_ctor_get(v_a_4987_, 5);
                v_currNamespace_5001_ = lean_ctor_get(v_a_4987_, 6);
                v_openDecls_5002_ = lean_ctor_get(v_a_4987_, 7);
                v_initHeartbeats_5003_ = lean_ctor_get(v_a_4987_, 8);
                v_maxHeartbeats_5004_ = lean_ctor_get(v_a_4987_, 9);
                v_quotContext_5005_ = lean_ctor_get(v_a_4987_, 10);
                v_currMacroScope_5006_ = lean_ctor_get(v_a_4987_, 11);
                v_diag_5007_ = lean_ctor_get_uint8(
                    v_a_4987_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5008_ = lean_ctor_get(v_a_4987_, 12);
                v_suppressElabErrors_5009_ = lean_ctor_get_uint8(
                    v_a_4987_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5010_ = lean_ctor_get(v_a_4987_, 13);
                lean_inc(v_stx_4982_);
                v___x_5011_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_4982_,
                    );
                v_ref_5012_ = l_Lean_replaceRef(v_stx_4982_, v_ref_5000_);
                lean_inc_ref(v_inheritedTraceOptions_5010_);
                lean_inc(v_cancelTk_x3f_5008_);
                lean_inc(v_currMacroScope_5006_);
                lean_inc(v_quotContext_5005_);
                lean_inc(v_maxHeartbeats_5004_);
                lean_inc(v_initHeartbeats_5003_);
                lean_inc(v_openDecls_5002_);
                lean_inc(v_currNamespace_5001_);
                lean_inc(v_maxRecDepth_4999_);
                lean_inc(v_currRecDepth_4998_);
                lean_inc_ref(v_options_4997_);
                lean_inc_ref(v_fileMap_4996_);
                lean_inc_ref(v_fileName_4995_);
                v___x_5013_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_5013_, 0, v_fileName_4995_);
                lean_ctor_set(v___x_5013_, 1, v_fileMap_4996_);
                lean_ctor_set(v___x_5013_, 2, v_options_4997_);
                lean_ctor_set(v___x_5013_, 3, v_currRecDepth_4998_);
                lean_ctor_set(v___x_5013_, 4, v_maxRecDepth_4999_);
                lean_ctor_set(v___x_5013_, 5, v_ref_5012_);
                lean_ctor_set(v___x_5013_, 6, v_currNamespace_5001_);
                lean_ctor_set(v___x_5013_, 7, v_openDecls_5002_);
                lean_ctor_set(v___x_5013_, 8, v_initHeartbeats_5003_);
                lean_ctor_set(v___x_5013_, 9, v_maxHeartbeats_5004_);
                lean_ctor_set(v___x_5013_, 10, v_quotContext_5005_);
                lean_ctor_set(v___x_5013_, 11, v_currMacroScope_5006_);
                lean_ctor_set(v___x_5013_, 12, v_cancelTk_x3f_5008_);
                lean_ctor_set(v___x_5013_, 13, v_inheritedTraceOptions_5010_);
                lean_ctor_set_uint8(
                    v___x_5013_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_5007_,
                );
                lean_ctor_set_uint8(
                    v___x_5013_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5009_,
                );
                lean_inc(v_a_4988_);
                lean_inc(v_a_4986_);
                lean_inc_ref(v_a_4985_);
                lean_inc(v_a_4984_);
                lean_inc_ref(v_a_4983_);
                v___x_5014_ = lean_apply_8(
                    v_f_4981_,
                    v___x_5011_,
                    v_a_4983_,
                    v_a_4984_,
                    v_a_4985_,
                    v_a_4986_,
                    v___x_5013_,
                    v_a_4988_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5014_) == 0 {
                    v_a_5015_ = lean_ctor_get(v___x_5014_, 0);
                    v_isSharedCheck_5050_ = (!lean_is_exclusive(v___x_5014_)) as u8;
                    if v_isSharedCheck_5050_ == 0 {
                        v___x_5017_ = v___x_5014_;
                        v_isShared_5018_ = v_isSharedCheck_5050_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5015_);
                        lean_dec(v___x_5014_);
                        v___x_5017_ = lean_box(0);
                        v_isShared_5018_ = v_isSharedCheck_5050_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4993_);
                    lean_dec_ref(v_toTypeExpr_4991_);
                    lean_dec_ref(v_toExpr_4990_);
                    lean_dec(v_stx_4982_);
                    v_a_5051_ = lean_ctor_get(v___x_5014_, 0);
                    v_isSharedCheck_5058_ = (!lean_is_exclusive(v___x_5014_)) as u8;
                    if v_isSharedCheck_5058_ == 0 {
                        v___x_5053_ = v___x_5014_;
                        v_isShared_5054_ = v_isSharedCheck_5058_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5051_);
                        lean_dec(v___x_5014_);
                        v___x_5053_ = lean_box(0);
                        v_isShared_5054_ = v_isSharedCheck_5058_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5019_ = lean_st_ref_get(v_a_4988_);
                v_infoState_5020_ = lean_ctor_get(v___x_5019_, 7);
                lean_inc_ref(v_infoState_5020_);
                lean_dec(v___x_5019_);
                v_enabled_5021_ = lean_ctor_get_uint8(
                    v_infoState_5020_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_5020_);
                lean_inc(v_a_5015_);
                v___x_5022_ = lean_apply_1(v_toExpr_4990_, v_a_5015_);
                lean_inc_ref(v___x_5022_);
                if v_isShared_4994_ == 0 {
                    lean_ctor_set(v___x_4993_, 1, v___x_5022_);
                    lean_ctor_set(v___x_4993_, 0, v_a_5015_);
                    v___x_5024_ = v___x_4993_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5049_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_a_5015_);
                    lean_ctor_set(v_reuseFailAlloc_5049_, 1, v___x_5022_);
                    v___x_5024_ = v_reuseFailAlloc_5049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_enabled_5021_ == 0 {
                    lean_dec_ref(v___x_5022_);
                    lean_dec_ref(v_toTypeExpr_4991_);
                    lean_dec(v_stx_4982_);
                    if v_isShared_5018_ == 0 {
                        lean_ctor_set(v___x_5017_, 0, v___x_5024_);
                        v___x_5026_ = v___x_5017_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
                        v___x_5026_ = v_reuseFailAlloc_5027_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5017_);
                    v___x_5028_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5028_, 0, v_toTypeExpr_4991_);
                    v___x_5029_ = lean_box(0);
                    v___x_5030_ = lean_box(0);
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
                    if lean_obj_tag(v___x_5032_) == 0 {
                        v_isSharedCheck_5039_ = (!lean_is_exclusive(v___x_5032_)) as u8;
                        if v_isSharedCheck_5039_ == 0 {
                            v_unused_5040_ = lean_ctor_get(v___x_5032_, 0);
                            lean_dec(v_unused_5040_);
                            v___x_5034_ = v___x_5032_;
                            v_isShared_5035_ = v_isSharedCheck_5039_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_5032_);
                            v___x_5034_ = lean_box(0);
                            v_isShared_5035_ = v_isSharedCheck_5039_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_5024_);
                        v_a_5041_ = lean_ctor_get(v___x_5032_, 0);
                        v_isSharedCheck_5048_ = (!lean_is_exclusive(v___x_5032_)) as u8;
                        if v_isSharedCheck_5048_ == 0 {
                            v___x_5043_ = v___x_5032_;
                            v_isShared_5044_ = v_isSharedCheck_5048_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5041_);
                            lean_dec(v___x_5032_);
                            v___x_5043_ = lean_box(0);
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
                    lean_ctor_set(v___x_5034_, 0, v___x_5024_);
                    v___x_5037_ = v___x_5034_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5038_, 0, v___x_5024_);
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
                    v_reuseFailAlloc_5047_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5041_);
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
                    v_reuseFailAlloc_5057_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_a_5051_);
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
    mut v_inst_5060_: *mut LeanObject,
    mut v_f_5061_: *mut LeanObject,
    mut v_stx_5062_: *mut LeanObject,
    mut v_a_5063_: *mut LeanObject,
    mut v_a_5064_: *mut LeanObject,
    mut v_a_5065_: *mut LeanObject,
    mut v_a_5066_: *mut LeanObject,
    mut v_a_5067_: *mut LeanObject,
    mut v_a_5068_: *mut LeanObject,
    mut v_a_5069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5070_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5068_);
    lean_dec_ref(v_a_5067_);
    lean_dec(v_a_5066_);
    lean_dec_ref(v_a_5065_);
    lean_dec(v_a_5064_);
    lean_dec_ref(v_a_5063_);
    return v_res_5070_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(
    mut v_00_u03b1_5071_: *mut LeanObject,
    mut v_inst_5072_: *mut LeanObject,
    mut v_f_5073_: *mut LeanObject,
    mut v_stx_5074_: *mut LeanObject,
    mut v_a_5075_: *mut LeanObject,
    mut v_a_5076_: *mut LeanObject,
    mut v_a_5077_: *mut LeanObject,
    mut v_a_5078_: *mut LeanObject,
    mut v_a_5079_: *mut LeanObject,
    mut v_a_5080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toExpr_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5086_: u8 = 0;
    let mut v_fileName_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5099_: u8 = 0;
    let mut v_cancelTk_x3f_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5101_: u8 = 0;
    let mut v_inheritedTraceOptions_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5110_: u8 = 0;
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_5113_: u8 = 0;
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: u8 = 0;
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5127_: u8 = 0;
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5131_: u8 = 0;
    let mut v_unused_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5140_: u8 = 0;
    let mut v_reuseFailAlloc_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5142_: u8 = 0;
    let mut v_a_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5150_: u8 = 0;
    let mut v_isSharedCheck_5151_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toExpr_5082_ = lean_ctor_get(v_inst_5072_, 0);
                v_toTypeExpr_5083_ = lean_ctor_get(v_inst_5072_, 1);
                v_isSharedCheck_5151_ = (!lean_is_exclusive(v_inst_5072_)) as u8;
                if v_isSharedCheck_5151_ == 0 {
                    v___x_5085_ = v_inst_5072_;
                    v_isShared_5086_ = v_isSharedCheck_5151_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toTypeExpr_5083_);
                    lean_inc(v_toExpr_5082_);
                    lean_dec(v_inst_5072_);
                    v___x_5085_ = lean_box(0);
                    v_isShared_5086_ = v_isSharedCheck_5151_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileName_5087_ = lean_ctor_get(v_a_5079_, 0);
                v_fileMap_5088_ = lean_ctor_get(v_a_5079_, 1);
                v_options_5089_ = lean_ctor_get(v_a_5079_, 2);
                v_currRecDepth_5090_ = lean_ctor_get(v_a_5079_, 3);
                v_maxRecDepth_5091_ = lean_ctor_get(v_a_5079_, 4);
                v_ref_5092_ = lean_ctor_get(v_a_5079_, 5);
                v_currNamespace_5093_ = lean_ctor_get(v_a_5079_, 6);
                v_openDecls_5094_ = lean_ctor_get(v_a_5079_, 7);
                v_initHeartbeats_5095_ = lean_ctor_get(v_a_5079_, 8);
                v_maxHeartbeats_5096_ = lean_ctor_get(v_a_5079_, 9);
                v_quotContext_5097_ = lean_ctor_get(v_a_5079_, 10);
                v_currMacroScope_5098_ = lean_ctor_get(v_a_5079_, 11);
                v_diag_5099_ = lean_ctor_get_uint8(
                    v_a_5079_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5100_ = lean_ctor_get(v_a_5079_, 12);
                v_suppressElabErrors_5101_ = lean_ctor_get_uint8(
                    v_a_5079_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5102_ = lean_ctor_get(v_a_5079_, 13);
                lean_inc(v_stx_5074_);
                v___x_5103_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_5074_,
                    );
                v_ref_5104_ = l_Lean_replaceRef(v_stx_5074_, v_ref_5092_);
                lean_inc_ref(v_inheritedTraceOptions_5102_);
                lean_inc(v_cancelTk_x3f_5100_);
                lean_inc(v_currMacroScope_5098_);
                lean_inc(v_quotContext_5097_);
                lean_inc(v_maxHeartbeats_5096_);
                lean_inc(v_initHeartbeats_5095_);
                lean_inc(v_openDecls_5094_);
                lean_inc(v_currNamespace_5093_);
                lean_inc(v_maxRecDepth_5091_);
                lean_inc(v_currRecDepth_5090_);
                lean_inc_ref(v_options_5089_);
                lean_inc_ref(v_fileMap_5088_);
                lean_inc_ref(v_fileName_5087_);
                v___x_5105_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_5105_, 0, v_fileName_5087_);
                lean_ctor_set(v___x_5105_, 1, v_fileMap_5088_);
                lean_ctor_set(v___x_5105_, 2, v_options_5089_);
                lean_ctor_set(v___x_5105_, 3, v_currRecDepth_5090_);
                lean_ctor_set(v___x_5105_, 4, v_maxRecDepth_5091_);
                lean_ctor_set(v___x_5105_, 5, v_ref_5104_);
                lean_ctor_set(v___x_5105_, 6, v_currNamespace_5093_);
                lean_ctor_set(v___x_5105_, 7, v_openDecls_5094_);
                lean_ctor_set(v___x_5105_, 8, v_initHeartbeats_5095_);
                lean_ctor_set(v___x_5105_, 9, v_maxHeartbeats_5096_);
                lean_ctor_set(v___x_5105_, 10, v_quotContext_5097_);
                lean_ctor_set(v___x_5105_, 11, v_currMacroScope_5098_);
                lean_ctor_set(v___x_5105_, 12, v_cancelTk_x3f_5100_);
                lean_ctor_set(v___x_5105_, 13, v_inheritedTraceOptions_5102_);
                lean_ctor_set_uint8(
                    v___x_5105_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_5099_,
                );
                lean_ctor_set_uint8(
                    v___x_5105_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5101_,
                );
                lean_inc(v_a_5080_);
                lean_inc(v_a_5078_);
                lean_inc_ref(v_a_5077_);
                lean_inc(v_a_5076_);
                lean_inc_ref(v_a_5075_);
                v___x_5106_ = lean_apply_8(
                    v_f_5073_,
                    v___x_5103_,
                    v_a_5075_,
                    v_a_5076_,
                    v_a_5077_,
                    v_a_5078_,
                    v___x_5105_,
                    v_a_5080_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5106_) == 0 {
                    v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
                    v_isSharedCheck_5142_ = (!lean_is_exclusive(v___x_5106_)) as u8;
                    if v_isSharedCheck_5142_ == 0 {
                        v___x_5109_ = v___x_5106_;
                        v_isShared_5110_ = v_isSharedCheck_5142_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5107_);
                        lean_dec(v___x_5106_);
                        v___x_5109_ = lean_box(0);
                        v_isShared_5110_ = v_isSharedCheck_5142_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5085_);
                    lean_dec_ref(v_toTypeExpr_5083_);
                    lean_dec_ref(v_toExpr_5082_);
                    lean_dec(v_stx_5074_);
                    v_a_5143_ = lean_ctor_get(v___x_5106_, 0);
                    v_isSharedCheck_5150_ = (!lean_is_exclusive(v___x_5106_)) as u8;
                    if v_isSharedCheck_5150_ == 0 {
                        v___x_5145_ = v___x_5106_;
                        v_isShared_5146_ = v_isSharedCheck_5150_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5143_);
                        lean_dec(v___x_5106_);
                        v___x_5145_ = lean_box(0);
                        v_isShared_5146_ = v_isSharedCheck_5150_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5111_ = lean_st_ref_get(v_a_5080_);
                v_infoState_5112_ = lean_ctor_get(v___x_5111_, 7);
                lean_inc_ref(v_infoState_5112_);
                lean_dec(v___x_5111_);
                v_enabled_5113_ = lean_ctor_get_uint8(
                    v_infoState_5112_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_5112_);
                lean_inc(v_a_5107_);
                v___x_5114_ = lean_apply_1(v_toExpr_5082_, v_a_5107_);
                lean_inc_ref(v___x_5114_);
                if v_isShared_5086_ == 0 {
                    lean_ctor_set(v___x_5085_, 1, v___x_5114_);
                    lean_ctor_set(v___x_5085_, 0, v_a_5107_);
                    v___x_5116_ = v___x_5085_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5141_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5107_);
                    lean_ctor_set(v_reuseFailAlloc_5141_, 1, v___x_5114_);
                    v___x_5116_ = v_reuseFailAlloc_5141_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_enabled_5113_ == 0 {
                    lean_dec_ref(v___x_5114_);
                    lean_dec_ref(v_toTypeExpr_5083_);
                    lean_dec(v_stx_5074_);
                    if v_isShared_5110_ == 0 {
                        lean_ctor_set(v___x_5109_, 0, v___x_5116_);
                        v___x_5118_ = v___x_5109_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5119_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5119_, 0, v___x_5116_);
                        v___x_5118_ = v_reuseFailAlloc_5119_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5109_);
                    v___x_5120_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5120_, 0, v_toTypeExpr_5083_);
                    v___x_5121_ = lean_box(0);
                    v___x_5122_ = lean_box(0);
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
                    if lean_obj_tag(v___x_5124_) == 0 {
                        v_isSharedCheck_5131_ = (!lean_is_exclusive(v___x_5124_)) as u8;
                        if v_isSharedCheck_5131_ == 0 {
                            v_unused_5132_ = lean_ctor_get(v___x_5124_, 0);
                            lean_dec(v_unused_5132_);
                            v___x_5126_ = v___x_5124_;
                            v_isShared_5127_ = v_isSharedCheck_5131_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_5124_);
                            v___x_5126_ = lean_box(0);
                            v_isShared_5127_ = v_isSharedCheck_5131_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_5116_);
                        v_a_5133_ = lean_ctor_get(v___x_5124_, 0);
                        v_isSharedCheck_5140_ = (!lean_is_exclusive(v___x_5124_)) as u8;
                        if v_isSharedCheck_5140_ == 0 {
                            v___x_5135_ = v___x_5124_;
                            v_isShared_5136_ = v_isSharedCheck_5140_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5133_);
                            lean_dec(v___x_5124_);
                            v___x_5135_ = lean_box(0);
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
                    lean_ctor_set(v___x_5126_, 0, v___x_5116_);
                    v___x_5129_ = v___x_5126_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5130_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 0, v___x_5116_);
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
                    v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
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
                    v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
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
    mut v_00_u03b1_5152_: *mut LeanObject,
    mut v_inst_5153_: *mut LeanObject,
    mut v_f_5154_: *mut LeanObject,
    mut v_stx_5155_: *mut LeanObject,
    mut v_a_5156_: *mut LeanObject,
    mut v_a_5157_: *mut LeanObject,
    mut v_a_5158_: *mut LeanObject,
    mut v_a_5159_: *mut LeanObject,
    mut v_a_5160_: *mut LeanObject,
    mut v_a_5161_: *mut LeanObject,
    mut v_a_5162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5163_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5161_);
    lean_dec_ref(v_a_5160_);
    lean_dec(v_a_5159_);
    lean_dec_ref(v_a_5158_);
    lean_dec(v_a_5157_);
    lean_dec_ref(v_a_5156_);
    return v_res_5163_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(
    mut v_msgData_5164_: *mut LeanObject,
    mut v___y_5165_: *mut LeanObject,
    mut v___y_5166_: *mut LeanObject,
    mut v___y_5167_: *mut LeanObject,
    mut v___y_5168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    v___x_5170_ = lean_st_ref_get(v___y_5168_);
    v_env_5171_ = lean_ctor_get(v___x_5170_, 0);
    lean_inc_ref(v_env_5171_);
    lean_dec(v___x_5170_);
    v___x_5172_ = lean_st_ref_get(v___y_5166_);
    v_mctx_5173_ = lean_ctor_get(v___x_5172_, 0);
    lean_inc_ref(v_mctx_5173_);
    lean_dec(v___x_5172_);
    v_lctx_5174_ = lean_ctor_get(v___y_5165_, 2);
    v_options_5175_ = lean_ctor_get(v___y_5167_, 2);
    lean_inc_ref(v_options_5175_);
    lean_inc_ref(v_lctx_5174_);
    v___x_5176_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_5176_, 0, v_env_5171_);
    lean_ctor_set(v___x_5176_, 1, v_mctx_5173_);
    lean_ctor_set(v___x_5176_, 2, v_lctx_5174_);
    lean_ctor_set(v___x_5176_, 3, v_options_5175_);
    v___x_5177_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_5177_, 0, v___x_5176_);
    lean_ctor_set(v___x_5177_, 1, v_msgData_5164_);
    v___x_5178_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5178_, 0, v___x_5177_);
    return v___x_5178_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0___boxed(
    mut v_msgData_5179_: *mut LeanObject,
    mut v___y_5180_: *mut LeanObject,
    mut v___y_5181_: *mut LeanObject,
    mut v___y_5182_: *mut LeanObject,
    mut v___y_5183_: *mut LeanObject,
    mut v___y_5184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5185_: *mut LeanObject = core::ptr::null_mut();
    v_res_5185_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msgData_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
    lean_dec(v___y_5183_);
    lean_dec_ref(v___y_5182_);
    lean_dec(v___y_5181_);
    lean_dec_ref(v___y_5180_);
    return v_res_5185_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(
    mut v_msg_5186_: *mut LeanObject,
    mut v___y_5187_: *mut LeanObject,
    mut v___y_5188_: *mut LeanObject,
    mut v___y_5189_: *mut LeanObject,
    mut v___y_5190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5197_: u8 = 0;
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5192_ = lean_ctor_get(v___y_5189_, 5);
                v___x_5193_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
                v_a_5194_ = lean_ctor_get(v___x_5193_, 0);
                v_isSharedCheck_5202_ = (!lean_is_exclusive(v___x_5193_)) as u8;
                if v_isSharedCheck_5202_ == 0 {
                    v___x_5196_ = v___x_5193_;
                    v_isShared_5197_ = v_isSharedCheck_5202_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5194_);
                    lean_dec(v___x_5193_);
                    v___x_5196_ = lean_box(0);
                    v_isShared_5197_ = v_isSharedCheck_5202_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5192_);
                v___x_5198_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5198_, 0, v_ref_5192_);
                lean_ctor_set(v___x_5198_, 1, v_a_5194_);
                if v_isShared_5197_ == 0 {
                    lean_ctor_set_tag(v___x_5196_, 1);
                    lean_ctor_set(v___x_5196_, 0, v___x_5198_);
                    v___x_5200_ = v___x_5196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5201_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5201_, 0, v___x_5198_);
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
    mut v_msg_5203_: *mut LeanObject,
    mut v___y_5204_: *mut LeanObject,
    mut v___y_5205_: *mut LeanObject,
    mut v___y_5206_: *mut LeanObject,
    mut v___y_5207_: *mut LeanObject,
    mut v___y_5208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5209_: *mut LeanObject = core::ptr::null_mut();
    v_res_5209_ =
        l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(
            v_msg_5203_,
            v___y_5204_,
            v___y_5205_,
            v___y_5206_,
            v___y_5207_,
        );
    lean_dec(v___y_5207_);
    lean_dec_ref(v___y_5206_);
    lean_dec(v___y_5205_);
    lean_dec_ref(v___y_5204_);
    return v_res_5209_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    v___x_5211_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0;
    v___x_5212_ = l_Lean_stringToMessageData(v___x_5211_);
    return v___x_5212_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
    mut v_f_5213_: *mut LeanObject,
    mut v_e_5214_: *mut LeanObject,
    mut v_errMsg_5215_: *mut LeanObject,
    mut v_a_5216_: *mut LeanObject,
    mut v_a_5217_: *mut LeanObject,
    mut v_a_5218_: *mut LeanObject,
    mut v_a_5219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5227_: u8 = 0;
    let mut v_id_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5231_: u8 = 0;
    let mut v___x_5232_: u8 = 0;
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5240_: u8 = 0;
    let mut v_unused_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: u8 = 0;
    let mut v___x_5246_: u8 = 0;
    let mut v___y_5248_: u8 = 0;
    let mut v_id_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: u8 = 0;
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5258_: u8 = 0;
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5262_: u8 = 0;
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_f_5213_);
                lean_inc(v_a_5219_);
                lean_inc_ref(v_a_5218_);
                lean_inc(v_a_5217_);
                lean_inc_ref(v_a_5216_);
                lean_inc_ref(v_e_5214_);
                v___x_5221_ = lean_apply_6(
                    v_f_5213_,
                    v_e_5214_,
                    v_a_5216_,
                    v_a_5217_,
                    v_a_5218_,
                    v_a_5219_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5221_) == 0 {
                    lean_dec_ref(v_errMsg_5215_);
                    lean_dec_ref(v_e_5214_);
                    lean_dec_ref(v_f_5213_);
                    return v___x_5221_;
                } else {
                    v_a_5222_ = lean_ctor_get(v___x_5221_, 0);
                    lean_inc(v_a_5222_);
                    v___x_5223_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
                    v___x_5263_ = l_Lean_Exception_isInterrupt(v_a_5222_);
                    if v___x_5263_ == 0 {
                        lean_inc(v_a_5222_);
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
                    if lean_obj_tag(v___y_5226_) == 0 {
                        lean_dec_ref_known(v___y_5226_, 2);
                        lean_dec_ref(v_errMsg_5215_);
                        lean_dec_ref(v_e_5214_);
                        return v___y_5225_;
                    } else {
                        v_id_5228_ = lean_ctor_get(v___y_5226_, 0);
                        v_isSharedCheck_5240_ = (!lean_is_exclusive(v___y_5226_)) as u8;
                        if v_isSharedCheck_5240_ == 0 {
                            v_unused_5241_ = lean_ctor_get(v___y_5226_, 1);
                            lean_dec(v_unused_5241_);
                            v___x_5230_ = v___y_5226_;
                            v_isShared_5231_ = v_isSharedCheck_5240_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_id_5228_);
                            lean_dec(v___y_5226_);
                            v___x_5230_ = lean_box(0);
                            v_isShared_5231_ = v_isSharedCheck_5240_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_5226_);
                    lean_dec_ref(v_errMsg_5215_);
                    lean_dec_ref(v_e_5214_);
                    return v___y_5225_;
                }
            }
            2 => {
                v___x_5232_ = l_Lean_instBEqInternalExceptionId_beq(v___x_5223_, v_id_5228_);
                lean_dec(v_id_5228_);
                if v___x_5232_ == 0 {
                    lean_del_object(v___x_5230_);
                    lean_dec_ref(v_errMsg_5215_);
                    lean_dec_ref(v_e_5214_);
                    return v___y_5225_;
                } else {
                    lean_dec_ref(v___y_5225_);
                    v___x_5233_ = lean_obj_once(
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
                        lean_ctor_set_tag(v___x_5230_, 7);
                        lean_ctor_set(v___x_5230_, 1, v___x_5234_);
                        lean_ctor_set(v___x_5230_, 0, v___x_5233_);
                        v___x_5236_ = v___x_5230_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5239_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5233_);
                        lean_ctor_set(v_reuseFailAlloc_5239_, 1, v___x_5234_);
                        v___x_5236_ = v_reuseFailAlloc_5239_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5237_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5237_, 0, v___x_5236_);
                lean_ctor_set(v___x_5237_, 1, v_errMsg_5215_);
                v___x_5238_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v___x_5237_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_);
                return v___x_5238_;
            }
            4 => {
                v___x_5245_ = l_Lean_Exception_isInterrupt(v_a_5244_);
                if v___x_5245_ == 0 {
                    lean_inc_ref(v_a_5244_);
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
                    if lean_obj_tag(v_a_5222_) == 0 {
                        lean_dec_ref_known(v_a_5222_, 2);
                        lean_dec_ref(v_errMsg_5215_);
                        lean_dec_ref(v_e_5214_);
                        lean_dec_ref(v_f_5213_);
                        return v___x_5221_;
                    } else {
                        v_id_5249_ = lean_ctor_get(v_a_5222_, 0);
                        lean_inc(v_id_5249_);
                        lean_dec_ref_known(v_a_5222_, 2);
                        v___x_5250_ =
                            l_Lean_instBEqInternalExceptionId_beq(v___x_5223_, v_id_5249_);
                        lean_dec(v_id_5249_);
                        if v___x_5250_ == 0 {
                            lean_dec_ref(v_errMsg_5215_);
                            lean_dec_ref(v_e_5214_);
                            lean_dec_ref(v_f_5213_);
                            return v___x_5221_;
                        } else {
                            lean_dec_ref_known(v___x_5221_, 1);
                            lean_inc(v_a_5219_);
                            lean_inc_ref(v_a_5218_);
                            lean_inc(v_a_5217_);
                            lean_inc_ref(v_a_5216_);
                            lean_inc_ref(v_e_5214_);
                            v___x_5251_ =
                                lean_whnf(v_e_5214_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_);
                            if lean_obj_tag(v___x_5251_) == 0 {
                                v_a_5252_ = lean_ctor_get(v___x_5251_, 0);
                                lean_inc(v_a_5252_);
                                lean_dec_ref_known(v___x_5251_, 1);
                                lean_inc(v_a_5219_);
                                lean_inc_ref(v_a_5218_);
                                lean_inc(v_a_5217_);
                                lean_inc_ref(v_a_5216_);
                                v___x_5253_ = lean_apply_6(
                                    v_f_5213_,
                                    v_a_5252_,
                                    v_a_5216_,
                                    v_a_5217_,
                                    v_a_5218_,
                                    v_a_5219_,
                                    lean_box(0),
                                );
                                if lean_obj_tag(v___x_5253_) == 0 {
                                    lean_dec_ref(v_errMsg_5215_);
                                    lean_dec_ref(v_e_5214_);
                                    return v___x_5253_;
                                } else {
                                    v_a_5254_ = lean_ctor_get(v___x_5253_, 0);
                                    lean_inc(v_a_5254_);
                                    v___y_5243_ = v___x_5253_;
                                    v_a_5244_ = v_a_5254_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_f_5213_);
                                v_a_5255_ = lean_ctor_get(v___x_5251_, 0);
                                v_isSharedCheck_5262_ = (!lean_is_exclusive(v___x_5251_)) as u8;
                                if v_isSharedCheck_5262_ == 0 {
                                    v___x_5257_ = v___x_5251_;
                                    v_isShared_5258_ = v_isSharedCheck_5262_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_5255_);
                                    lean_dec(v___x_5251_);
                                    v___x_5257_ = lean_box(0);
                                    v_isShared_5258_ = v_isSharedCheck_5262_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_5222_);
                    lean_dec_ref(v_errMsg_5215_);
                    lean_dec_ref(v_e_5214_);
                    lean_dec_ref(v_f_5213_);
                    return v___x_5221_;
                }
            }
            6 => {
                lean_inc(v_a_5255_);
                if v_isShared_5258_ == 0 {
                    v___x_5260_ = v___x_5257_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5261_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
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
    mut v_f_5265_: *mut LeanObject,
    mut v_e_5266_: *mut LeanObject,
    mut v_errMsg_5267_: *mut LeanObject,
    mut v_a_5268_: *mut LeanObject,
    mut v_a_5269_: *mut LeanObject,
    mut v_a_5270_: *mut LeanObject,
    mut v_a_5271_: *mut LeanObject,
    mut v_a_5272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5273_: *mut LeanObject = core::ptr::null_mut();
    v_res_5273_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
        v_f_5265_,
        v_e_5266_,
        v_errMsg_5267_,
        v_a_5268_,
        v_a_5269_,
        v_a_5270_,
        v_a_5271_,
    );
    lean_dec(v_a_5271_);
    lean_dec_ref(v_a_5270_);
    lean_dec(v_a_5269_);
    lean_dec_ref(v_a_5268_);
    return v_res_5273_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(
    mut v_00_u03b1_5274_: *mut LeanObject,
    mut v_f_5275_: *mut LeanObject,
    mut v_e_5276_: *mut LeanObject,
    mut v_errMsg_5277_: *mut LeanObject,
    mut v_a_5278_: *mut LeanObject,
    mut v_a_5279_: *mut LeanObject,
    mut v_a_5280_: *mut LeanObject,
    mut v_a_5281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5284_: *mut LeanObject,
    mut v_f_5285_: *mut LeanObject,
    mut v_e_5286_: *mut LeanObject,
    mut v_errMsg_5287_: *mut LeanObject,
    mut v_a_5288_: *mut LeanObject,
    mut v_a_5289_: *mut LeanObject,
    mut v_a_5290_: *mut LeanObject,
    mut v_a_5291_: *mut LeanObject,
    mut v_a_5292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5293_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5291_);
    lean_dec_ref(v_a_5290_);
    lean_dec(v_a_5289_);
    lean_dec_ref(v_a_5288_);
    return v_res_5293_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(
    mut v_00_u03b1_5294_: *mut LeanObject,
    mut v_msg_5295_: *mut LeanObject,
    mut v___y_5296_: *mut LeanObject,
    mut v___y_5297_: *mut LeanObject,
    mut v___y_5298_: *mut LeanObject,
    mut v___y_5299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5302_: *mut LeanObject,
    mut v_msg_5303_: *mut LeanObject,
    mut v___y_5304_: *mut LeanObject,
    mut v___y_5305_: *mut LeanObject,
    mut v___y_5306_: *mut LeanObject,
    mut v___y_5307_: *mut LeanObject,
    mut v___y_5308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5309_: *mut LeanObject = core::ptr::null_mut();
    v_res_5309_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(
        v_00_u03b1_5302_,
        v_msg_5303_,
        v___y_5304_,
        v___y_5305_,
        v___y_5306_,
        v___y_5307_,
    );
    lean_dec(v___y_5307_);
    lean_dec_ref(v___y_5306_);
    lean_dec(v___y_5305_);
    lean_dec_ref(v___y_5304_);
    return v_res_5309_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
    mut v_item_5310_: *mut LeanObject,
) -> u8 {
    let mut v_optionComps_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: u8 = 0;
    v_optionComps_5311_ = lean_ctor_get(v_item_5310_, 5);
    v___x_5312_ = l_List_isEmpty___redArg(v_optionComps_5311_);
    return v___x_5312_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous___boxed(
    mut v_item_5313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5314_: u8 = 0;
    let mut v_r_5315_: *mut LeanObject = core::ptr::null_mut();
    v_res_5314_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_5313_);
    lean_dec_ref(v_item_5313_);
    v_r_5315_ = lean_box((v_res_5314_) as usize);
    return v_r_5315_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_root(
    mut v_item_5316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_optionComps_5317_: *mut LeanObject = core::ptr::null_mut();
    v_optionComps_5317_ = lean_ctor_get(v_item_5316_, 5);
    if lean_obj_tag(v_optionComps_5317_) == 1 {
        let mut v_head_5318_: *mut LeanObject = core::ptr::null_mut();
        v_head_5318_ = lean_ctor_get(v_optionComps_5317_, 0);
        lean_inc(v_head_5318_);
        return v_head_5318_;
    } else {
        let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
        v___x_5319_ = lean_box(0);
        return v___x_5319_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_root___boxed(
    mut v_item_5320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5321_: *mut LeanObject = core::ptr::null_mut();
    v_res_5321_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_5320_);
    lean_dec_ref(v_item_5320_);
    return v_res_5321_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(
    mut v_item_5322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    v___x_5323_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_5322_);
    v___x_5324_ = l_Lean_Syntax_getId(v___x_5323_);
    lean_dec(v___x_5323_);
    if lean_obj_tag(v___x_5324_) == 1 {
        let mut v_str_5325_: *mut LeanObject = core::ptr::null_mut();
        v_str_5325_ = lean_ctor_get(v___x_5324_, 1);
        lean_inc_ref(v_str_5325_);
        lean_dec_ref_known(v___x_5324_, 2);
        return v_str_5325_;
    } else {
        let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_5324_);
        v___x_5326_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29;
        return v___x_5326_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_getRootStr___boxed(
    mut v_item_5327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5328_: *mut LeanObject = core::ptr::null_mut();
    v_res_5328_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_5327_);
    lean_dec_ref(v_item_5327_);
    return v_res_5328_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(
    mut v_item_5329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_prevOptionComps_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    v_prevOptionComps_5330_ = lean_ctor_get(v_item_5329_, 6);
    v___x_5331_ = lean_unsigned_to_nat(0);
    v___x_5332_ = l_List_get_x3fInternal___redArg(v_prevOptionComps_5330_, v___x_5331_);
    return v___x_5332_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f___boxed(
    mut v_item_5333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5334_: *mut LeanObject = core::ptr::null_mut();
    v_res_5334_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(v_item_5333_);
    lean_dec_ref(v_item_5333_);
    return v_res_5334_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(
    mut v_item_5335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_prevOptionComps_5336_: *mut LeanObject = core::ptr::null_mut();
    v_prevOptionComps_5336_ = lean_ctor_get(v_item_5335_, 6);
    if lean_obj_tag(v_prevOptionComps_5336_) == 1 {
        let mut v_head_5337_: *mut LeanObject = core::ptr::null_mut();
        v_head_5337_ = lean_ctor_get(v_prevOptionComps_5336_, 0);
        lean_inc(v_head_5337_);
        return v_head_5337_;
    } else {
        let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
        v___x_5338_ = lean_box(0);
        return v___x_5338_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_prevRoot___boxed(
    mut v_item_5339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5340_: *mut LeanObject = core::ptr::null_mut();
    v_res_5340_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(v_item_5339_);
    lean_dec_ref(v_item_5339_);
    return v_res_5340_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(
    mut v_x_5341_: *mut LeanObject,
    mut v_x_5342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5342_) == 0 {
                    return v_x_5341_;
                } else {
                    v_head_5343_ = lean_ctor_get(v_x_5342_, 0);
                    lean_inc(v_head_5343_);
                    v_tail_5344_ = lean_ctor_get(v_x_5342_, 1);
                    lean_inc(v_tail_5344_);
                    lean_dec_ref_known(v_x_5342_, 2);
                    v___x_5345_ = l_Lean_Name_appendCore(v_x_5341_, v_head_5343_);
                    lean_dec(v_x_5341_);
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
    mut v_a_5347_: *mut LeanObject,
    mut v_a_5348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5354_: u8 = 0;
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5347_) == 0 {
                    v___x_5349_ = l_List_reverse___redArg(v_a_5348_);
                    return v___x_5349_;
                } else {
                    v_head_5350_ = lean_ctor_get(v_a_5347_, 0);
                    v_tail_5351_ = lean_ctor_get(v_a_5347_, 1);
                    v_isSharedCheck_5360_ = (!lean_is_exclusive(v_a_5347_)) as u8;
                    if v_isSharedCheck_5360_ == 0 {
                        v___x_5353_ = v_a_5347_;
                        v_isShared_5354_ = v_isSharedCheck_5360_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5351_);
                        lean_inc(v_head_5350_);
                        lean_dec(v_a_5347_);
                        v___x_5353_ = lean_box(0);
                        v_isShared_5354_ = v_isSharedCheck_5360_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5355_ = l_Lean_Syntax_getId(v_head_5350_);
                lean_dec(v_head_5350_);
                if v_isShared_5354_ == 0 {
                    lean_ctor_set(v___x_5353_, 1, v_a_5348_);
                    lean_ctor_set(v___x_5353_, 0, v___x_5355_);
                    v___x_5357_ = v___x_5353_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5359_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5355_);
                    lean_ctor_set(v_reuseFailAlloc_5359_, 1, v_a_5348_);
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
    mut v_item_5361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_optionComps_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    v_optionComps_5362_ = lean_ctor_get(v_item_5361_, 5);
    lean_inc(v_optionComps_5362_);
    lean_dec_ref(v_item_5361_);
    v___x_5363_ = lean_box(0);
    v___x_5364_ = lean_box(0);
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
    mut v_item_5367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_option_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bool_x3f_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origOptionName_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_optionComps_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prevOptionComps_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5380_: u8 = 0;
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5385_: u8 = 0;
    let mut v_unused_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5368_ = lean_ctor_get(v_item_5367_, 0);
                lean_inc(v_ref_5368_);
                v_option_5369_ = lean_ctor_get(v_item_5367_, 1);
                lean_inc(v_option_5369_);
                v_value_5370_ = lean_ctor_get(v_item_5367_, 2);
                lean_inc(v_value_5370_);
                v_bool_x3f_5371_ = lean_ctor_get(v_item_5367_, 3);
                lean_inc(v_bool_x3f_5371_);
                v_origOptionName_5372_ = lean_ctor_get(v_item_5367_, 4);
                lean_inc(v_origOptionName_5372_);
                v_optionComps_5373_ = lean_ctor_get(v_item_5367_, 5);
                v_prevOptionComps_5374_ = lean_ctor_get(v_item_5367_, 6);
                lean_inc(v_prevOptionComps_5374_);
                if lean_obj_tag(v_optionComps_5373_) == 0 {
                    v___y_5376_ = v_optionComps_5373_;
                    state = 1;
                    continue;
                } else {
                    v_tail_5393_ = lean_ctor_get(v_optionComps_5373_, 1);
                    lean_inc(v_tail_5393_);
                    v___y_5376_ = v_tail_5393_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5377_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_5367_);
                v_isSharedCheck_5385_ = (!lean_is_exclusive(v_item_5367_)) as u8;
                if v_isSharedCheck_5385_ == 0 {
                    v_unused_5386_ = lean_ctor_get(v_item_5367_, 6);
                    lean_dec(v_unused_5386_);
                    v_unused_5387_ = lean_ctor_get(v_item_5367_, 5);
                    lean_dec(v_unused_5387_);
                    v_unused_5388_ = lean_ctor_get(v_item_5367_, 4);
                    lean_dec(v_unused_5388_);
                    v_unused_5389_ = lean_ctor_get(v_item_5367_, 3);
                    lean_dec(v_unused_5389_);
                    v_unused_5390_ = lean_ctor_get(v_item_5367_, 2);
                    lean_dec(v_unused_5390_);
                    v_unused_5391_ = lean_ctor_get(v_item_5367_, 1);
                    lean_dec(v_unused_5391_);
                    v_unused_5392_ = lean_ctor_get(v_item_5367_, 0);
                    lean_dec(v_unused_5392_);
                    v___x_5379_ = v_item_5367_;
                    v_isShared_5380_ = v_isSharedCheck_5385_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_item_5367_);
                    v___x_5379_ = lean_box(0);
                    v_isShared_5380_ = v_isSharedCheck_5385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5381_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5381_, 0, v___x_5377_);
                lean_ctor_set(v___x_5381_, 1, v_prevOptionComps_5374_);
                if v_isShared_5380_ == 0 {
                    lean_ctor_set(v___x_5379_, 6, v___x_5381_);
                    lean_ctor_set(v___x_5379_, 5, v___y_5376_);
                    v___x_5383_ = v___x_5379_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5384_ = lean_alloc_ctor(0, 7, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_ref_5368_);
                    lean_ctor_set(v_reuseFailAlloc_5384_, 1, v_option_5369_);
                    lean_ctor_set(v_reuseFailAlloc_5384_, 2, v_value_5370_);
                    lean_ctor_set(v_reuseFailAlloc_5384_, 3, v_bool_x3f_5371_);
                    lean_ctor_set(v_reuseFailAlloc_5384_, 4, v_origOptionName_5372_);
                    lean_ctor_set(v_reuseFailAlloc_5384_, 5, v___y_5376_);
                    lean_ctor_set(v_reuseFailAlloc_5384_, 6, v___x_5381_);
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
-> *mut LeanObject {
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    v___x_5394_ = lean_box(1);
    v___x_5395_ = l_Lean_MessageData_ofFormat(v___x_5394_);
    return v___x_5395_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    v___x_5399_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2;
    v___x_5400_ = l_Lean_MessageData_ofFormat(v___x_5399_);
    return v___x_5400_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(
    mut v_x_5401_: *mut LeanObject,
    mut v_x_5402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5407_: u8 = 0;
    let mut v_before_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5424_: u8 = 0;
    let mut v_unused_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5402_) == 0 {
                    return v_x_5401_;
                } else {
                    v_head_5403_ = lean_ctor_get(v_x_5402_, 0);
                    v_tail_5404_ = lean_ctor_get(v_x_5402_, 1);
                    v_isSharedCheck_5426_ = (!lean_is_exclusive(v_x_5402_)) as u8;
                    if v_isSharedCheck_5426_ == 0 {
                        v___x_5406_ = v_x_5402_;
                        v_isShared_5407_ = v_isSharedCheck_5426_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5404_);
                        lean_inc(v_head_5403_);
                        lean_dec(v_x_5402_);
                        v___x_5406_ = lean_box(0);
                        v_isShared_5407_ = v_isSharedCheck_5426_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_5408_ = lean_ctor_get(v_head_5403_, 0);
                v_isSharedCheck_5424_ = (!lean_is_exclusive(v_head_5403_)) as u8;
                if v_isSharedCheck_5424_ == 0 {
                    v_unused_5425_ = lean_ctor_get(v_head_5403_, 1);
                    lean_dec(v_unused_5425_);
                    v___x_5410_ = v_head_5403_;
                    v_isShared_5411_ = v_isSharedCheck_5424_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_5408_);
                    lean_dec(v_head_5403_);
                    v___x_5410_ = lean_box(0);
                    v_isShared_5411_ = v_isSharedCheck_5424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5412_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_5411_ == 0 {
                    lean_ctor_set_tag(v___x_5410_, 7);
                    lean_ctor_set(v___x_5410_, 1, v___x_5412_);
                    lean_ctor_set(v___x_5410_, 0, v_x_5401_);
                    v___x_5414_ = v___x_5410_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5423_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_x_5401_);
                    lean_ctor_set(v_reuseFailAlloc_5423_, 1, v___x_5412_);
                    v___x_5414_ = v_reuseFailAlloc_5423_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5415_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3);
                if v_isShared_5407_ == 0 {
                    lean_ctor_set_tag(v___x_5406_, 7);
                    lean_ctor_set(v___x_5406_, 1, v___x_5415_);
                    lean_ctor_set(v___x_5406_, 0, v___x_5414_);
                    v___x_5417_ = v___x_5406_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5422_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5422_, 0, v___x_5414_);
                    lean_ctor_set(v_reuseFailAlloc_5422_, 1, v___x_5415_);
                    v___x_5417_ = v_reuseFailAlloc_5422_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5418_ = l_Lean_MessageData_ofSyntax(v_before_5408_);
                v___x_5419_ = l_Lean_indentD(v___x_5418_);
                v___x_5420_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5420_, 0, v___x_5417_);
                lean_ctor_set(v___x_5420_, 1, v___x_5419_);
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
    mut v_opts_5427_: *mut LeanObject,
    mut v_opt_5428_: *mut LeanObject,
) -> u8 {
    let mut v_name_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    v_name_5429_ = lean_ctor_get(v_opt_5428_, 0);
    v_defValue_5430_ = lean_ctor_get(v_opt_5428_, 1);
    v_map_5431_ = lean_ctor_get(v_opts_5427_, 0);
    v___x_5432_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5431_,
            v_name_5429_,
        );
    if lean_obj_tag(v___x_5432_) == 0 {
        let mut v___x_5433_: u8 = 0;
        v___x_5433_ = (lean_unbox(v_defValue_5430_) as u8);
        return v___x_5433_;
    } else {
        let mut v_val_5434_: *mut LeanObject = core::ptr::null_mut();
        v_val_5434_ = lean_ctor_get(v___x_5432_, 0);
        lean_inc(v_val_5434_);
        lean_dec_ref_known(v___x_5432_, 1);
        if lean_obj_tag(v_val_5434_) == 1 {
            let mut v_v_5435_: u8 = 0;
            v_v_5435_ = lean_ctor_get_uint8(v_val_5434_, 0 as u32);
            lean_dec_ref_known(v_val_5434_, 0);
            return v_v_5435_;
        } else {
            let mut v___x_5436_: u8 = 0;
            lean_dec(v_val_5434_);
            v___x_5436_ = (lean_unbox(v_defValue_5430_) as u8);
            return v___x_5436_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_opts_5437_: *mut LeanObject,
    mut v_opt_5438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5439_: u8 = 0;
    let mut v_r_5440_: *mut LeanObject = core::ptr::null_mut();
    v_res_5439_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_opts_5437_, v_opt_5438_);
    lean_dec_ref(v_opt_5438_);
    lean_dec_ref(v_opts_5437_);
    v_r_5440_ = lean_box((v_res_5439_) as usize);
    return v_r_5440_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    v___x_5444_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1;
    v___x_5445_ = l_Lean_MessageData_ofFormat(v___x_5444_);
    return v___x_5445_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(
    mut v_msgData_5446_: *mut LeanObject,
    mut v_macroStack_5447_: *mut LeanObject,
    mut v___y_5448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: u8 = 0;
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5459_: u8 = 0;
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5471_: u8 = 0;
    let mut v_unused_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5450_ = lean_ctor_get(v___y_5448_, 2);
                v___x_5451_ = l_Lean_Elab_pp_macroStack;
                v___x_5452_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_options_5450_, v___x_5451_);
                if v___x_5452_ == 0 {
                    lean_dec(v_macroStack_5447_);
                    v___x_5453_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5453_, 0, v_msgData_5446_);
                    return v___x_5453_;
                } else {
                    if lean_obj_tag(v_macroStack_5447_) == 0 {
                        v___x_5454_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5454_, 0, v_msgData_5446_);
                        return v___x_5454_;
                    } else {
                        v_head_5455_ = lean_ctor_get(v_macroStack_5447_, 0);
                        lean_inc(v_head_5455_);
                        v_after_5456_ = lean_ctor_get(v_head_5455_, 1);
                        v_isSharedCheck_5471_ = (!lean_is_exclusive(v_head_5455_)) as u8;
                        if v_isSharedCheck_5471_ == 0 {
                            v_unused_5472_ = lean_ctor_get(v_head_5455_, 0);
                            lean_dec(v_unused_5472_);
                            v___x_5458_ = v_head_5455_;
                            v_isShared_5459_ = v_isSharedCheck_5471_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_5456_);
                            lean_dec(v_head_5455_);
                            v___x_5458_ = lean_box(0);
                            v_isShared_5459_ = v_isSharedCheck_5471_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5460_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_5459_ == 0 {
                    lean_ctor_set_tag(v___x_5458_, 7);
                    lean_ctor_set(v___x_5458_, 1, v___x_5460_);
                    lean_ctor_set(v___x_5458_, 0, v_msgData_5446_);
                    v___x_5462_ = v___x_5458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5470_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_msgData_5446_);
                    lean_ctor_set(v_reuseFailAlloc_5470_, 1, v___x_5460_);
                    v___x_5462_ = v_reuseFailAlloc_5470_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5463_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2);
                v___x_5464_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5464_, 0, v___x_5462_);
                lean_ctor_set(v___x_5464_, 1, v___x_5463_);
                v___x_5465_ = l_Lean_MessageData_ofSyntax(v_after_5456_);
                v___x_5466_ = l_Lean_indentD(v___x_5465_);
                v_msgData_5467_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_5467_, 0, v___x_5464_);
                lean_ctor_set(v_msgData_5467_, 1, v___x_5466_);
                v___x_5468_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(v_msgData_5467_, v_macroStack_5447_);
                v___x_5469_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5469_, 0, v___x_5468_);
                return v___x_5469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msgData_5473_: *mut LeanObject,
    mut v_macroStack_5474_: *mut LeanObject,
    mut v___y_5475_: *mut LeanObject,
    mut v___y_5476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5477_: *mut LeanObject = core::ptr::null_mut();
    v_res_5477_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_5473_, v_macroStack_5474_, v___y_5475_);
    lean_dec_ref(v___y_5475_);
    return v_res_5477_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(
    mut v_msg_5478_: *mut LeanObject,
    mut v___y_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
    mut v___y_5484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5495_: u8 = 0;
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5486_ = lean_ctor_get(v___y_5483_, 5);
                v___x_5487_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_5478_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_);
                v_a_5488_ = lean_ctor_get(v___x_5487_, 0);
                lean_inc(v_a_5488_);
                lean_dec_ref(v___x_5487_);
                v_macroStack_5489_ = lean_ctor_get(v___y_5479_, 1);
                v___x_5490_ = l_Lean_Elab_getBetterRef(v_ref_5486_, v_macroStack_5489_);
                lean_inc(v_macroStack_5489_);
                v___x_5491_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_a_5488_, v_macroStack_5489_, v___y_5483_);
                v_a_5492_ = lean_ctor_get(v___x_5491_, 0);
                v_isSharedCheck_5500_ = (!lean_is_exclusive(v___x_5491_)) as u8;
                if v_isSharedCheck_5500_ == 0 {
                    v___x_5494_ = v___x_5491_;
                    v_isShared_5495_ = v_isSharedCheck_5500_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5492_);
                    lean_dec(v___x_5491_);
                    v___x_5494_ = lean_box(0);
                    v_isShared_5495_ = v_isSharedCheck_5500_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5496_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5496_, 0, v___x_5490_);
                lean_ctor_set(v___x_5496_, 1, v_a_5492_);
                if v_isShared_5495_ == 0 {
                    lean_ctor_set_tag(v___x_5494_, 1);
                    lean_ctor_set(v___x_5494_, 0, v___x_5496_);
                    v___x_5498_ = v___x_5494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5499_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5499_, 0, v___x_5496_);
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
    mut v_msg_5501_: *mut LeanObject,
    mut v___y_5502_: *mut LeanObject,
    mut v___y_5503_: *mut LeanObject,
    mut v___y_5504_: *mut LeanObject,
    mut v___y_5505_: *mut LeanObject,
    mut v___y_5506_: *mut LeanObject,
    mut v___y_5507_: *mut LeanObject,
    mut v___y_5508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5509_: *mut LeanObject = core::ptr::null_mut();
    v_res_5509_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_);
    lean_dec(v___y_5507_);
    lean_dec_ref(v___y_5506_);
    lean_dec(v___y_5505_);
    lean_dec_ref(v___y_5504_);
    lean_dec(v___y_5503_);
    lean_dec_ref(v___y_5502_);
    return v_res_5509_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(
    mut v_ref_5510_: *mut LeanObject,
    mut v_msg_5511_: *mut LeanObject,
    mut v___y_5512_: *mut LeanObject,
    mut v___y_5513_: *mut LeanObject,
    mut v___y_5514_: *mut LeanObject,
    mut v___y_5515_: *mut LeanObject,
    mut v___y_5516_: *mut LeanObject,
    mut v___y_5517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5531_: u8 = 0;
    let mut v_cancelTk_x3f_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5533_: u8 = 0;
    let mut v_inheritedTraceOptions_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_5519_ = lean_ctor_get(v___y_5516_, 0);
    v_fileMap_5520_ = lean_ctor_get(v___y_5516_, 1);
    v_options_5521_ = lean_ctor_get(v___y_5516_, 2);
    v_currRecDepth_5522_ = lean_ctor_get(v___y_5516_, 3);
    v_maxRecDepth_5523_ = lean_ctor_get(v___y_5516_, 4);
    v_ref_5524_ = lean_ctor_get(v___y_5516_, 5);
    v_currNamespace_5525_ = lean_ctor_get(v___y_5516_, 6);
    v_openDecls_5526_ = lean_ctor_get(v___y_5516_, 7);
    v_initHeartbeats_5527_ = lean_ctor_get(v___y_5516_, 8);
    v_maxHeartbeats_5528_ = lean_ctor_get(v___y_5516_, 9);
    v_quotContext_5529_ = lean_ctor_get(v___y_5516_, 10);
    v_currMacroScope_5530_ = lean_ctor_get(v___y_5516_, 11);
    v_diag_5531_ = lean_ctor_get_uint8(
        v___y_5516_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5532_ = lean_ctor_get(v___y_5516_, 12);
    v_suppressElabErrors_5533_ = lean_ctor_get_uint8(
        v___y_5516_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5534_ = lean_ctor_get(v___y_5516_, 13);
    v_ref_5535_ = l_Lean_replaceRef(v_ref_5510_, v_ref_5524_);
    lean_inc_ref(v_inheritedTraceOptions_5534_);
    lean_inc(v_cancelTk_x3f_5532_);
    lean_inc(v_currMacroScope_5530_);
    lean_inc(v_quotContext_5529_);
    lean_inc(v_maxHeartbeats_5528_);
    lean_inc(v_initHeartbeats_5527_);
    lean_inc(v_openDecls_5526_);
    lean_inc(v_currNamespace_5525_);
    lean_inc(v_maxRecDepth_5523_);
    lean_inc(v_currRecDepth_5522_);
    lean_inc_ref(v_options_5521_);
    lean_inc_ref(v_fileMap_5520_);
    lean_inc_ref(v_fileName_5519_);
    v___x_5536_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_5536_, 0, v_fileName_5519_);
    lean_ctor_set(v___x_5536_, 1, v_fileMap_5520_);
    lean_ctor_set(v___x_5536_, 2, v_options_5521_);
    lean_ctor_set(v___x_5536_, 3, v_currRecDepth_5522_);
    lean_ctor_set(v___x_5536_, 4, v_maxRecDepth_5523_);
    lean_ctor_set(v___x_5536_, 5, v_ref_5535_);
    lean_ctor_set(v___x_5536_, 6, v_currNamespace_5525_);
    lean_ctor_set(v___x_5536_, 7, v_openDecls_5526_);
    lean_ctor_set(v___x_5536_, 8, v_initHeartbeats_5527_);
    lean_ctor_set(v___x_5536_, 9, v_maxHeartbeats_5528_);
    lean_ctor_set(v___x_5536_, 10, v_quotContext_5529_);
    lean_ctor_set(v___x_5536_, 11, v_currMacroScope_5530_);
    lean_ctor_set(v___x_5536_, 12, v_cancelTk_x3f_5532_);
    lean_ctor_set(v___x_5536_, 13, v_inheritedTraceOptions_5534_);
    lean_ctor_set_uint8(
        v___x_5536_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_5531_,
    );
    lean_ctor_set_uint8(
        v___x_5536_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5533_,
    );
    v___x_5537_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___x_5536_, v___y_5517_);
    lean_dec_ref_known(v___x_5536_, 14);
    return v___x_5537_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg___boxed(
    mut v_ref_5538_: *mut LeanObject,
    mut v_msg_5539_: *mut LeanObject,
    mut v___y_5540_: *mut LeanObject,
    mut v___y_5541_: *mut LeanObject,
    mut v___y_5542_: *mut LeanObject,
    mut v___y_5543_: *mut LeanObject,
    mut v___y_5544_: *mut LeanObject,
    mut v___y_5545_: *mut LeanObject,
    mut v___y_5546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5547_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5545_);
    lean_dec_ref(v___y_5544_);
    lean_dec(v___y_5543_);
    lean_dec_ref(v___y_5542_);
    lean_dec(v___y_5541_);
    lean_dec_ref(v___y_5540_);
    lean_dec(v_ref_5538_);
    return v_res_5547_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1() -> *mut LeanObject
{
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    v___x_5549_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0;
    v___x_5550_ = l_Lean_stringToMessageData(v___x_5549_);
    return v___x_5550_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3() -> *mut LeanObject
{
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    v___x_5552_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2;
    v___x_5553_ = l_Lean_stringToMessageData(v___x_5552_);
    return v___x_5553_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(
    mut v_item_5554_: *mut LeanObject,
    mut v_a_5555_: *mut LeanObject,
    mut v_a_5556_: *mut LeanObject,
    mut v_a_5557_: *mut LeanObject,
    mut v_a_5558_: *mut LeanObject,
    mut v_a_5559_: *mut LeanObject,
    mut v_a_5560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bool_x3f_5562_: *mut LeanObject = core::ptr::null_mut();
    v_bool_x3f_5562_ = lean_ctor_get(v_item_5554_, 3);
    if lean_obj_tag(v_bool_x3f_5562_) == 0 {
        let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_item_5554_);
        v___x_5563_ = lean_box(0);
        v___x_5564_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5564_, 0, v___x_5563_);
        return v___x_5564_;
    } else {
        let mut v_option_5565_: *mut LeanObject = core::ptr::null_mut();
        let mut v_origOptionName_5566_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
        v_option_5565_ = lean_ctor_get(v_item_5554_, 1);
        lean_inc(v_option_5565_);
        v_origOptionName_5566_ = lean_ctor_get(v_item_5554_, 4);
        lean_inc(v_origOptionName_5566_);
        lean_dec_ref(v_item_5554_);
        v___x_5567_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1_once
            ),
            _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1,
        );
        v___x_5568_ = l_Lean_MessageData_ofName(v_origOptionName_5566_);
        v___x_5569_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_5569_, 0, v___x_5567_);
        lean_ctor_set(v___x_5569_, 1, v___x_5568_);
        v___x_5570_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3_once
            ),
            _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3,
        );
        v___x_5571_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_5571_, 0, v___x_5569_);
        lean_ctor_set(v___x_5571_, 1, v___x_5570_);
        v___x_5572_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_5565_, v___x_5571_, v_a_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_);
        lean_dec(v_option_5565_);
        return v___x_5572_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___boxed(
    mut v_item_5573_: *mut LeanObject,
    mut v_a_5574_: *mut LeanObject,
    mut v_a_5575_: *mut LeanObject,
    mut v_a_5576_: *mut LeanObject,
    mut v_a_5577_: *mut LeanObject,
    mut v_a_5578_: *mut LeanObject,
    mut v_a_5579_: *mut LeanObject,
    mut v_a_5580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5581_: *mut LeanObject = core::ptr::null_mut();
    v_res_5581_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(
        v_item_5573_,
        v_a_5574_,
        v_a_5575_,
        v_a_5576_,
        v_a_5577_,
        v_a_5578_,
        v_a_5579_,
    );
    lean_dec(v_a_5579_);
    lean_dec_ref(v_a_5578_);
    lean_dec(v_a_5577_);
    lean_dec_ref(v_a_5576_);
    lean_dec(v_a_5575_);
    lean_dec_ref(v_a_5574_);
    return v_res_5581_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(
    mut v_00_u03b1_5582_: *mut LeanObject,
    mut v_ref_5583_: *mut LeanObject,
    mut v_msg_5584_: *mut LeanObject,
    mut v___y_5585_: *mut LeanObject,
    mut v___y_5586_: *mut LeanObject,
    mut v___y_5587_: *mut LeanObject,
    mut v___y_5588_: *mut LeanObject,
    mut v___y_5589_: *mut LeanObject,
    mut v___y_5590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5593_: *mut LeanObject,
    mut v_ref_5594_: *mut LeanObject,
    mut v_msg_5595_: *mut LeanObject,
    mut v___y_5596_: *mut LeanObject,
    mut v___y_5597_: *mut LeanObject,
    mut v___y_5598_: *mut LeanObject,
    mut v___y_5599_: *mut LeanObject,
    mut v___y_5600_: *mut LeanObject,
    mut v___y_5601_: *mut LeanObject,
    mut v___y_5602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5603_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5601_);
    lean_dec_ref(v___y_5600_);
    lean_dec(v___y_5599_);
    lean_dec_ref(v___y_5598_);
    lean_dec(v___y_5597_);
    lean_dec_ref(v___y_5596_);
    lean_dec(v_ref_5594_);
    return v_res_5603_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(
    mut v_00_u03b1_5604_: *mut LeanObject,
    mut v_msg_5605_: *mut LeanObject,
    mut v___y_5606_: *mut LeanObject,
    mut v___y_5607_: *mut LeanObject,
    mut v___y_5608_: *mut LeanObject,
    mut v___y_5609_: *mut LeanObject,
    mut v___y_5610_: *mut LeanObject,
    mut v___y_5611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    v___x_5613_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_);
    return v___x_5613_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___boxed(
    mut v_00_u03b1_5614_: *mut LeanObject,
    mut v_msg_5615_: *mut LeanObject,
    mut v___y_5616_: *mut LeanObject,
    mut v___y_5617_: *mut LeanObject,
    mut v___y_5618_: *mut LeanObject,
    mut v___y_5619_: *mut LeanObject,
    mut v___y_5620_: *mut LeanObject,
    mut v___y_5621_: *mut LeanObject,
    mut v___y_5622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5623_: *mut LeanObject = core::ptr::null_mut();
    v_res_5623_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(v_00_u03b1_5614_, v_msg_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
    lean_dec(v___y_5621_);
    lean_dec_ref(v___y_5620_);
    lean_dec(v___y_5619_);
    lean_dec_ref(v___y_5618_);
    lean_dec(v___y_5617_);
    lean_dec_ref(v___y_5616_);
    return v_res_5623_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(
    mut v_msgData_5624_: *mut LeanObject,
    mut v_macroStack_5625_: *mut LeanObject,
    mut v___y_5626_: *mut LeanObject,
    mut v___y_5627_: *mut LeanObject,
    mut v___y_5628_: *mut LeanObject,
    mut v___y_5629_: *mut LeanObject,
    mut v___y_5630_: *mut LeanObject,
    mut v___y_5631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    v___x_5633_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_5624_, v_macroStack_5625_, v___y_5630_);
    return v___x_5633_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_5634_: *mut LeanObject,
    mut v_macroStack_5635_: *mut LeanObject,
    mut v___y_5636_: *mut LeanObject,
    mut v___y_5637_: *mut LeanObject,
    mut v___y_5638_: *mut LeanObject,
    mut v___y_5639_: *mut LeanObject,
    mut v___y_5640_: *mut LeanObject,
    mut v___y_5641_: *mut LeanObject,
    mut v___y_5642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5643_: *mut LeanObject = core::ptr::null_mut();
    v_res_5643_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(v_msgData_5634_, v_macroStack_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_);
    lean_dec(v___y_5641_);
    lean_dec_ref(v___y_5640_);
    lean_dec(v___y_5639_);
    lean_dec_ref(v___y_5638_);
    lean_dec(v___y_5637_);
    lean_dec_ref(v___y_5636_);
    return v_res_5643_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    v___x_5645_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0;
    v___x_5646_ = l_Lean_stringToMessageData(v___x_5645_);
    return v___x_5646_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    v___x_5648_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2;
    v___x_5649_ = l_Lean_stringToMessageData(v___x_5648_);
    return v___x_5649_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut LeanObject = core::ptr::null_mut();
    v___x_5651_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4;
    v___x_5652_ = l_Lean_stringToMessageData(v___x_5651_);
    return v___x_5652_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(
    mut v_item_5653_: *mut LeanObject,
    mut v_structName_x3f_5654_: *mut LeanObject,
    mut v_a_5655_: *mut LeanObject,
    mut v_a_5656_: *mut LeanObject,
    mut v_a_5657_: *mut LeanObject,
    mut v_a_5658_: *mut LeanObject,
    mut v_a_5659_: *mut LeanObject,
    mut v_a_5660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_option_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origOptionName_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: u8 = 0;
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: u8 = 0;
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_option_5662_ = lean_ctor_get(v_item_5653_, 1);
                lean_inc(v_option_5662_);
                v_origOptionName_5663_ = lean_ctor_get(v_item_5653_, 4);
                lean_inc(v_origOptionName_5663_);
                lean_dec_ref(v_item_5653_);
                v___x_5681_ = l_Lean_Name_isAnonymous(v_origOptionName_5663_);
                if v___x_5681_ == 0 {
                    v___x_5682_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
                    v___x_5683_ = l_Lean_MessageData_ofName(v_origOptionName_5663_);
                    v___x_5684_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5684_, 0, v___x_5682_);
                    lean_ctor_set(v___x_5684_, 1, v___x_5683_);
                    v___x_5685_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                    );
                    v___x_5686_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5686_, 0, v___x_5684_);
                    lean_ctor_set(v___x_5686_, 1, v___x_5685_);
                    v___y_5672_ = v___x_5686_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_origOptionName_5663_);
                    v___x_5687_ = lean_obj_once(
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
                v___x_5667_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1);
                v___x_5668_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5668_, 0, v___x_5667_);
                lean_ctor_set(v___x_5668_, 1, v___y_5665_);
                v___x_5669_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5669_, 0, v___x_5668_);
                lean_ctor_set(v___x_5669_, 1, v___y_5666_);
                v___x_5670_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_5662_, v___x_5669_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_);
                lean_dec(v_option_5662_);
                return v___x_5670_;
            }
            2 => {
                if lean_obj_tag(v_structName_x3f_5654_) == 1 {
                    v_val_5673_ = lean_ctor_get(v_structName_x3f_5654_, 0);
                    lean_inc(v_val_5673_);
                    lean_dec_ref_known(v_structName_x3f_5654_, 1);
                    v___x_5674_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
                    v___x_5675_ = 0;
                    v___x_5676_ = l_Lean_MessageData_ofConstName(v_val_5673_, v___x_5675_);
                    v___x_5677_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5677_, 0, v___x_5674_);
                    lean_ctor_set(v___x_5677_, 1, v___x_5676_);
                    v___x_5678_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                    );
                    v___x_5679_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5679_, 0, v___x_5677_);
                    lean_ctor_set(v___x_5679_, 1, v___x_5678_);
                    v___y_5665_ = v___y_5672_;
                    v___y_5666_ = v___x_5679_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_structName_x3f_5654_);
                    v___x_5680_ = lean_obj_once(
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
    mut v_item_5688_: *mut LeanObject,
    mut v_structName_x3f_5689_: *mut LeanObject,
    mut v_a_5690_: *mut LeanObject,
    mut v_a_5691_: *mut LeanObject,
    mut v_a_5692_: *mut LeanObject,
    mut v_a_5693_: *mut LeanObject,
    mut v_a_5694_: *mut LeanObject,
    mut v_a_5695_: *mut LeanObject,
    mut v_a_5696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5697_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5695_);
    lean_dec_ref(v_a_5694_);
    lean_dec(v_a_5693_);
    lean_dec_ref(v_a_5692_);
    lean_dec(v_a_5691_);
    lean_dec_ref(v_a_5690_);
    return v_res_5697_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(
    mut v_00_u03b1_5698_: *mut LeanObject,
    mut v_item_5699_: *mut LeanObject,
    mut v_structName_x3f_5700_: *mut LeanObject,
    mut v_a_5701_: *mut LeanObject,
    mut v_a_5702_: *mut LeanObject,
    mut v_a_5703_: *mut LeanObject,
    mut v_a_5704_: *mut LeanObject,
    mut v_a_5705_: *mut LeanObject,
    mut v_a_5706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5709_: *mut LeanObject,
    mut v_item_5710_: *mut LeanObject,
    mut v_structName_x3f_5711_: *mut LeanObject,
    mut v_a_5712_: *mut LeanObject,
    mut v_a_5713_: *mut LeanObject,
    mut v_a_5714_: *mut LeanObject,
    mut v_a_5715_: *mut LeanObject,
    mut v_a_5716_: *mut LeanObject,
    mut v_a_5717_: *mut LeanObject,
    mut v_a_5718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5719_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5717_);
    lean_dec_ref(v_a_5716_);
    lean_dec(v_a_5715_);
    lean_dec_ref(v_a_5714_);
    lean_dec(v_a_5713_);
    lean_dec_ref(v_a_5712_);
    return v_res_5719_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    v___x_5721_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0;
    v___x_5722_ = l_Lean_stringToMessageData(v___x_5721_);
    return v___x_5722_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    v___x_5724_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2;
    v___x_5725_ = l_Lean_stringToMessageData(v___x_5724_);
    return v___x_5725_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(
    mut v_item_5726_: *mut LeanObject,
    mut v_structName_x3f_5727_: *mut LeanObject,
    mut v_a_5728_: *mut LeanObject,
    mut v_a_5729_: *mut LeanObject,
    mut v_a_5730_: *mut LeanObject,
    mut v_a_5731_: *mut LeanObject,
    mut v_a_5732_: *mut LeanObject,
    mut v_a_5733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_option_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origOptionName_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: u8 = 0;
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: u8 = 0;
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_option_5735_ = lean_ctor_get(v_item_5726_, 1);
                lean_inc(v_option_5735_);
                v_origOptionName_5736_ = lean_ctor_get(v_item_5726_, 4);
                lean_inc(v_origOptionName_5736_);
                lean_dec_ref(v_item_5726_);
                v___x_5756_ = l_Lean_Name_isAnonymous(v_origOptionName_5736_);
                if v___x_5756_ == 0 {
                    v___x_5757_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
                    v___x_5758_ = l_Lean_MessageData_ofName(v_origOptionName_5736_);
                    v___x_5759_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5759_, 0, v___x_5757_);
                    lean_ctor_set(v___x_5759_, 1, v___x_5758_);
                    v___x_5760_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                    );
                    v___x_5761_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5761_, 0, v___x_5759_);
                    lean_ctor_set(v___x_5761_, 1, v___x_5760_);
                    v___y_5747_ = v___x_5761_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_origOptionName_5736_);
                    v___x_5762_ = lean_obj_once(
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
                v___x_5740_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1);
                v___x_5741_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5741_, 0, v___x_5740_);
                lean_ctor_set(v___x_5741_, 1, v___y_5738_);
                v___x_5742_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5742_, 0, v___x_5741_);
                lean_ctor_set(v___x_5742_, 1, v___y_5739_);
                v___x_5743_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3);
                v___x_5744_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5744_, 0, v___x_5742_);
                lean_ctor_set(v___x_5744_, 1, v___x_5743_);
                v___x_5745_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_5735_, v___x_5744_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_);
                lean_dec(v_option_5735_);
                return v___x_5745_;
            }
            2 => {
                if lean_obj_tag(v_structName_x3f_5727_) == 1 {
                    v_val_5748_ = lean_ctor_get(v_structName_x3f_5727_, 0);
                    lean_inc(v_val_5748_);
                    lean_dec_ref_known(v_structName_x3f_5727_, 1);
                    v___x_5749_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once), _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
                    v___x_5750_ = 0;
                    v___x_5751_ = l_Lean_MessageData_ofConstName(v_val_5748_, v___x_5750_);
                    v___x_5752_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5752_, 0, v___x_5749_);
                    lean_ctor_set(v___x_5752_, 1, v___x_5751_);
                    v___x_5753_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
                    );
                    v___x_5754_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5754_, 0, v___x_5752_);
                    lean_ctor_set(v___x_5754_, 1, v___x_5753_);
                    v___y_5738_ = v___y_5747_;
                    v___y_5739_ = v___x_5754_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_structName_x3f_5727_);
                    v___x_5755_ = lean_obj_once(
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
    mut v_item_5763_: *mut LeanObject,
    mut v_structName_x3f_5764_: *mut LeanObject,
    mut v_a_5765_: *mut LeanObject,
    mut v_a_5766_: *mut LeanObject,
    mut v_a_5767_: *mut LeanObject,
    mut v_a_5768_: *mut LeanObject,
    mut v_a_5769_: *mut LeanObject,
    mut v_a_5770_: *mut LeanObject,
    mut v_a_5771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5772_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5770_);
    lean_dec_ref(v_a_5769_);
    lean_dec(v_a_5768_);
    lean_dec_ref(v_a_5767_);
    lean_dec(v_a_5766_);
    lean_dec_ref(v_a_5765_);
    return v_res_5772_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(
    mut v_00_u03b1_5773_: *mut LeanObject,
    mut v_item_5774_: *mut LeanObject,
    mut v_structName_x3f_5775_: *mut LeanObject,
    mut v_a_5776_: *mut LeanObject,
    mut v_a_5777_: *mut LeanObject,
    mut v_a_5778_: *mut LeanObject,
    mut v_a_5779_: *mut LeanObject,
    mut v_a_5780_: *mut LeanObject,
    mut v_a_5781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5784_: *mut LeanObject,
    mut v_item_5785_: *mut LeanObject,
    mut v_structName_x3f_5786_: *mut LeanObject,
    mut v_a_5787_: *mut LeanObject,
    mut v_a_5788_: *mut LeanObject,
    mut v_a_5789_: *mut LeanObject,
    mut v_a_5790_: *mut LeanObject,
    mut v_a_5791_: *mut LeanObject,
    mut v_a_5792_: *mut LeanObject,
    mut v_a_5793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5794_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5792_);
    lean_dec_ref(v_a_5791_);
    lean_dec(v_a_5790_);
    lean_dec_ref(v_a_5789_);
    lean_dec(v_a_5788_);
    lean_dec_ref(v_a_5787_);
    return v_res_5794_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    v___x_5795_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5795_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    v___x_5796_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
    v___x_5797_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5797_, 0, v___x_5796_);
    return v___x_5797_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    v___x_5798_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_5799_ = lean_unsigned_to_nat(0);
    v___x_5800_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_5800_, 0, v___x_5799_);
    lean_ctor_set(v___x_5800_, 1, v___x_5799_);
    lean_ctor_set(v___x_5800_, 2, v___x_5799_);
    lean_ctor_set(v___x_5800_, 3, v___x_5799_);
    lean_ctor_set(v___x_5800_, 4, v___x_5798_);
    lean_ctor_set(v___x_5800_, 5, v___x_5798_);
    lean_ctor_set(v___x_5800_, 6, v___x_5798_);
    lean_ctor_set(v___x_5800_, 7, v___x_5798_);
    lean_ctor_set(v___x_5800_, 8, v___x_5798_);
    lean_ctor_set(v___x_5800_, 9, v___x_5798_);
    return v___x_5800_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    v___x_5801_ = lean_unsigned_to_nat(32);
    v___x_5802_ = lean_mk_empty_array_with_capacity(v___x_5801_);
    v___x_5803_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5803_, 0, v___x_5802_);
    return v___x_5803_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_5804_: usize = 0;
    let mut v___x_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    v___x_5804_ = 5usize;
    v___x_5805_ = lean_unsigned_to_nat(0);
    v___x_5806_ = lean_unsigned_to_nat(32);
    v___x_5807_ = lean_mk_empty_array_with_capacity(v___x_5806_);
    v___x_5808_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
    v___x_5809_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_5809_, 0, v___x_5808_);
    lean_ctor_set(v___x_5809_, 1, v___x_5807_);
    lean_ctor_set(v___x_5809_, 2, v___x_5805_);
    lean_ctor_set(v___x_5809_, 3, v___x_5805_);
    lean_ctor_set_usize(v___x_5809_, 4, v___x_5804_);
    return v___x_5809_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    v___x_5810_ = lean_box(1);
    v___x_5811_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_5812_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_5813_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_5813_, 0, v___x_5812_);
    lean_ctor_set(v___x_5813_, 1, v___x_5811_);
    lean_ctor_set(v___x_5813_, 2, v___x_5810_);
    return v___x_5813_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut LeanObject = core::ptr::null_mut();
    v___x_5815_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_5816_ = l_Lean_stringToMessageData(v___x_5815_);
    return v___x_5816_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    v___x_5818_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_5819_ = l_Lean_stringToMessageData(v___x_5818_);
    return v___x_5819_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    v___x_5821_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_5822_ = l_Lean_stringToMessageData(v___x_5821_);
    return v___x_5822_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    v___x_5824_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_5825_ = l_Lean_stringToMessageData(v___x_5824_);
    return v___x_5825_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    v___x_5827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14;
    v___x_5828_ = l_Lean_stringToMessageData(v___x_5827_);
    return v___x_5828_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    v___x_5830_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16;
    v___x_5831_ = l_Lean_stringToMessageData(v___x_5830_);
    return v___x_5831_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    v___x_5833_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18;
    v___x_5834_ = l_Lean_stringToMessageData(v___x_5833_);
    return v___x_5834_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(
    mut v_msg_5835_: *mut LeanObject,
    mut v_declHint_5836_: *mut LeanObject,
    mut v___y_5837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: u8 = 0;
    let mut v_isExporting_5842_: u8 = 0;
    let mut v___x_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: u8 = 0;
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5864_: u8 = 0;
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: u8 = 0;
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5896_: u8 = 0;
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5839_ = lean_st_ref_get(v___y_5837_);
                v_env_5840_ = lean_ctor_get(v___x_5839_, 0);
                lean_inc_ref(v_env_5840_);
                lean_dec(v___x_5839_);
                v___x_5841_ = l_Lean_Name_isAnonymous(v_declHint_5836_);
                if v___x_5841_ == 0 {
                    v_isExporting_5842_ = lean_ctor_get_uint8(
                        v_env_5840_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5842_ == 0 {
                        lean_dec_ref(v_env_5840_);
                        lean_dec(v_declHint_5836_);
                        v___x_5843_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5843_, 0, v_msg_5835_);
                        return v___x_5843_;
                    } else {
                        lean_inc_ref(v_env_5840_);
                        v___x_5844_ = l_Lean_Environment_setExporting(v_env_5840_, v___x_5841_);
                        lean_inc(v_declHint_5836_);
                        lean_inc_ref(v___x_5844_);
                        v___x_5845_ = l_Lean_Environment_contains(
                            v___x_5844_,
                            v_declHint_5836_,
                            v_isExporting_5842_,
                        );
                        if v___x_5845_ == 0 {
                            lean_dec_ref(v___x_5844_);
                            lean_dec_ref(v_env_5840_);
                            lean_dec(v_declHint_5836_);
                            v___x_5846_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5846_, 0, v_msg_5835_);
                            return v___x_5846_;
                        } else {
                            v___x_5847_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
                            v___x_5848_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
                            v___x_5849_ = l_Lean_Options_empty;
                            v___x_5850_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_5850_, 0, v___x_5844_);
                            lean_ctor_set(v___x_5850_, 1, v___x_5847_);
                            lean_ctor_set(v___x_5850_, 2, v___x_5848_);
                            lean_ctor_set(v___x_5850_, 3, v___x_5849_);
                            lean_inc(v_declHint_5836_);
                            v___x_5851_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5836_, v___x_5841_);
                            v_c_5852_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_5852_, 0, v___x_5850_);
                            lean_ctor_set(v_c_5852_, 1, v___x_5851_);
                            v___x_5853_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5840_,
                                v_declHint_5836_,
                            );
                            if lean_obj_tag(v___x_5853_) == 0 {
                                lean_dec_ref(v_env_5840_);
                                lean_dec(v_declHint_5836_);
                                v___x_5854_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
                                v___x_5855_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5855_, 0, v___x_5854_);
                                lean_ctor_set(v___x_5855_, 1, v_c_5852_);
                                v___x_5856_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
                                v___x_5857_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5857_, 0, v___x_5855_);
                                lean_ctor_set(v___x_5857_, 1, v___x_5856_);
                                v___x_5858_ = l_Lean_MessageData_note(v___x_5857_);
                                v___x_5859_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5859_, 0, v_msg_5835_);
                                lean_ctor_set(v___x_5859_, 1, v___x_5858_);
                                v___x_5860_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_5860_, 0, v___x_5859_);
                                return v___x_5860_;
                            } else {
                                v_val_5861_ = lean_ctor_get(v___x_5853_, 0);
                                v_isSharedCheck_5896_ = (!lean_is_exclusive(v___x_5853_)) as u8;
                                if v_isSharedCheck_5896_ == 0 {
                                    v___x_5863_ = v___x_5853_;
                                    v_isShared_5864_ = v_isSharedCheck_5896_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_5861_);
                                    lean_dec(v___x_5853_);
                                    v___x_5863_ = lean_box(0);
                                    v_isShared_5864_ = v_isSharedCheck_5896_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_5840_);
                    lean_dec(v_declHint_5836_);
                    v___x_5897_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5897_, 0, v_msg_5835_);
                    return v___x_5897_;
                }
            }
            1 => {
                v___x_5865_ = lean_box(0);
                v___x_5866_ = l_Lean_Environment_header(v_env_5840_);
                lean_dec_ref(v_env_5840_);
                v___x_5867_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5866_);
                v_mod_5868_ = lean_array_get(v___x_5865_, v___x_5867_, v_val_5861_);
                lean_dec(v_val_5861_);
                lean_dec_ref(v___x_5867_);
                v___x_5869_ = l_Lean_isPrivateName(v_declHint_5836_);
                lean_dec(v_declHint_5836_);
                if v___x_5869_ == 0 {
                    v___x_5870_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_5871_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5871_, 0, v___x_5870_);
                    lean_ctor_set(v___x_5871_, 1, v_c_5852_);
                    v___x_5872_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_5873_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5873_, 0, v___x_5871_);
                    lean_ctor_set(v___x_5873_, 1, v___x_5872_);
                    v___x_5874_ = l_Lean_MessageData_ofName(v_mod_5868_);
                    v___x_5875_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5875_, 0, v___x_5873_);
                    lean_ctor_set(v___x_5875_, 1, v___x_5874_);
                    v___x_5876_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
                    v___x_5877_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5877_, 0, v___x_5875_);
                    lean_ctor_set(v___x_5877_, 1, v___x_5876_);
                    v___x_5878_ = l_Lean_MessageData_note(v___x_5877_);
                    v___x_5879_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5879_, 0, v_msg_5835_);
                    lean_ctor_set(v___x_5879_, 1, v___x_5878_);
                    if v_isShared_5864_ == 0 {
                        lean_ctor_set_tag(v___x_5863_, 0);
                        lean_ctor_set(v___x_5863_, 0, v___x_5879_);
                        v___x_5881_ = v___x_5863_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5882_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5882_, 0, v___x_5879_);
                        v___x_5881_ = v_reuseFailAlloc_5882_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5883_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_5884_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5884_, 0, v___x_5883_);
                    lean_ctor_set(v___x_5884_, 1, v_c_5852_);
                    v___x_5885_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
                    v___x_5886_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5886_, 0, v___x_5884_);
                    lean_ctor_set(v___x_5886_, 1, v___x_5885_);
                    v___x_5887_ = l_Lean_MessageData_ofName(v_mod_5868_);
                    v___x_5888_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5888_, 0, v___x_5886_);
                    lean_ctor_set(v___x_5888_, 1, v___x_5887_);
                    v___x_5889_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
                    v___x_5890_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5890_, 0, v___x_5888_);
                    lean_ctor_set(v___x_5890_, 1, v___x_5889_);
                    v___x_5891_ = l_Lean_MessageData_note(v___x_5890_);
                    v___x_5892_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5892_, 0, v_msg_5835_);
                    lean_ctor_set(v___x_5892_, 1, v___x_5891_);
                    if v_isShared_5864_ == 0 {
                        lean_ctor_set_tag(v___x_5863_, 0);
                        lean_ctor_set(v___x_5863_, 0, v___x_5892_);
                        v___x_5894_ = v___x_5863_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5895_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5895_, 0, v___x_5892_);
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
    mut v_msg_5898_: *mut LeanObject,
    mut v_declHint_5899_: *mut LeanObject,
    mut v___y_5900_: *mut LeanObject,
    mut v___y_5901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5902_: *mut LeanObject = core::ptr::null_mut();
    v_res_5902_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_5898_, v_declHint_5899_, v___y_5900_);
    lean_dec(v___y_5900_);
    return v_res_5902_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(
    mut v_msg_5903_: *mut LeanObject,
    mut v_declHint_5904_: *mut LeanObject,
    mut v___y_5905_: *mut LeanObject,
    mut v___y_5906_: *mut LeanObject,
    mut v___y_5907_: *mut LeanObject,
    mut v___y_5908_: *mut LeanObject,
    mut v___y_5909_: *mut LeanObject,
    mut v___y_5910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v___x_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5912_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_5903_, v_declHint_5904_, v___y_5910_);
                v_a_5913_ = lean_ctor_get(v___x_5912_, 0);
                v_isSharedCheck_5922_ = (!lean_is_exclusive(v___x_5912_)) as u8;
                if v_isSharedCheck_5922_ == 0 {
                    v___x_5915_ = v___x_5912_;
                    v_isShared_5916_ = v_isSharedCheck_5922_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5913_);
                    lean_dec(v___x_5912_);
                    v___x_5915_ = lean_box(0);
                    v_isShared_5916_ = v_isSharedCheck_5922_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5917_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5918_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_5918_, 0, v___x_5917_);
                lean_ctor_set(v___x_5918_, 1, v_a_5913_);
                if v_isShared_5916_ == 0 {
                    lean_ctor_set(v___x_5915_, 0, v___x_5918_);
                    v___x_5920_ = v___x_5915_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5921_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5921_, 0, v___x_5918_);
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
    mut v_msg_5923_: *mut LeanObject,
    mut v_declHint_5924_: *mut LeanObject,
    mut v___y_5925_: *mut LeanObject,
    mut v___y_5926_: *mut LeanObject,
    mut v___y_5927_: *mut LeanObject,
    mut v___y_5928_: *mut LeanObject,
    mut v___y_5929_: *mut LeanObject,
    mut v___y_5930_: *mut LeanObject,
    mut v___y_5931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5932_: *mut LeanObject = core::ptr::null_mut();
    v_res_5932_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_5923_, v_declHint_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_);
    lean_dec(v___y_5930_);
    lean_dec_ref(v___y_5929_);
    lean_dec(v___y_5928_);
    lean_dec_ref(v___y_5927_);
    lean_dec(v___y_5926_);
    lean_dec_ref(v___y_5925_);
    return v_res_5932_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(
    mut v_ref_5933_: *mut LeanObject,
    mut v_msg_5934_: *mut LeanObject,
    mut v_declHint_5935_: *mut LeanObject,
    mut v___y_5936_: *mut LeanObject,
    mut v___y_5937_: *mut LeanObject,
    mut v___y_5938_: *mut LeanObject,
    mut v___y_5939_: *mut LeanObject,
    mut v___y_5940_: *mut LeanObject,
    mut v___y_5941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    v___x_5943_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_5934_, v_declHint_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_);
    v_a_5944_ = lean_ctor_get(v___x_5943_, 0);
    lean_inc(v_a_5944_);
    lean_dec_ref(v___x_5943_);
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
    mut v_ref_5946_: *mut LeanObject,
    mut v_msg_5947_: *mut LeanObject,
    mut v_declHint_5948_: *mut LeanObject,
    mut v___y_5949_: *mut LeanObject,
    mut v___y_5950_: *mut LeanObject,
    mut v___y_5951_: *mut LeanObject,
    mut v___y_5952_: *mut LeanObject,
    mut v___y_5953_: *mut LeanObject,
    mut v___y_5954_: *mut LeanObject,
    mut v___y_5955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5956_: *mut LeanObject = core::ptr::null_mut();
    v_res_5956_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_5946_, v_msg_5947_, v_declHint_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
    lean_dec(v___y_5954_);
    lean_dec_ref(v___y_5953_);
    lean_dec(v___y_5952_);
    lean_dec_ref(v___y_5951_);
    lean_dec(v___y_5950_);
    lean_dec_ref(v___y_5949_);
    lean_dec(v_ref_5946_);
    return v_res_5956_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    v___x_5958_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0;
    v___x_5959_ = l_Lean_stringToMessageData(v___x_5958_);
    return v___x_5959_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_ref_5960_: *mut LeanObject,
    mut v_constName_5961_: *mut LeanObject,
    mut v___y_5962_: *mut LeanObject,
    mut v___y_5963_: *mut LeanObject,
    mut v___y_5964_: *mut LeanObject,
    mut v___y_5965_: *mut LeanObject,
    mut v___y_5966_: *mut LeanObject,
    mut v___y_5967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: u8 = 0;
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    v___x_5969_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
    v___x_5970_ = 0;
    lean_inc(v_constName_5961_);
    v___x_5971_ = l_Lean_MessageData_ofConstName(v_constName_5961_, v___x_5970_);
    v___x_5972_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5972_, 0, v___x_5969_);
    lean_ctor_set(v___x_5972_, 1, v___x_5971_);
    v___x_5973_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once),
        _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28,
    );
    v___x_5974_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5974_, 0, v___x_5972_);
    lean_ctor_set(v___x_5974_, 1, v___x_5973_);
    v___x_5975_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_5960_, v___x_5974_, v_constName_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_);
    return v___x_5975_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_ref_5976_: *mut LeanObject,
    mut v_constName_5977_: *mut LeanObject,
    mut v___y_5978_: *mut LeanObject,
    mut v___y_5979_: *mut LeanObject,
    mut v___y_5980_: *mut LeanObject,
    mut v___y_5981_: *mut LeanObject,
    mut v___y_5982_: *mut LeanObject,
    mut v___y_5983_: *mut LeanObject,
    mut v___y_5984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5985_: *mut LeanObject = core::ptr::null_mut();
    v_res_5985_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_5976_, v_constName_5977_, v___y_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
    lean_dec(v___y_5983_);
    lean_dec_ref(v___y_5982_);
    lean_dec(v___y_5981_);
    lean_dec_ref(v___y_5980_);
    lean_dec(v___y_5979_);
    lean_dec_ref(v___y_5978_);
    lean_dec(v_ref_5976_);
    return v_res_5985_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_constName_5986_: *mut LeanObject,
    mut v___y_5987_: *mut LeanObject,
    mut v___y_5988_: *mut LeanObject,
    mut v___y_5989_: *mut LeanObject,
    mut v___y_5990_: *mut LeanObject,
    mut v___y_5991_: *mut LeanObject,
    mut v___y_5992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5994_ = lean_ctor_get(v___y_5991_, 5);
    v___x_5995_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_5994_, v_constName_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_);
    return v___x_5995_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_constName_5996_: *mut LeanObject,
    mut v___y_5997_: *mut LeanObject,
    mut v___y_5998_: *mut LeanObject,
    mut v___y_5999_: *mut LeanObject,
    mut v___y_6000_: *mut LeanObject,
    mut v___y_6001_: *mut LeanObject,
    mut v___y_6002_: *mut LeanObject,
    mut v___y_6003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6004_: *mut LeanObject = core::ptr::null_mut();
    v_res_6004_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_);
    lean_dec(v___y_6002_);
    lean_dec_ref(v___y_6001_);
    lean_dec(v___y_6000_);
    lean_dec_ref(v___y_5999_);
    lean_dec(v___y_5998_);
    lean_dec_ref(v___y_5997_);
    return v_res_6004_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(
    mut v_constName_6005_: *mut LeanObject,
    mut v___y_6006_: *mut LeanObject,
    mut v___y_6007_: *mut LeanObject,
    mut v___y_6008_: *mut LeanObject,
    mut v___y_6009_: *mut LeanObject,
    mut v___y_6010_: *mut LeanObject,
    mut v___y_6011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: u8 = 0;
    let mut v___x_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6021_: u8 = 0;
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6013_ = lean_st_ref_get(v___y_6011_);
                v_env_6014_ = lean_ctor_get(v___x_6013_, 0);
                lean_inc_ref(v_env_6014_);
                lean_dec(v___x_6013_);
                v___x_6015_ = 0;
                lean_inc(v_constName_6005_);
                v___x_6016_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_6014_,
                    v_constName_6005_,
                    v___x_6015_,
                );
                if lean_obj_tag(v___x_6016_) == 0 {
                    v___x_6017_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_);
                    return v___x_6017_;
                } else {
                    lean_dec(v_constName_6005_);
                    v_val_6018_ = lean_ctor_get(v___x_6016_, 0);
                    v_isSharedCheck_6025_ = (!lean_is_exclusive(v___x_6016_)) as u8;
                    if v_isSharedCheck_6025_ == 0 {
                        v___x_6020_ = v___x_6016_;
                        v_isShared_6021_ = v_isSharedCheck_6025_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6018_);
                        lean_dec(v___x_6016_);
                        v___x_6020_ = lean_box(0);
                        v_isShared_6021_ = v_isSharedCheck_6025_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6021_ == 0 {
                    lean_ctor_set_tag(v___x_6020_, 0);
                    v___x_6023_ = v___x_6020_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6024_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6024_, 0, v_val_6018_);
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
    mut v_constName_6026_: *mut LeanObject,
    mut v___y_6027_: *mut LeanObject,
    mut v___y_6028_: *mut LeanObject,
    mut v___y_6029_: *mut LeanObject,
    mut v___y_6030_: *mut LeanObject,
    mut v___y_6031_: *mut LeanObject,
    mut v___y_6032_: *mut LeanObject,
    mut v___y_6033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6034_: *mut LeanObject = core::ptr::null_mut();
    v_res_6034_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_);
    lean_dec(v___y_6032_);
    lean_dec_ref(v___y_6031_);
    lean_dec(v___y_6030_);
    lean_dec_ref(v___y_6029_);
    lean_dec(v___y_6028_);
    lean_dec_ref(v___y_6027_);
    return v_res_6034_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(
    mut v_a_6035_: *mut LeanObject,
    mut v_a_6036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6042_: u8 = 0;
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6048_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6035_) == 0 {
                    v___x_6037_ = l_List_reverse___redArg(v_a_6036_);
                    return v___x_6037_;
                } else {
                    v_head_6038_ = lean_ctor_get(v_a_6035_, 0);
                    v_tail_6039_ = lean_ctor_get(v_a_6035_, 1);
                    v_isSharedCheck_6048_ = (!lean_is_exclusive(v_a_6035_)) as u8;
                    if v_isSharedCheck_6048_ == 0 {
                        v___x_6041_ = v_a_6035_;
                        v_isShared_6042_ = v_isSharedCheck_6048_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6039_);
                        lean_inc(v_head_6038_);
                        lean_dec(v_a_6035_);
                        v___x_6041_ = lean_box(0);
                        v_isShared_6042_ = v_isSharedCheck_6048_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6043_ = l_Lean_mkLevelParam(v_head_6038_);
                if v_isShared_6042_ == 0 {
                    lean_ctor_set(v___x_6041_, 1, v_a_6036_);
                    lean_ctor_set(v___x_6041_, 0, v___x_6043_);
                    v___x_6045_ = v___x_6041_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6047_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6047_, 0, v___x_6043_);
                    lean_ctor_set(v_reuseFailAlloc_6047_, 1, v_a_6036_);
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
    mut v_constName_6049_: *mut LeanObject,
    mut v___y_6050_: *mut LeanObject,
    mut v___y_6051_: *mut LeanObject,
    mut v___y_6052_: *mut LeanObject,
    mut v___y_6053_: *mut LeanObject,
    mut v___y_6054_: *mut LeanObject,
    mut v___y_6055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6061_: u8 = 0;
    let mut v_levelParams_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6069_: u8 = 0;
    let mut v_a_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6073_: u8 = 0;
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_constName_6049_);
                v___x_6057_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_);
                if lean_obj_tag(v___x_6057_) == 0 {
                    v_a_6058_ = lean_ctor_get(v___x_6057_, 0);
                    v_isSharedCheck_6069_ = (!lean_is_exclusive(v___x_6057_)) as u8;
                    if v_isSharedCheck_6069_ == 0 {
                        v___x_6060_ = v___x_6057_;
                        v_isShared_6061_ = v_isSharedCheck_6069_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6058_);
                        lean_dec(v___x_6057_);
                        v___x_6060_ = lean_box(0);
                        v_isShared_6061_ = v_isSharedCheck_6069_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_constName_6049_);
                    v_a_6070_ = lean_ctor_get(v___x_6057_, 0);
                    v_isSharedCheck_6077_ = (!lean_is_exclusive(v___x_6057_)) as u8;
                    if v_isSharedCheck_6077_ == 0 {
                        v___x_6072_ = v___x_6057_;
                        v_isShared_6073_ = v_isSharedCheck_6077_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6070_);
                        lean_dec(v___x_6057_);
                        v___x_6072_ = lean_box(0);
                        v_isShared_6073_ = v_isSharedCheck_6077_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_6062_ = lean_ctor_get(v_a_6058_, 1);
                lean_inc(v_levelParams_6062_);
                lean_dec(v_a_6058_);
                v___x_6063_ = lean_box(0);
                v___x_6064_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(v_levelParams_6062_, v___x_6063_);
                v___x_6065_ = l_Lean_mkConst(v_constName_6049_, v___x_6064_);
                if v_isShared_6061_ == 0 {
                    lean_ctor_set(v___x_6060_, 0, v___x_6065_);
                    v___x_6067_ = v___x_6060_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6068_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6068_, 0, v___x_6065_);
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
                    v_reuseFailAlloc_6076_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6076_, 0, v_a_6070_);
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
    mut v_constName_6078_: *mut LeanObject,
    mut v___y_6079_: *mut LeanObject,
    mut v___y_6080_: *mut LeanObject,
    mut v___y_6081_: *mut LeanObject,
    mut v___y_6082_: *mut LeanObject,
    mut v___y_6083_: *mut LeanObject,
    mut v___y_6084_: *mut LeanObject,
    mut v___y_6085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6086_: *mut LeanObject = core::ptr::null_mut();
    v_res_6086_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_constName_6078_, v___y_6079_, v___y_6080_, v___y_6081_, v___y_6082_, v___y_6083_, v___y_6084_);
    lean_dec(v___y_6084_);
    lean_dec_ref(v___y_6083_);
    lean_dec(v___y_6082_);
    lean_dec_ref(v___y_6081_);
    lean_dec(v___y_6080_);
    lean_dec_ref(v___y_6079_);
    return v_res_6086_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(
    mut v_t_6087_: *mut LeanObject,
    mut v___y_6088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_6092_: u8 = 0;
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6107_: u8 = 0;
    let mut v_enabled_6108_: u8 = 0;
    let mut v_assignment_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6114_: u8 = 0;
    let mut v___x_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6125_: u8 = 0;
    let mut v_isSharedCheck_6126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6090_ = lean_st_ref_get(v___y_6088_);
                v_infoState_6091_ = lean_ctor_get(v___x_6090_, 7);
                lean_inc_ref(v_infoState_6091_);
                lean_dec(v___x_6090_);
                v_enabled_6092_ = lean_ctor_get_uint8(
                    v_infoState_6091_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_6091_);
                if v_enabled_6092_ == 0 {
                    lean_dec_ref(v_t_6087_);
                    v___x_6093_ = lean_box(0);
                    v___x_6094_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6094_, 0, v___x_6093_);
                    return v___x_6094_;
                } else {
                    v___x_6095_ = lean_st_ref_take(v___y_6088_);
                    v_infoState_6096_ = lean_ctor_get(v___x_6095_, 7);
                    v_env_6097_ = lean_ctor_get(v___x_6095_, 0);
                    v_nextMacroScope_6098_ = lean_ctor_get(v___x_6095_, 1);
                    v_ngen_6099_ = lean_ctor_get(v___x_6095_, 2);
                    v_auxDeclNGen_6100_ = lean_ctor_get(v___x_6095_, 3);
                    v_traceState_6101_ = lean_ctor_get(v___x_6095_, 4);
                    v_cache_6102_ = lean_ctor_get(v___x_6095_, 5);
                    v_messages_6103_ = lean_ctor_get(v___x_6095_, 6);
                    v_snapshotTasks_6104_ = lean_ctor_get(v___x_6095_, 8);
                    v_isSharedCheck_6126_ = (!lean_is_exclusive(v___x_6095_)) as u8;
                    if v_isSharedCheck_6126_ == 0 {
                        v___x_6106_ = v___x_6095_;
                        v_isShared_6107_ = v_isSharedCheck_6126_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_6104_);
                        lean_inc(v_infoState_6096_);
                        lean_inc(v_messages_6103_);
                        lean_inc(v_cache_6102_);
                        lean_inc(v_traceState_6101_);
                        lean_inc(v_auxDeclNGen_6100_);
                        lean_inc(v_ngen_6099_);
                        lean_inc(v_nextMacroScope_6098_);
                        lean_inc(v_env_6097_);
                        lean_dec(v___x_6095_);
                        v___x_6106_ = lean_box(0);
                        v_isShared_6107_ = v_isSharedCheck_6126_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_6108_ = lean_ctor_get_uint8(
                    v_infoState_6096_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_6109_ = lean_ctor_get(v_infoState_6096_, 0);
                v_lazyAssignment_6110_ = lean_ctor_get(v_infoState_6096_, 1);
                v_trees_6111_ = lean_ctor_get(v_infoState_6096_, 2);
                v_isSharedCheck_6125_ = (!lean_is_exclusive(v_infoState_6096_)) as u8;
                if v_isSharedCheck_6125_ == 0 {
                    v___x_6113_ = v_infoState_6096_;
                    v_isShared_6114_ = v_isSharedCheck_6125_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_trees_6111_);
                    lean_inc(v_lazyAssignment_6110_);
                    lean_inc(v_assignment_6109_);
                    lean_dec(v_infoState_6096_);
                    v___x_6113_ = lean_box(0);
                    v_isShared_6114_ = v_isSharedCheck_6125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6115_ = l_Lean_PersistentArray_push___redArg(v_trees_6111_, v_t_6087_);
                if v_isShared_6114_ == 0 {
                    lean_ctor_set(v___x_6113_, 2, v___x_6115_);
                    v___x_6117_ = v___x_6113_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6124_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_assignment_6109_);
                    lean_ctor_set(v_reuseFailAlloc_6124_, 1, v_lazyAssignment_6110_);
                    lean_ctor_set(v_reuseFailAlloc_6124_, 2, v___x_6115_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6124_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_6108_,
                    );
                    v___x_6117_ = v_reuseFailAlloc_6124_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6107_ == 0 {
                    lean_ctor_set(v___x_6106_, 7, v___x_6117_);
                    v___x_6119_ = v___x_6106_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6123_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6123_, 0, v_env_6097_);
                    lean_ctor_set(v_reuseFailAlloc_6123_, 1, v_nextMacroScope_6098_);
                    lean_ctor_set(v_reuseFailAlloc_6123_, 2, v_ngen_6099_);
                    lean_ctor_set(v_reuseFailAlloc_6123_, 3, v_auxDeclNGen_6100_);
                    lean_ctor_set(v_reuseFailAlloc_6123_, 4, v_traceState_6101_);
                    lean_ctor_set(v_reuseFailAlloc_6123_, 5, v_cache_6102_);
                    lean_ctor_set(v_reuseFailAlloc_6123_, 6, v_messages_6103_);
                    lean_ctor_set(v_reuseFailAlloc_6123_, 7, v___x_6117_);
                    lean_ctor_set(v_reuseFailAlloc_6123_, 8, v_snapshotTasks_6104_);
                    v___x_6119_ = v_reuseFailAlloc_6123_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6120_ = lean_st_ref_set(v___y_6088_, v___x_6119_);
                v___x_6121_ = lean_box(0);
                v___x_6122_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6122_, 0, v___x_6121_);
                return v___x_6122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_t_6127_: *mut LeanObject,
    mut v___y_6128_: *mut LeanObject,
    mut v___y_6129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6130_: *mut LeanObject = core::ptr::null_mut();
    v_res_6130_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_6127_, v___y_6128_);
    lean_dec(v___y_6128_);
    return v_res_6130_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    v___x_6131_ = lean_unsigned_to_nat(32);
    v___x_6132_ = lean_mk_empty_array_with_capacity(v___x_6131_);
    v___x_6133_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6133_, 0, v___x_6132_);
    return v___x_6133_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_6134_: usize = 0;
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut LeanObject = core::ptr::null_mut();
    v___x_6134_ = 5usize;
    v___x_6135_ = lean_unsigned_to_nat(0);
    v___x_6136_ = lean_unsigned_to_nat(32);
    v___x_6137_ = lean_mk_empty_array_with_capacity(v___x_6136_);
    v___x_6138_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0);
    v___x_6139_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_6139_, 0, v___x_6138_);
    lean_ctor_set(v___x_6139_, 1, v___x_6137_);
    lean_ctor_set(v___x_6139_, 2, v___x_6135_);
    lean_ctor_set(v___x_6139_, 3, v___x_6135_);
    lean_ctor_set_usize(v___x_6139_, 4, v___x_6134_);
    return v___x_6139_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(
    mut v_t_6140_: *mut LeanObject,
    mut v___y_6141_: *mut LeanObject,
    mut v___y_6142_: *mut LeanObject,
    mut v___y_6143_: *mut LeanObject,
    mut v___y_6144_: *mut LeanObject,
    mut v___y_6145_: *mut LeanObject,
    mut v___y_6146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_6150_: u8 = 0;
    v___x_6148_ = lean_st_ref_get(v___y_6146_);
    v_infoState_6149_ = lean_ctor_get(v___x_6148_, 7);
    lean_inc_ref(v_infoState_6149_);
    lean_dec(v___x_6148_);
    v_enabled_6150_ = lean_ctor_get_uint8(
        v_infoState_6149_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    lean_dec_ref(v_infoState_6149_);
    if v_enabled_6150_ == 0 {
        let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_t_6140_);
        v___x_6151_ = lean_box(0);
        v___x_6152_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6152_, 0, v___x_6151_);
        return v___x_6152_;
    } else {
        let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
        v___x_6153_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
        v___x_6154_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_6154_, 0, v_t_6140_);
        lean_ctor_set(v___x_6154_, 1, v___x_6153_);
        v___x_6155_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v___x_6154_, v___y_6146_);
        return v___x_6155_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___boxed(
    mut v_t_6156_: *mut LeanObject,
    mut v___y_6157_: *mut LeanObject,
    mut v___y_6158_: *mut LeanObject,
    mut v___y_6159_: *mut LeanObject,
    mut v___y_6160_: *mut LeanObject,
    mut v___y_6161_: *mut LeanObject,
    mut v___y_6162_: *mut LeanObject,
    mut v___y_6163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6164_: *mut LeanObject = core::ptr::null_mut();
    v_res_6164_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v_t_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_);
    lean_dec(v___y_6162_);
    lean_dec_ref(v___y_6161_);
    lean_dec(v___y_6160_);
    lean_dec_ref(v___y_6159_);
    lean_dec(v___y_6158_);
    lean_dec_ref(v___y_6157_);
    return v_res_6164_;
}
pub unsafe fn l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(
    mut v_stx_6165_: *mut LeanObject,
    mut v_n_6166_: *mut LeanObject,
    mut v_expectedType_x3f_6167_: *mut LeanObject,
    mut v___y_6168_: *mut LeanObject,
    mut v___y_6169_: *mut LeanObject,
    mut v___y_6170_: *mut LeanObject,
    mut v___y_6171_: *mut LeanObject,
    mut v___y_6172_: *mut LeanObject,
    mut v___y_6173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: u8 = 0;
    let mut v___x_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6187_: u8 = 0;
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6175_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_n_6166_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_);
                if lean_obj_tag(v___x_6175_) == 0 {
                    v_a_6176_ = lean_ctor_get(v___x_6175_, 0);
                    lean_inc(v_a_6176_);
                    lean_dec_ref_known(v___x_6175_, 1);
                    v___x_6177_ = lean_box(0);
                    v___x_6178_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6178_, 0, v___x_6177_);
                    lean_ctor_set(v___x_6178_, 1, v_stx_6165_);
                    v___x_6179_ = l_Lean_LocalContext_empty;
                    v___x_6180_ = 0;
                    v___x_6181_ = lean_alloc_ctor(0, 4, (2) as u32);
                    lean_ctor_set(v___x_6181_, 0, v___x_6178_);
                    lean_ctor_set(v___x_6181_, 1, v___x_6179_);
                    lean_ctor_set(v___x_6181_, 2, v_expectedType_x3f_6167_);
                    lean_ctor_set(v___x_6181_, 3, v_a_6176_);
                    lean_ctor_set_uint8(
                        v___x_6181_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v___x_6180_,
                    );
                    lean_ctor_set_uint8(
                        v___x_6181_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v___x_6180_,
                    );
                    v___x_6182_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6182_, 0, v___x_6181_);
                    v___x_6183_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_6182_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_);
                    return v___x_6183_;
                } else {
                    lean_dec(v_expectedType_x3f_6167_);
                    lean_dec(v_stx_6165_);
                    v_a_6184_ = lean_ctor_get(v___x_6175_, 0);
                    v_isSharedCheck_6191_ = (!lean_is_exclusive(v___x_6175_)) as u8;
                    if v_isSharedCheck_6191_ == 0 {
                        v___x_6186_ = v___x_6175_;
                        v_isShared_6187_ = v_isSharedCheck_6191_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6184_);
                        lean_dec(v___x_6175_);
                        v___x_6186_ = lean_box(0);
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
                    v_reuseFailAlloc_6190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6190_, 0, v_a_6184_);
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
    mut v_stx_6192_: *mut LeanObject,
    mut v_n_6193_: *mut LeanObject,
    mut v_expectedType_x3f_6194_: *mut LeanObject,
    mut v___y_6195_: *mut LeanObject,
    mut v___y_6196_: *mut LeanObject,
    mut v___y_6197_: *mut LeanObject,
    mut v___y_6198_: *mut LeanObject,
    mut v___y_6199_: *mut LeanObject,
    mut v___y_6200_: *mut LeanObject,
    mut v___y_6201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6202_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6200_);
    lean_dec_ref(v___y_6199_);
    lean_dec(v___y_6198_);
    lean_dec_ref(v___y_6197_);
    lean_dec(v___y_6196_);
    lean_dec_ref(v___y_6195_);
    return v_res_6202_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
    mut v_item_6203_: *mut LeanObject,
    mut v_projFn_6204_: *mut LeanObject,
    mut v_a_6205_: *mut LeanObject,
    mut v_a_6206_: *mut LeanObject,
    mut v_a_6207_: *mut LeanObject,
    mut v_a_6208_: *mut LeanObject,
    mut v_a_6209_: *mut LeanObject,
    mut v_a_6210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_6214_: u8 = 0;
    v___x_6212_ = lean_st_ref_get(v_a_6210_);
    v_infoState_6213_ = lean_ctor_get(v___x_6212_, 7);
    lean_inc_ref(v_infoState_6213_);
    lean_dec(v___x_6212_);
    v_enabled_6214_ = lean_ctor_get_uint8(
        v_infoState_6213_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    lean_dec_ref(v_infoState_6213_);
    if v_enabled_6214_ == 0 {
        let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_projFn_6204_);
        v___x_6215_ = lean_box(0);
        v___x_6216_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6216_, 0, v___x_6215_);
        return v___x_6216_;
    } else {
        let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
        let mut v_env_6218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6219_: u8 = 0;
        v___x_6217_ = lean_st_ref_get(v_a_6210_);
        v_env_6218_ = lean_ctor_get(v___x_6217_, 0);
        lean_inc_ref(v_env_6218_);
        lean_dec(v___x_6217_);
        lean_inc(v_projFn_6204_);
        v___x_6219_ = l_Lean_Environment_contains(v_env_6218_, v_projFn_6204_, v_enabled_6214_);
        if v___x_6219_ == 0 {
            let mut v___x_6220_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6221_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_projFn_6204_);
            v___x_6220_ = lean_box(0);
            v___x_6221_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_6221_, 0, v___x_6220_);
            return v___x_6221_;
        } else {
            let mut v___x_6222_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6223_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
            v___x_6222_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_6203_);
            v___x_6223_ = lean_box(0);
            v___x_6224_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v___x_6222_, v_projFn_6204_, v___x_6223_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_);
            return v___x_6224_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___boxed(
    mut v_item_6225_: *mut LeanObject,
    mut v_projFn_6226_: *mut LeanObject,
    mut v_a_6227_: *mut LeanObject,
    mut v_a_6228_: *mut LeanObject,
    mut v_a_6229_: *mut LeanObject,
    mut v_a_6230_: *mut LeanObject,
    mut v_a_6231_: *mut LeanObject,
    mut v_a_6232_: *mut LeanObject,
    mut v_a_6233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6234_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6232_);
    lean_dec_ref(v_a_6231_);
    lean_dec(v_a_6230_);
    lean_dec_ref(v_a_6229_);
    lean_dec(v_a_6228_);
    lean_dec_ref(v_a_6227_);
    lean_dec_ref(v_item_6225_);
    return v_res_6234_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(
    mut v_t_6235_: *mut LeanObject,
    mut v___y_6236_: *mut LeanObject,
    mut v___y_6237_: *mut LeanObject,
    mut v___y_6238_: *mut LeanObject,
    mut v___y_6239_: *mut LeanObject,
    mut v___y_6240_: *mut LeanObject,
    mut v___y_6241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6243_: *mut LeanObject = core::ptr::null_mut();
    v___x_6243_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_6235_, v___y_6241_);
    return v___x_6243_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___boxed(
    mut v_t_6244_: *mut LeanObject,
    mut v___y_6245_: *mut LeanObject,
    mut v___y_6246_: *mut LeanObject,
    mut v___y_6247_: *mut LeanObject,
    mut v___y_6248_: *mut LeanObject,
    mut v___y_6249_: *mut LeanObject,
    mut v___y_6250_: *mut LeanObject,
    mut v___y_6251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6252_: *mut LeanObject = core::ptr::null_mut();
    v_res_6252_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(v_t_6244_, v___y_6245_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_);
    lean_dec(v___y_6250_);
    lean_dec_ref(v___y_6249_);
    lean_dec(v___y_6248_);
    lean_dec_ref(v___y_6247_);
    lean_dec(v___y_6246_);
    lean_dec_ref(v___y_6245_);
    return v_res_6252_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_6253_: *mut LeanObject,
    mut v_constName_6254_: *mut LeanObject,
    mut v___y_6255_: *mut LeanObject,
    mut v___y_6256_: *mut LeanObject,
    mut v___y_6257_: *mut LeanObject,
    mut v___y_6258_: *mut LeanObject,
    mut v___y_6259_: *mut LeanObject,
    mut v___y_6260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6262_: *mut LeanObject = core::ptr::null_mut();
    v___x_6262_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_);
    return v___x_6262_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_6263_: *mut LeanObject,
    mut v_constName_6264_: *mut LeanObject,
    mut v___y_6265_: *mut LeanObject,
    mut v___y_6266_: *mut LeanObject,
    mut v___y_6267_: *mut LeanObject,
    mut v___y_6268_: *mut LeanObject,
    mut v___y_6269_: *mut LeanObject,
    mut v___y_6270_: *mut LeanObject,
    mut v___y_6271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6272_: *mut LeanObject = core::ptr::null_mut();
    v_res_6272_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_6263_, v_constName_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_);
    lean_dec(v___y_6270_);
    lean_dec_ref(v___y_6269_);
    lean_dec(v___y_6268_);
    lean_dec_ref(v___y_6267_);
    lean_dec(v___y_6266_);
    lean_dec_ref(v___y_6265_);
    return v_res_6272_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b1_6273_: *mut LeanObject,
    mut v_ref_6274_: *mut LeanObject,
    mut v_constName_6275_: *mut LeanObject,
    mut v___y_6276_: *mut LeanObject,
    mut v___y_6277_: *mut LeanObject,
    mut v___y_6278_: *mut LeanObject,
    mut v___y_6279_: *mut LeanObject,
    mut v___y_6280_: *mut LeanObject,
    mut v___y_6281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    v___x_6283_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_6274_, v_constName_6275_, v___y_6276_, v___y_6277_, v___y_6278_, v___y_6279_, v___y_6280_, v___y_6281_);
    return v___x_6283_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b1_6284_: *mut LeanObject,
    mut v_ref_6285_: *mut LeanObject,
    mut v_constName_6286_: *mut LeanObject,
    mut v___y_6287_: *mut LeanObject,
    mut v___y_6288_: *mut LeanObject,
    mut v___y_6289_: *mut LeanObject,
    mut v___y_6290_: *mut LeanObject,
    mut v___y_6291_: *mut LeanObject,
    mut v___y_6292_: *mut LeanObject,
    mut v___y_6293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6294_: *mut LeanObject = core::ptr::null_mut();
    v_res_6294_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_6284_, v_ref_6285_, v_constName_6286_, v___y_6287_, v___y_6288_, v___y_6289_, v___y_6290_, v___y_6291_, v___y_6292_);
    lean_dec(v___y_6292_);
    lean_dec_ref(v___y_6291_);
    lean_dec(v___y_6290_);
    lean_dec_ref(v___y_6289_);
    lean_dec(v___y_6288_);
    lean_dec_ref(v___y_6287_);
    lean_dec(v_ref_6285_);
    return v_res_6294_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(
    mut v_00_u03b1_6295_: *mut LeanObject,
    mut v_ref_6296_: *mut LeanObject,
    mut v_msg_6297_: *mut LeanObject,
    mut v_declHint_6298_: *mut LeanObject,
    mut v___y_6299_: *mut LeanObject,
    mut v___y_6300_: *mut LeanObject,
    mut v___y_6301_: *mut LeanObject,
    mut v___y_6302_: *mut LeanObject,
    mut v___y_6303_: *mut LeanObject,
    mut v___y_6304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    v___x_6306_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_6296_, v_msg_6297_, v_declHint_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
    return v___x_6306_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(
    mut v_00_u03b1_6307_: *mut LeanObject,
    mut v_ref_6308_: *mut LeanObject,
    mut v_msg_6309_: *mut LeanObject,
    mut v_declHint_6310_: *mut LeanObject,
    mut v___y_6311_: *mut LeanObject,
    mut v___y_6312_: *mut LeanObject,
    mut v___y_6313_: *mut LeanObject,
    mut v___y_6314_: *mut LeanObject,
    mut v___y_6315_: *mut LeanObject,
    mut v___y_6316_: *mut LeanObject,
    mut v___y_6317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6318_: *mut LeanObject = core::ptr::null_mut();
    v_res_6318_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_6307_, v_ref_6308_, v_msg_6309_, v_declHint_6310_, v___y_6311_, v___y_6312_, v___y_6313_, v___y_6314_, v___y_6315_, v___y_6316_);
    lean_dec(v___y_6316_);
    lean_dec_ref(v___y_6315_);
    lean_dec(v___y_6314_);
    lean_dec_ref(v___y_6313_);
    lean_dec(v___y_6312_);
    lean_dec_ref(v___y_6311_);
    lean_dec(v_ref_6308_);
    return v_res_6318_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(
    mut v_msg_6319_: *mut LeanObject,
    mut v_declHint_6320_: *mut LeanObject,
    mut v___y_6321_: *mut LeanObject,
    mut v___y_6322_: *mut LeanObject,
    mut v___y_6323_: *mut LeanObject,
    mut v___y_6324_: *mut LeanObject,
    mut v___y_6325_: *mut LeanObject,
    mut v___y_6326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    v___x_6328_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_6319_, v_declHint_6320_, v___y_6326_);
    return v___x_6328_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(
    mut v_msg_6329_: *mut LeanObject,
    mut v_declHint_6330_: *mut LeanObject,
    mut v___y_6331_: *mut LeanObject,
    mut v___y_6332_: *mut LeanObject,
    mut v___y_6333_: *mut LeanObject,
    mut v___y_6334_: *mut LeanObject,
    mut v___y_6335_: *mut LeanObject,
    mut v___y_6336_: *mut LeanObject,
    mut v___y_6337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6338_: *mut LeanObject = core::ptr::null_mut();
    v_res_6338_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_6329_, v_declHint_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_);
    lean_dec(v___y_6336_);
    lean_dec_ref(v___y_6335_);
    lean_dec(v___y_6334_);
    lean_dec_ref(v___y_6333_);
    lean_dec(v___y_6332_);
    lean_dec_ref(v___y_6331_);
    return v_res_6338_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(
    mut v_info_6339_: *mut LeanObject,
    mut v___y_6340_: *mut LeanObject,
    mut v___y_6341_: *mut LeanObject,
    mut v___y_6342_: *mut LeanObject,
    mut v___y_6343_: *mut LeanObject,
    mut v___y_6344_: *mut LeanObject,
    mut v___y_6345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    v___x_6347_ = lean_alloc_ctor(8, 1, (0) as u32);
    lean_ctor_set(v___x_6347_, 0, v_info_6339_);
    v___x_6348_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_6347_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_, v___y_6345_);
    return v___x_6348_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0___boxed(
    mut v_info_6349_: *mut LeanObject,
    mut v___y_6350_: *mut LeanObject,
    mut v___y_6351_: *mut LeanObject,
    mut v___y_6352_: *mut LeanObject,
    mut v___y_6353_: *mut LeanObject,
    mut v___y_6354_: *mut LeanObject,
    mut v___y_6355_: *mut LeanObject,
    mut v___y_6356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6357_: *mut LeanObject = core::ptr::null_mut();
    v_res_6357_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v_info_6349_, v___y_6350_, v___y_6351_, v___y_6352_, v___y_6353_, v___y_6354_, v___y_6355_);
    lean_dec(v___y_6355_);
    lean_dec_ref(v___y_6354_);
    lean_dec(v___y_6353_);
    lean_dec_ref(v___y_6352_);
    lean_dec(v___y_6351_);
    lean_dec_ref(v___y_6350_);
    return v_res_6357_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0()
-> *mut LeanObject {
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    v___x_6358_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6358_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1()
-> *mut LeanObject {
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    v___x_6359_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0,
    );
    v___x_6360_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6360_, 0, v___x_6359_);
    return v___x_6360_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2()
-> *mut LeanObject {
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    v___x_6361_ = lean_box(1);
    v___x_6362_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_6363_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1,
    );
    v___x_6364_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_6364_, 0, v___x_6363_);
    lean_ctor_set(v___x_6364_, 1, v___x_6362_);
    lean_ctor_set(v___x_6364_, 2, v___x_6361_);
    return v___x_6364_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(
    mut v_item_6365_: *mut LeanObject,
    mut v_structName_6366_: *mut LeanObject,
    mut v_a_6367_: *mut LeanObject,
    mut v_a_6368_: *mut LeanObject,
    mut v_a_6369_: *mut LeanObject,
    mut v_a_6370_: *mut LeanObject,
    mut v_a_6371_: *mut LeanObject,
    mut v_a_6372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_6376_: u8 = 0;
    v___x_6374_ = lean_st_ref_get(v_a_6372_);
    v_infoState_6375_ = lean_ctor_get(v___x_6374_, 7);
    lean_inc_ref(v_infoState_6375_);
    lean_dec(v___x_6374_);
    v_enabled_6376_ = lean_ctor_get_uint8(
        v_infoState_6375_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    lean_dec_ref(v_infoState_6375_);
    if v_enabled_6376_ == 0 {
        let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_structName_6366_);
        v___x_6377_ = lean_box(0);
        v___x_6378_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6378_, 0, v___x_6377_);
        return v___x_6378_;
    } else {
        let mut v___x_6379_: *mut LeanObject = core::ptr::null_mut();
        let mut v_env_6380_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6381_: u8 = 0;
        v___x_6379_ = lean_st_ref_get(v_a_6372_);
        v_env_6380_ = lean_ctor_get(v___x_6379_, 0);
        lean_inc_ref(v_env_6380_);
        lean_dec(v___x_6379_);
        lean_inc(v_structName_6366_);
        v___x_6381_ = l_Lean_Environment_contains(v_env_6380_, v_structName_6366_, v_enabled_6376_);
        if v___x_6381_ == 0 {
            let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_structName_6366_);
            v___x_6382_ = lean_box(0);
            v___x_6383_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_6383_, 0, v___x_6382_);
            return v___x_6383_;
        } else {
            let mut v___x_6384_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6385_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6387_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6388_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
            v___x_6384_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_6365_);
            v___x_6385_ = l_Lean_Syntax_getId(v___x_6384_);
            v___x_6386_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_6386_, 0, v___x_6385_);
            v___x_6387_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once
                ),
                _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2,
            );
            v___x_6388_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_6388_, 0, v___x_6384_);
            lean_ctor_set(v___x_6388_, 1, v___x_6386_);
            lean_ctor_set(v___x_6388_, 2, v___x_6387_);
            lean_ctor_set(v___x_6388_, 3, v_structName_6366_);
            v___x_6389_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_6388_, v_a_6367_, v_a_6368_, v_a_6369_, v_a_6370_, v_a_6371_, v_a_6372_);
            return v___x_6389_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___boxed(
    mut v_item_6390_: *mut LeanObject,
    mut v_structName_6391_: *mut LeanObject,
    mut v_a_6392_: *mut LeanObject,
    mut v_a_6393_: *mut LeanObject,
    mut v_a_6394_: *mut LeanObject,
    mut v_a_6395_: *mut LeanObject,
    mut v_a_6396_: *mut LeanObject,
    mut v_a_6397_: *mut LeanObject,
    mut v_a_6398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6399_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6397_);
    lean_dec_ref(v_a_6396_);
    lean_dec(v_a_6395_);
    lean_dec_ref(v_a_6394_);
    lean_dec(v_a_6393_);
    lean_dec_ref(v_a_6392_);
    lean_dec_ref(v_item_6390_);
    return v_res_6399_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(
    mut v_cfg_6400_: *mut LeanObject,
    mut v_withRef_6401_: *mut LeanObject,
    mut v___x_6402_: *mut LeanObject,
    mut v_oldRef_6403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    v_ref_6404_ = l_Lean_replaceRef(v_cfg_6400_, v_oldRef_6403_);
    v___x_6405_ = lean_apply_3(v_withRef_6401_, lean_box(0), v_ref_6404_, v___x_6402_);
    return v___x_6405_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed(
    mut v_cfg_6406_: *mut LeanObject,
    mut v_withRef_6407_: *mut LeanObject,
    mut v___x_6408_: *mut LeanObject,
    mut v_oldRef_6409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6410_: *mut LeanObject = core::ptr::null_mut();
    v_res_6410_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(
        v_cfg_6406_,
        v_withRef_6407_,
        v___x_6408_,
        v_oldRef_6409_,
    );
    lean_dec(v_oldRef_6409_);
    lean_dec(v_cfg_6406_);
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
    mut v_x_6414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1685__boxed_6415_: u32 = 0;
    let mut v_res_6416_: u8 = 0;
    let mut v_r_6417_: *mut LeanObject = core::ptr::null_mut();
    v_x_1685__boxed_6415_ = lean_unbox_uint32(v_x_6414_);
    lean_dec(v_x_6414_);
    v_res_6416_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(v_x_1685__boxed_6415_);
    v_r_6417_ = lean_box((v_res_6416_) as usize);
    return v_r_6417_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2(
    mut v___f_6418_: *mut LeanObject,
    mut v_s_6419_: *mut LeanObject,
    mut v___y_6420_: *mut LeanObject,
    mut v___y_6421_: *mut LeanObject,
    mut v___y_6422_: *mut LeanObject,
    mut v___y_6423_: *mut LeanObject,
    mut v___y_6424_: *mut LeanObject,
    mut v___y_6425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
    v___x_6426_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_6418_);
    v___x_6427_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_6419_, v___x_6426_, v___y_6420_, lean_box(0), lean_box(0), v___y_6423_, v___y_6424_, v___y_6425_);
    return v___x_6427_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(
    mut v___f_6429_: *mut LeanObject,
    mut v_si_6430_: *mut LeanObject,
    mut v_val_6431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: u8 = 0;
    let mut v___x_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6439_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0;
                v___x_6440_ = lean_unsigned_to_nat(0);
                v___x_6441_ = lean_string_utf8_byte_size(v_val_6431_);
                lean_inc_ref(v_val_6431_);
                v___x_6442_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_6442_, 0, v_val_6431_);
                lean_ctor_set(v___x_6442_, 1, v___x_6440_);
                lean_ctor_set(v___x_6442_, 2, v___x_6441_);
                v___x_6443_ =
                    l_String_Slice_contains___redArg(v___f_6429_, v___x_6442_, v___f_6439_);
                if v___x_6443_ == 0 {
                    v___x_6444_ = lean_box(0);
                    lean_inc_ref(v_val_6431_);
                    v___x_6445_ = l_Lean_Name_str___override(v___x_6444_, v_val_6431_);
                    v___y_6433_ = v___x_6445_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_val_6431_);
                    v___x_6446_ = l_String_toName(v_val_6431_);
                    v___y_6433_ = v___x_6446_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6434_ = lean_unsigned_to_nat(0);
                v___x_6435_ = lean_string_utf8_byte_size(v_val_6431_);
                v___x_6436_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_6436_, 0, v_val_6431_);
                lean_ctor_set(v___x_6436_, 1, v___x_6434_);
                lean_ctor_set(v___x_6436_, 2, v___x_6435_);
                v___x_6437_ = lean_box(0);
                v___x_6438_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_6438_, 0, v_si_6430_);
                lean_ctor_set(v___x_6438_, 1, v___x_6436_);
                lean_ctor_set(v___x_6438_, 2, v___y_6433_);
                lean_ctor_set(v___x_6438_, 3, v___x_6437_);
                return v___x_6438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(
    mut v_atomAsIdent_6447_: *mut LeanObject,
    mut v_stx_6448_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_stx_6448_) {
        3 => {
            let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_atomAsIdent_6447_);
            v___x_6449_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_6449_, 0, v_stx_6448_);
            return v___x_6449_;
        }
        2 => {
            let mut v_info_6450_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_6451_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6452_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6453_: *mut LeanObject = core::ptr::null_mut();
            v_info_6450_ = lean_ctor_get(v_stx_6448_, 0);
            lean_inc(v_info_6450_);
            v_val_6451_ = lean_ctor_get(v_stx_6448_, 1);
            lean_inc_ref(v_val_6451_);
            lean_dec_ref_known(v_stx_6448_, 2);
            v___x_6452_ = lean_apply_2(v_atomAsIdent_6447_, v_info_6450_, v_val_6451_);
            v___x_6453_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_6453_, 0, v___x_6452_);
            return v___x_6453_;
        }
        _ => {
            let mut v___x_6454_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_stx_6448_);
            lean_dec_ref(v_atomAsIdent_6447_);
            v___x_6454_ = lean_box(0);
            return v___x_6454_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___redArg(
    mut v_inst_6478_: *mut LeanObject,
    mut v_inst_6479_: *mut LeanObject,
    mut v_init_6480_: *mut LeanObject,
    mut v_cfgs_6481_: *mut LeanObject,
    mut v_k_6482_: *mut LeanObject,
    mut v_onErr_6483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: u8 = 0;
    v___x_6484_ = lean_unsigned_to_nat(0);
    v___x_6485_ = lean_array_get_size(v_cfgs_6481_);
    v___x_6486_ = lean_nat_dec_lt(v___x_6484_, v___x_6485_);
    if v___x_6486_ == 0 {
        let mut v_toApplicative_6487_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_6488_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_onErr_6483_);
        lean_dec(v_k_6482_);
        lean_dec_ref(v_cfgs_6481_);
        lean_dec_ref(v_inst_6479_);
        v_toApplicative_6487_ = lean_ctor_get(v_inst_6478_, 0);
        lean_inc_ref(v_toApplicative_6487_);
        lean_dec_ref(v_inst_6478_);
        v_toPure_6488_ = lean_ctor_get(v_toApplicative_6487_, 1);
        lean_inc(v_toPure_6488_);
        lean_dec_ref(v_toApplicative_6487_);
        v___x_6489_ = lean_apply_2(v_toPure_6488_, lean_box(0), v_init_6480_);
        return v___x_6489_;
    } else {
        let mut v___f_6490_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6491_: u8 = 0;
        lean_inc_ref(v_inst_6478_);
        v___f_6490_ = lean_alloc_closure(
            l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0 as *mut core::ffi::c_void,
            6,
            4,
        );
        lean_closure_set(v___f_6490_, 0, v_inst_6478_);
        lean_closure_set(v___f_6490_, 1, v_inst_6479_);
        lean_closure_set(v___f_6490_, 2, v_k_6482_);
        lean_closure_set(v___f_6490_, 3, v_onErr_6483_);
        v___x_6491_ = lean_nat_dec_le(v___x_6485_, v___x_6485_);
        if v___x_6491_ == 0 {
            if v___x_6486_ == 0 {
                let mut v_toApplicative_6492_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_6493_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_6490_);
                lean_dec_ref(v_cfgs_6481_);
                v_toApplicative_6492_ = lean_ctor_get(v_inst_6478_, 0);
                lean_inc_ref(v_toApplicative_6492_);
                lean_dec_ref(v_inst_6478_);
                v_toPure_6493_ = lean_ctor_get(v_toApplicative_6492_, 1);
                lean_inc(v_toPure_6493_);
                lean_dec_ref(v_toApplicative_6492_);
                v___x_6494_ = lean_apply_2(v_toPure_6493_, lean_box(0), v_init_6480_);
                return v___x_6494_;
            } else {
                let mut v___x_6495_: usize = 0;
                let mut v___x_6496_: usize = 0;
                let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
                v___x_6495_ = 0usize;
                v___x_6496_ = lean_usize_of_nat(v___x_6485_);
                v___x_6497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
            v___x_6498_ = 0usize;
            v___x_6499_ = lean_usize_of_nat(v___x_6485_);
            v___x_6500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_inst_6501_: *mut LeanObject,
    mut v_inst_6502_: *mut LeanObject,
    mut v_init_6503_: *mut LeanObject,
    mut v_cfg_6504_: *mut LeanObject,
    mut v_k_6505_: *mut LeanObject,
    mut v_onErr_6506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withRef_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: u8 = 0;
    let mut v___x_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: u8 = 0;
    let mut v___f_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_atomAsIdent_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: u8 = 0;
    let mut v_info_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6551_: u8 = 0;
    let mut v___x_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: u8 = 0;
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: u8 = 0;
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: u8 = 0;
    let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: u8 = 0;
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: u8 = 0;
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6525_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1;
                lean_inc(v_cfg_6504_);
                v___x_6526_ = l_Lean_Syntax_isOfKind(v_cfg_6504_, v___x_6525_);
                if v___x_6526_ == 0 {
                    v___x_6527_ = l_Lean_Syntax_getNumArgs(v_cfg_6504_);
                    v___x_6528_ = lean_unsigned_to_nat(1);
                    v___x_6529_ = lean_nat_dec_eq(v___x_6527_, v___x_6528_);
                    if v___x_6529_ == 0 {
                        v___f_6530_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3;
                        v_atomAsIdent_6531_ =
                            l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4;
                        v___x_6532_ = lean_nat_dec_le(v___x_6528_, v___x_6527_);
                        if v___x_6532_ == 0 {
                            lean_dec(v___x_6527_);
                            if lean_obj_tag(v_cfg_6504_) == 2 {
                                lean_dec(v_onErr_6506_);
                                lean_dec_ref(v_inst_6502_);
                                lean_dec_ref(v_inst_6501_);
                                v_info_6533_ = lean_ctor_get(v_cfg_6504_, 0);
                                v_val_6534_ = lean_ctor_get(v_cfg_6504_, 1);
                                lean_inc_ref(v_val_6534_);
                                lean_inc(v_info_6533_);
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
                                v___x_6541_ = lean_box(0);
                                lean_inc(v___x_6535_);
                                v___x_6542_ =
                                    l_Lean_Syntax_identComponents(v___x_6535_, v___x_6541_);
                                v___x_6543_ = lean_box(0);
                                v___x_6544_ = lean_alloc_ctor(0, 7, (0) as u32);
                                lean_ctor_set(v___x_6544_, 0, v_cfg_6504_);
                                lean_ctor_set(v___x_6544_, 1, v___x_6535_);
                                lean_ctor_set(v___x_6544_, 2, v___x_6537_);
                                lean_ctor_set(v___x_6544_, 3, v___x_6538_);
                                lean_ctor_set(v___x_6544_, 4, v___x_6540_);
                                lean_ctor_set(v___x_6544_, 5, v___x_6542_);
                                lean_ctor_set(v___x_6544_, 6, v___x_6543_);
                                v___x_6545_ = lean_apply_2(v_k_6505_, v_init_6503_, v___x_6544_);
                                return v___x_6545_;
                            } else {
                                lean_dec(v_k_6505_);
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_6546_ = lean_unsigned_to_nat(0);
                            v___x_6547_ = l_Lean_Syntax_getArg(v_cfg_6504_, v___x_6546_);
                            if lean_obj_tag(v___x_6547_) == 2 {
                                v_val_6548_ = lean_ctor_get(v___x_6547_, 1);
                                lean_inc_ref(v_val_6548_);
                                v___x_6562_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11;
                                v___x_6563_ = lean_string_dec_eq(v_val_6548_, v___x_6562_);
                                if v___x_6563_ == 0 {
                                    v___x_6564_ =
                                        l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12;
                                    v___x_6565_ = lean_string_dec_eq(v_val_6548_, v___x_6564_);
                                    if v___x_6565_ == 0 {
                                        lean_dec_ref_known(v___x_6547_, 2);
                                        v___x_6566_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13;
                                        v___x_6567_ = lean_string_dec_eq(v_val_6548_, v___x_6566_);
                                        lean_dec_ref(v_val_6548_);
                                        if v___x_6567_ == 0 {
                                            lean_dec(v___x_6527_);
                                            lean_dec(v_k_6505_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_6568_ = lean_unsigned_to_nat(5);
                                            v___x_6569_ = lean_nat_dec_le(v___x_6527_, v___x_6568_);
                                            lean_dec(v___x_6527_);
                                            if v___x_6569_ == 0 {
                                                lean_dec(v_k_6505_);
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_6570_ =
                                                    l_Lean_Syntax_getArg(v_cfg_6504_, v___x_6528_);
                                                v___x_6571_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_6531_, v___x_6570_);
                                                if lean_obj_tag(v___x_6571_) == 1 {
                                                    lean_dec(v_onErr_6506_);
                                                    lean_dec_ref(v_inst_6502_);
                                                    lean_dec_ref(v_inst_6501_);
                                                    v_val_6572_ = lean_ctor_get(v___x_6571_, 0);
                                                    lean_inc_n(v_val_6572_, 2);
                                                    lean_dec_ref_known(v___x_6571_, 1);
                                                    v___x_6573_ = lean_unsigned_to_nat(3);
                                                    v___x_6574_ = l_Lean_Syntax_getArg(
                                                        v_cfg_6504_,
                                                        v___x_6573_,
                                                    );
                                                    v___x_6575_ = lean_box(0);
                                                    v___x_6576_ = l_Lean_TSyntax_getId(v_val_6572_);
                                                    v___x_6577_ =
                                                        lean_erase_macro_scopes(v___x_6576_);
                                                    v___x_6578_ = l_Lean_Syntax_identComponents(
                                                        v_val_6572_,
                                                        v___x_6575_,
                                                    );
                                                    v___x_6579_ = lean_box(0);
                                                    v___x_6580_ = lean_alloc_ctor(0, 7, (0) as u32);
                                                    lean_ctor_set(v___x_6580_, 0, v_cfg_6504_);
                                                    lean_ctor_set(v___x_6580_, 1, v_val_6572_);
                                                    lean_ctor_set(v___x_6580_, 2, v___x_6574_);
                                                    lean_ctor_set(v___x_6580_, 3, v___x_6575_);
                                                    lean_ctor_set(v___x_6580_, 4, v___x_6577_);
                                                    lean_ctor_set(v___x_6580_, 5, v___x_6578_);
                                                    lean_ctor_set(v___x_6580_, 6, v___x_6579_);
                                                    v___x_6581_ = lean_apply_2(
                                                        v_k_6505_,
                                                        v_init_6503_,
                                                        v___x_6580_,
                                                    );
                                                    return v___x_6581_;
                                                } else {
                                                    lean_dec(v___x_6571_);
                                                    lean_dec(v_k_6505_);
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v_val_6548_);
                                        v___x_6582_ = lean_box((v___x_6529_) as usize);
                                        v___x_6583_ = lean_alloc_ctor(1, 1, (0) as u32);
                                        lean_ctor_set(v___x_6583_, 0, v___x_6582_);
                                        v___y_6550_ = v___x_6583_;
                                        v_val_6551_ = v___x_6529_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_val_6548_);
                                    v___x_6584_ = lean_box((v___x_6563_) as usize);
                                    v___x_6585_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_6585_, 0, v___x_6584_);
                                    v___y_6550_ = v___x_6585_;
                                    v_val_6551_ = v___x_6563_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_6547_);
                                lean_dec(v___x_6527_);
                                lean_dec(v_k_6505_);
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_6527_);
                        v___x_6586_ = lean_unsigned_to_nat(0);
                        v___x_6587_ = l_Lean_Syntax_getArg(v_cfg_6504_, v___x_6586_);
                        lean_dec(v_cfg_6504_);
                        v_cfg_6504_ = v___x_6587_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_6589_ = l_Lean_Syntax_getArgs(v_cfg_6504_);
                    lean_dec(v_cfg_6504_);
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
                v___x_6513_ = lean_box(0);
                lean_inc(v___y_6508_);
                v___x_6514_ = l_Lean_Syntax_identComponents(v___y_6508_, v___x_6513_);
                v___x_6515_ = lean_box(0);
                v___x_6516_ = lean_alloc_ctor(0, 7, (0) as u32);
                lean_ctor_set(v___x_6516_, 0, v_cfg_6504_);
                lean_ctor_set(v___x_6516_, 1, v___y_6508_);
                lean_ctor_set(v___x_6516_, 2, v___y_6510_);
                lean_ctor_set(v___x_6516_, 3, v___y_6509_);
                lean_ctor_set(v___x_6516_, 4, v___x_6512_);
                lean_ctor_set(v___x_6516_, 5, v___x_6514_);
                lean_ctor_set(v___x_6516_, 6, v___x_6515_);
                v___x_6517_ = lean_apply_2(v_k_6505_, v_init_6503_, v___x_6516_);
                return v___x_6517_;
            }
            2 => {
                v_toBind_6519_ = lean_ctor_get(v_inst_6501_, 1);
                lean_inc(v_toBind_6519_);
                lean_dec_ref(v_inst_6501_);
                v_getRef_6520_ = lean_ctor_get(v_inst_6502_, 0);
                lean_inc(v_getRef_6520_);
                v_withRef_6521_ = lean_ctor_get(v_inst_6502_, 1);
                lean_inc(v_withRef_6521_);
                lean_dec_ref(v_inst_6502_);
                lean_inc(v_cfg_6504_);
                v___x_6522_ = lean_apply_2(v_onErr_6506_, v_init_6503_, v_cfg_6504_);
                v___f_6523_ = lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_6523_, 0, v_cfg_6504_);
                lean_closure_set(v___f_6523_, 1, v_withRef_6521_);
                lean_closure_set(v___f_6523_, 2, v___x_6522_);
                v___x_6524_ = lean_apply_4(
                    v_toBind_6519_,
                    lean_box(0),
                    lean_box(0),
                    v_getRef_6520_,
                    v___f_6523_,
                );
                return v___x_6524_;
            }
            3 => {
                v___x_6552_ = lean_unsigned_to_nat(2);
                v___x_6553_ = lean_nat_dec_eq(v___x_6527_, v___x_6552_);
                lean_dec(v___x_6527_);
                if v___x_6553_ == 0 {
                    lean_dec(v___y_6550_);
                    lean_dec_ref_known(v___x_6547_, 2);
                    lean_dec(v_k_6505_);
                    state = 2;
                    continue;
                } else {
                    v___x_6554_ = l_Lean_Syntax_getArg(v_cfg_6504_, v___x_6528_);
                    v___x_6555_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(
                        v_atomAsIdent_6531_,
                        v___x_6554_,
                    );
                    if lean_obj_tag(v___x_6555_) == 1 {
                        lean_dec(v_onErr_6506_);
                        lean_dec_ref(v_inst_6502_);
                        lean_dec_ref(v_inst_6501_);
                        if v_val_6551_ == 0 {
                            v_val_6556_ = lean_ctor_get(v___x_6555_, 0);
                            lean_inc(v_val_6556_);
                            lean_dec_ref_known(v___x_6555_, 1);
                            v___x_6557_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10;
                            v___x_6558_ =
                                l_Lean_mkCIdentFrom(v___x_6547_, v___x_6557_, v___x_6529_);
                            lean_dec_ref_known(v___x_6547_, 2);
                            v___y_6508_ = v_val_6556_;
                            v___y_6509_ = v___y_6550_;
                            v___y_6510_ = v___x_6558_;
                            state = 1;
                            continue;
                        } else {
                            v_val_6559_ = lean_ctor_get(v___x_6555_, 0);
                            lean_inc(v_val_6559_);
                            lean_dec_ref_known(v___x_6555_, 1);
                            v___x_6560_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7;
                            v___x_6561_ =
                                l_Lean_mkCIdentFrom(v___x_6547_, v___x_6560_, v___x_6529_);
                            lean_dec_ref_known(v___x_6547_, 2);
                            v___y_6508_ = v_val_6559_;
                            v___y_6509_ = v___y_6550_;
                            v___y_6510_ = v___x_6561_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_6555_);
                        lean_dec(v___y_6550_);
                        lean_dec_ref_known(v___x_6547_, 2);
                        lean_dec(v_k_6505_);
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
    mut v_inst_6591_: *mut LeanObject,
    mut v_inst_6592_: *mut LeanObject,
    mut v_k_6593_: *mut LeanObject,
    mut v_onErr_6594_: *mut LeanObject,
    mut v_x_6595_: *mut LeanObject,
    mut v_cfg_x27_6596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6597_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6598_: *mut LeanObject,
    mut v_m_6599_: *mut LeanObject,
    mut v_inst_6600_: *mut LeanObject,
    mut v_inst_6601_: *mut LeanObject,
    mut v_init_6602_: *mut LeanObject,
    mut v_cfg_6603_: *mut LeanObject,
    mut v_k_6604_: *mut LeanObject,
    mut v_onErr_6605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6607_: *mut LeanObject,
    mut v_m_6608_: *mut LeanObject,
    mut v_inst_6609_: *mut LeanObject,
    mut v_inst_6610_: *mut LeanObject,
    mut v_init_6611_: *mut LeanObject,
    mut v_cfgs_6612_: *mut LeanObject,
    mut v_k_6613_: *mut LeanObject,
    mut v_onErr_6614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_6626_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_6626_) == 1 {
        let mut v_pre_6627_: *mut LeanObject = core::ptr::null_mut();
        v_pre_6627_ = lean_ctor_get(v_x_6626_, 0);
        match lean_obj_tag(v_pre_6627_) {
            1 => {
                let mut v_pre_6628_: *mut LeanObject = core::ptr::null_mut();
                v_pre_6628_ = lean_ctor_get(v_pre_6627_, 0);
                match lean_obj_tag(v_pre_6628_) {
                    0 => {
                        let mut v_str_6629_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_6630_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_6632_: u8 = 0;
                        v_str_6629_ = lean_ctor_get(v_x_6626_, 1);
                        v_str_6630_ = lean_ctor_get(v_pre_6627_, 1);
                        v___x_6631_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0;
                        v___x_6632_ = lean_string_dec_eq(v_str_6630_, v___x_6631_);
                        if v___x_6632_ == 0 {
                            let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_6634_: u8 = 0;
                            v___x_6633_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1;
                            v___x_6634_ = lean_string_dec_eq(v_str_6630_, v___x_6633_);
                            if v___x_6634_ == 0 {
                                return v___y_6624_;
                            } else {
                                let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_6639_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_6639_ = lean_ctor_get(v_pre_6628_, 0);
                        if lean_obj_tag(v_pre_6639_) == 0 {
                            let mut v_str_6640_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_6641_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_6642_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_6643_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_6644_: u8 = 0;
                            v_str_6640_ = lean_ctor_get(v_x_6626_, 1);
                            v_str_6641_ = lean_ctor_get(v_pre_6627_, 1);
                            v_str_6642_ = lean_ctor_get(v_pre_6628_, 1);
                            v___x_6643_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4;
                            v___x_6644_ = lean_string_dec_eq(v_str_6642_, v___x_6643_);
                            if v___x_6644_ == 0 {
                                return v___y_6624_;
                            } else {
                                let mut v___x_6645_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_6646_: u8 = 0;
                                v___x_6645_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5;
                                v___x_6646_ = lean_string_dec_eq(v_str_6641_, v___x_6645_);
                                if v___x_6646_ == 0 {
                                    return v___y_6624_;
                                } else {
                                    let mut v___x_6647_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_6649_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6651_: u8 = 0;
                v_str_6649_ = lean_ctor_get(v_x_6626_, 1);
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
    mut v___y_6652_: *mut LeanObject,
    mut v_suppressElabErrors_6653_: *mut LeanObject,
    mut v_x_6654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6697__boxed_6655_: u8 = 0;
    let mut v_suppressElabErrors_boxed_6656_: u8 = 0;
    let mut v_res_6657_: u8 = 0;
    let mut v_r_6658_: *mut LeanObject = core::ptr::null_mut();
    v___y_6697__boxed_6655_ = (lean_unbox(v___y_6652_) as u8);
    v_suppressElabErrors_boxed_6656_ = (lean_unbox(v_suppressElabErrors_6653_) as u8);
    v_res_6657_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(v___y_6697__boxed_6655_, v_suppressElabErrors_boxed_6656_, v_x_6654_);
    lean_dec(v_x_6654_);
    v_r_6658_ = lean_box((v_res_6657_) as usize);
    return v_r_6658_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(
    mut v_ref_6659_: *mut LeanObject,
    mut v_msgData_6660_: *mut LeanObject,
    mut v_severity_6661_: u8,
    mut v_isSilent_6662_: u8,
    mut v___y_6663_: *mut LeanObject,
    mut v___y_6664_: *mut LeanObject,
    mut v___y_6665_: *mut LeanObject,
    mut v___y_6666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6672_: u8 = 0;
    let mut v___y_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6674_: u8 = 0;
    let mut v___y_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6692_: u8 = 0;
    let mut v___x_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6703_: u8 = 0;
    let mut v___y_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6707_: u8 = 0;
    let mut v___y_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6709_: u8 = 0;
    let mut v___y_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6711_: u8 = 0;
    let mut v___y_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6718_: u8 = 0;
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: u8 = 0;
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6728_: u8 = 0;
    let mut v___y_6730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6733_: u8 = 0;
    let mut v___y_6734_: u8 = 0;
    let mut v___y_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6736_: u8 = 0;
    let mut v___y_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6742_: u8 = 0;
    let mut v___y_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6744_: u8 = 0;
    let mut v___y_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6747_: u8 = 0;
    let mut v_ref_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: u8 = 0;
    let mut v___y_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6756_: u8 = 0;
    let mut v___y_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6759_: u8 = 0;
    let mut v___y_6760_: u8 = 0;
    let mut v___y_6762_: u8 = 0;
    let mut v_fileName_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6767_: u8 = 0;
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: u8 = 0;
    let mut v___x_6772_: u8 = 0;
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: u8 = 0;
    let mut v___x_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_6660_);
                    v___x_6778_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6660_);
                    v___y_6762_ = v___x_6778_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_6678_ = lean_st_ref_take(v___y_6677_);
                v_currNamespace_6679_ = lean_ctor_get(v___y_6676_, 6);
                v_openDecls_6680_ = lean_ctor_get(v___y_6676_, 7);
                v_env_6681_ = lean_ctor_get(v___x_6678_, 0);
                v_nextMacroScope_6682_ = lean_ctor_get(v___x_6678_, 1);
                v_ngen_6683_ = lean_ctor_get(v___x_6678_, 2);
                v_auxDeclNGen_6684_ = lean_ctor_get(v___x_6678_, 3);
                v_traceState_6685_ = lean_ctor_get(v___x_6678_, 4);
                v_cache_6686_ = lean_ctor_get(v___x_6678_, 5);
                v_messages_6687_ = lean_ctor_get(v___x_6678_, 6);
                v_infoState_6688_ = lean_ctor_get(v___x_6678_, 7);
                v_snapshotTasks_6689_ = lean_ctor_get(v___x_6678_, 8);
                v_isSharedCheck_6703_ = (!lean_is_exclusive(v___x_6678_)) as u8;
                if v_isSharedCheck_6703_ == 0 {
                    v___x_6691_ = v___x_6678_;
                    v_isShared_6692_ = v_isSharedCheck_6703_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6689_);
                    lean_inc(v_infoState_6688_);
                    lean_inc(v_messages_6687_);
                    lean_inc(v_cache_6686_);
                    lean_inc(v_traceState_6685_);
                    lean_inc(v_auxDeclNGen_6684_);
                    lean_inc(v_ngen_6683_);
                    lean_inc(v_nextMacroScope_6682_);
                    lean_inc(v_env_6681_);
                    lean_dec(v___x_6678_);
                    v___x_6691_ = lean_box(0);
                    v_isShared_6692_ = v_isSharedCheck_6703_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_6680_);
                lean_inc(v_currNamespace_6679_);
                v___x_6693_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6693_, 0, v_currNamespace_6679_);
                lean_ctor_set(v___x_6693_, 1, v_openDecls_6680_);
                v___x_6694_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_6694_, 0, v___x_6693_);
                lean_ctor_set(v___x_6694_, 1, v___y_6669_);
                lean_inc_ref(v___y_6671_);
                lean_inc_ref(v___y_6673_);
                v___x_6695_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_6695_, 0, v___y_6673_);
                lean_ctor_set(v___x_6695_, 1, v___y_6670_);
                lean_ctor_set(v___x_6695_, 2, v___y_6675_);
                lean_ctor_set(v___x_6695_, 3, v___y_6671_);
                lean_ctor_set(v___x_6695_, 4, v___x_6694_);
                lean_ctor_set_uint8(
                    v___x_6695_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_6672_,
                );
                lean_ctor_set_uint8(
                    v___x_6695_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_6674_,
                );
                lean_ctor_set_uint8(
                    v___x_6695_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_6662_,
                );
                v___x_6696_ = l_Lean_MessageLog_add(v___x_6695_, v_messages_6687_);
                if v_isShared_6692_ == 0 {
                    lean_ctor_set(v___x_6691_, 6, v___x_6696_);
                    v___x_6698_ = v___x_6691_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6702_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6702_, 0, v_env_6681_);
                    lean_ctor_set(v_reuseFailAlloc_6702_, 1, v_nextMacroScope_6682_);
                    lean_ctor_set(v_reuseFailAlloc_6702_, 2, v_ngen_6683_);
                    lean_ctor_set(v_reuseFailAlloc_6702_, 3, v_auxDeclNGen_6684_);
                    lean_ctor_set(v_reuseFailAlloc_6702_, 4, v_traceState_6685_);
                    lean_ctor_set(v_reuseFailAlloc_6702_, 5, v_cache_6686_);
                    lean_ctor_set(v_reuseFailAlloc_6702_, 6, v___x_6696_);
                    lean_ctor_set(v_reuseFailAlloc_6702_, 7, v_infoState_6688_);
                    lean_ctor_set(v_reuseFailAlloc_6702_, 8, v_snapshotTasks_6689_);
                    v___x_6698_ = v_reuseFailAlloc_6702_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6699_ = lean_st_ref_set(v___y_6677_, v___x_6698_);
                v___x_6700_ = lean_box(0);
                v___x_6701_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6701_, 0, v___x_6700_);
                return v___x_6701_;
            }
            4 => {
                v___x_6713_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_6660_,
                    );
                v___x_6714_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v___x_6713_, v___y_6663_, v___y_6664_, v___y_6665_, v___y_6666_);
                v_a_6715_ = lean_ctor_get(v___x_6714_, 0);
                v_isSharedCheck_6728_ = (!lean_is_exclusive(v___x_6714_)) as u8;
                if v_isSharedCheck_6728_ == 0 {
                    v___x_6717_ = v___x_6714_;
                    v_isShared_6718_ = v_isSharedCheck_6728_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_6715_);
                    lean_dec(v___x_6714_);
                    v___x_6717_ = lean_box(0);
                    v_isShared_6718_ = v_isSharedCheck_6728_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_6708_, 2);
                v___x_6719_ = l_Lean_FileMap_toPosition(v___y_6708_, v___y_6706_);
                lean_dec(v___y_6706_);
                v___x_6720_ = l_Lean_FileMap_toPosition(v___y_6708_, v___y_6712_);
                lean_dec(v___y_6712_);
                v___x_6721_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6721_, 0, v___x_6720_);
                v___x_6722_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29;
                if v___y_6707_ == 0 {
                    lean_del_object(v___x_6717_);
                    lean_dec_ref(v___y_6705_);
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
                    lean_inc(v_a_6715_);
                    v___x_6723_ = l_Lean_MessageData_hasTag(v___y_6705_, v_a_6715_);
                    if v___x_6723_ == 0 {
                        lean_dec_ref_known(v___x_6721_, 1);
                        lean_dec_ref(v___x_6719_);
                        lean_dec(v_a_6715_);
                        v___x_6724_ = lean_box(0);
                        if v_isShared_6718_ == 0 {
                            lean_ctor_set(v___x_6717_, 0, v___x_6724_);
                            v___x_6726_ = v___x_6717_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_6727_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6727_, 0, v___x_6724_);
                            v___x_6726_ = v_reuseFailAlloc_6727_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_6717_);
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
                lean_dec(v___y_6731_);
                if lean_obj_tag(v___x_6738_) == 0 {
                    lean_inc(v___y_6737_);
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
                    v_val_6739_ = lean_ctor_get(v___x_6738_, 0);
                    lean_inc(v_val_6739_);
                    lean_dec_ref_known(v___x_6738_, 1);
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
                if lean_obj_tag(v___x_6749_) == 0 {
                    v___x_6750_ = lean_unsigned_to_nat(0);
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
                    v_val_6751_ = lean_ctor_get(v___x_6749_, 0);
                    lean_inc(v_val_6751_);
                    lean_dec_ref_known(v___x_6749_, 1);
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
                    v_fileName_6763_ = lean_ctor_get(v___y_6665_, 0);
                    v_fileMap_6764_ = lean_ctor_get(v___y_6665_, 1);
                    v_options_6765_ = lean_ctor_get(v___y_6665_, 2);
                    v_ref_6766_ = lean_ctor_get(v___y_6665_, 5);
                    v_suppressElabErrors_6767_ = lean_ctor_get_uint8(
                        v___y_6665_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_6768_ = lean_box((v___y_6762_) as usize);
                    v___x_6769_ = lean_box((v_suppressElabErrors_6767_) as usize);
                    v___f_6770_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_6770_, 0, v___x_6768_);
                    lean_closure_set(v___f_6770_, 1, v___x_6769_);
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
                    lean_dec_ref(v_msgData_6660_);
                    v___x_6775_ = lean_box(0);
                    v___x_6776_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6776_, 0, v___x_6775_);
                    return v___x_6776_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_6779_: *mut LeanObject,
    mut v_msgData_6780_: *mut LeanObject,
    mut v_severity_6781_: *mut LeanObject,
    mut v_isSilent_6782_: *mut LeanObject,
    mut v___y_6783_: *mut LeanObject,
    mut v___y_6784_: *mut LeanObject,
    mut v___y_6785_: *mut LeanObject,
    mut v___y_6786_: *mut LeanObject,
    mut v___y_6787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_6788_: u8 = 0;
    let mut v_isSilent_boxed_6789_: u8 = 0;
    let mut v_res_6790_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_6788_ = (lean_unbox(v_severity_6781_) as u8);
    v_isSilent_boxed_6789_ = (lean_unbox(v_isSilent_6782_) as u8);
    v_res_6790_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_6779_, v_msgData_6780_, v_severity_boxed_6788_, v_isSilent_boxed_6789_, v___y_6783_, v___y_6784_, v___y_6785_, v___y_6786_);
    lean_dec(v___y_6786_);
    lean_dec_ref(v___y_6785_);
    lean_dec(v___y_6784_);
    lean_dec_ref(v___y_6783_);
    lean_dec(v_ref_6779_);
    return v_res_6790_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(
    mut v_msgData_6791_: *mut LeanObject,
    mut v_severity_6792_: u8,
    mut v_isSilent_6793_: u8,
    mut v___y_6794_: *mut LeanObject,
    mut v___y_6795_: *mut LeanObject,
    mut v___y_6796_: *mut LeanObject,
    mut v___y_6797_: *mut LeanObject,
    mut v___y_6798_: *mut LeanObject,
    mut v___y_6799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut LeanObject = core::ptr::null_mut();
    v_ref_6801_ = lean_ctor_get(v___y_6798_, 5);
    v___x_6802_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_6801_, v_msgData_6791_, v_severity_6792_, v_isSilent_6793_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_);
    return v___x_6802_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3___boxed(
    mut v_msgData_6803_: *mut LeanObject,
    mut v_severity_6804_: *mut LeanObject,
    mut v_isSilent_6805_: *mut LeanObject,
    mut v___y_6806_: *mut LeanObject,
    mut v___y_6807_: *mut LeanObject,
    mut v___y_6808_: *mut LeanObject,
    mut v___y_6809_: *mut LeanObject,
    mut v___y_6810_: *mut LeanObject,
    mut v___y_6811_: *mut LeanObject,
    mut v___y_6812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_6813_: u8 = 0;
    let mut v_isSilent_boxed_6814_: u8 = 0;
    let mut v_res_6815_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_6813_ = (lean_unbox(v_severity_6804_) as u8);
    v_isSilent_boxed_6814_ = (lean_unbox(v_isSilent_6805_) as u8);
    v_res_6815_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_6803_, v_severity_boxed_6813_, v_isSilent_boxed_6814_, v___y_6806_, v___y_6807_, v___y_6808_, v___y_6809_, v___y_6810_, v___y_6811_);
    lean_dec(v___y_6811_);
    lean_dec_ref(v___y_6810_);
    lean_dec(v___y_6809_);
    lean_dec_ref(v___y_6808_);
    lean_dec(v___y_6807_);
    lean_dec_ref(v___y_6806_);
    return v_res_6815_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(
    mut v_msgData_6816_: *mut LeanObject,
    mut v___y_6817_: *mut LeanObject,
    mut v___y_6818_: *mut LeanObject,
    mut v___y_6819_: *mut LeanObject,
    mut v___y_6820_: *mut LeanObject,
    mut v___y_6821_: *mut LeanObject,
    mut v___y_6822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6824_: u8 = 0;
    let mut v___x_6825_: u8 = 0;
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    v___x_6824_ = 2;
    v___x_6825_ = 0;
    v___x_6826_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_6816_, v___x_6824_, v___x_6825_, v___y_6817_, v___y_6818_, v___y_6819_, v___y_6820_, v___y_6821_, v___y_6822_);
    return v___x_6826_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1___boxed(
    mut v_msgData_6827_: *mut LeanObject,
    mut v___y_6828_: *mut LeanObject,
    mut v___y_6829_: *mut LeanObject,
    mut v___y_6830_: *mut LeanObject,
    mut v___y_6831_: *mut LeanObject,
    mut v___y_6832_: *mut LeanObject,
    mut v___y_6833_: *mut LeanObject,
    mut v___y_6834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6835_: *mut LeanObject = core::ptr::null_mut();
    v_res_6835_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v_msgData_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_, v___y_6833_);
    lean_dec(v___y_6833_);
    lean_dec_ref(v___y_6832_);
    lean_dec(v___y_6831_);
    lean_dec_ref(v___y_6830_);
    lean_dec(v___y_6829_);
    lean_dec_ref(v___y_6828_);
    return v_res_6835_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(
    mut v_ref_6836_: *mut LeanObject,
    mut v_msgData_6837_: *mut LeanObject,
    mut v___y_6838_: *mut LeanObject,
    mut v___y_6839_: *mut LeanObject,
    mut v___y_6840_: *mut LeanObject,
    mut v___y_6841_: *mut LeanObject,
    mut v___y_6842_: *mut LeanObject,
    mut v___y_6843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6845_: u8 = 0;
    let mut v___x_6846_: u8 = 0;
    let mut v___x_6847_: *mut LeanObject = core::ptr::null_mut();
    v___x_6845_ = 2;
    v___x_6846_ = 0;
    v___x_6847_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_6836_, v_msgData_6837_, v___x_6845_, v___x_6846_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_);
    return v___x_6847_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0___boxed(
    mut v_ref_6848_: *mut LeanObject,
    mut v_msgData_6849_: *mut LeanObject,
    mut v___y_6850_: *mut LeanObject,
    mut v___y_6851_: *mut LeanObject,
    mut v___y_6852_: *mut LeanObject,
    mut v___y_6853_: *mut LeanObject,
    mut v___y_6854_: *mut LeanObject,
    mut v___y_6855_: *mut LeanObject,
    mut v___y_6856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6857_: *mut LeanObject = core::ptr::null_mut();
    v_res_6857_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_6848_, v_msgData_6849_, v___y_6850_, v___y_6851_, v___y_6852_, v___y_6853_, v___y_6854_, v___y_6855_);
    lean_dec(v___y_6855_);
    lean_dec_ref(v___y_6854_);
    lean_dec(v___y_6853_);
    lean_dec_ref(v___y_6852_);
    lean_dec(v___y_6851_);
    lean_dec_ref(v___y_6850_);
    lean_dec(v_ref_6848_);
    return v_res_6857_;
}
pub unsafe fn _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut LeanObject = core::ptr::null_mut();
    v___x_6859_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0;
    v___x_6860_ = l_Lean_stringToMessageData(v___x_6859_);
    return v___x_6860_;
}
pub unsafe fn l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(
    mut v_ex_6861_: *mut LeanObject,
    mut v___y_6862_: *mut LeanObject,
    mut v___y_6863_: *mut LeanObject,
    mut v___y_6864_: *mut LeanObject,
    mut v___y_6865_: *mut LeanObject,
    mut v___y_6866_: *mut LeanObject,
    mut v___y_6867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_6870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_6872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6874_: u8 = 0;
    let mut v___x_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6884_: u8 = 0;
    let mut v_ref_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6893_: u8 = 0;
    let mut v___x_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: u8 = 0;
    let mut v___x_6897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_ex_6861_) == 0 {
                    v_ref_6869_ = lean_ctor_get(v_ex_6861_, 0);
                    lean_inc(v_ref_6869_);
                    v_msg_6870_ = lean_ctor_get(v_ex_6861_, 1);
                    lean_inc_ref(v_msg_6870_);
                    lean_dec_ref_known(v_ex_6861_, 2);
                    v___x_6871_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_6869_, v_msg_6870_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_, v___y_6867_);
                    lean_dec(v_ref_6869_);
                    return v___x_6871_;
                } else {
                    v_id_6872_ = lean_ctor_get(v_ex_6861_, 0);
                    lean_inc(v_id_6872_);
                    v___x_6896_ = l_Lean_Elab_isAbortExceptionId(v_id_6872_);
                    if v___x_6896_ == 0 {
                        v___x_6897_ = l_Lean_Exception_isInterrupt(v_ex_6861_);
                        lean_dec_ref_known(v_ex_6861_, 2);
                        v___y_6874_ = v___x_6897_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref_known(v_ex_6861_, 2);
                        v___y_6874_ = v___x_6896_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6874_ == 0 {
                    v___x_6875_ = l_Lean_InternalExceptionId_getName(v_id_6872_);
                    lean_dec(v_id_6872_);
                    if lean_obj_tag(v___x_6875_) == 0 {
                        v_a_6876_ = lean_ctor_get(v___x_6875_, 0);
                        lean_inc(v_a_6876_);
                        lean_dec_ref_known(v___x_6875_, 1);
                        v___x_6877_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once), _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1);
                        v___x_6878_ = l_Lean_MessageData_ofName(v_a_6876_);
                        v___x_6879_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6879_, 0, v___x_6877_);
                        lean_ctor_set(v___x_6879_, 1, v___x_6878_);
                        v___x_6880_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v___x_6879_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_, v___y_6867_);
                        return v___x_6880_;
                    } else {
                        v_a_6881_ = lean_ctor_get(v___x_6875_, 0);
                        v_isSharedCheck_6893_ = (!lean_is_exclusive(v___x_6875_)) as u8;
                        if v_isSharedCheck_6893_ == 0 {
                            v___x_6883_ = v___x_6875_;
                            v_isShared_6884_ = v_isSharedCheck_6893_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_6881_);
                            lean_dec(v___x_6875_);
                            v___x_6883_ = lean_box(0);
                            v_isShared_6884_ = v_isSharedCheck_6893_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_id_6872_);
                    v___x_6894_ = lean_box(0);
                    v___x_6895_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6895_, 0, v___x_6894_);
                    return v___x_6895_;
                }
            }
            2 => {
                v_ref_6885_ = lean_ctor_get(v___y_6866_, 5);
                v___x_6886_ = lean_io_error_to_string(v_a_6881_);
                v___x_6887_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6887_, 0, v___x_6886_);
                v___x_6888_ = l_Lean_MessageData_ofFormat(v___x_6887_);
                lean_inc(v_ref_6885_);
                v___x_6889_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6889_, 0, v_ref_6885_);
                lean_ctor_set(v___x_6889_, 1, v___x_6888_);
                if v_isShared_6884_ == 0 {
                    lean_ctor_set(v___x_6883_, 0, v___x_6889_);
                    v___x_6891_ = v___x_6883_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6892_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6892_, 0, v___x_6889_);
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
    mut v_ex_6898_: *mut LeanObject,
    mut v___y_6899_: *mut LeanObject,
    mut v___y_6900_: *mut LeanObject,
    mut v___y_6901_: *mut LeanObject,
    mut v___y_6902_: *mut LeanObject,
    mut v___y_6903_: *mut LeanObject,
    mut v___y_6904_: *mut LeanObject,
    mut v___y_6905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6906_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6904_);
    lean_dec_ref(v___y_6903_);
    lean_dec(v___y_6902_);
    lean_dec_ref(v___y_6901_);
    lean_dec(v___y_6900_);
    lean_dec_ref(v___y_6899_);
    return v_res_6906_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(
    mut v_a_6907_: *mut LeanObject,
    mut v_config_6908_: *mut LeanObject,
    mut v_____r_6909_: *mut LeanObject,
    mut v___y_6910_: *mut LeanObject,
    mut v___y_6911_: *mut LeanObject,
    mut v___y_6912_: *mut LeanObject,
    mut v___y_6913_: *mut LeanObject,
    mut v___y_6914_: *mut LeanObject,
    mut v___y_6915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6920_: u8 = 0;
    let mut v___x_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6925_: u8 = 0;
    let mut v_unused_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6930_: u8 = 0;
    let mut v___x_6932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6917_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_a_6907_, v___y_6910_, v___y_6911_, v___y_6912_, v___y_6913_, v___y_6914_, v___y_6915_);
                if lean_obj_tag(v___x_6917_) == 0 {
                    v_isSharedCheck_6925_ = (!lean_is_exclusive(v___x_6917_)) as u8;
                    if v_isSharedCheck_6925_ == 0 {
                        v_unused_6926_ = lean_ctor_get(v___x_6917_, 0);
                        lean_dec(v_unused_6926_);
                        v___x_6919_ = v___x_6917_;
                        v_isShared_6920_ = v_isSharedCheck_6925_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_6917_);
                        v___x_6919_ = lean_box(0);
                        v_isShared_6920_ = v_isSharedCheck_6925_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_config_6908_);
                    v_a_6927_ = lean_ctor_get(v___x_6917_, 0);
                    v_isSharedCheck_6934_ = (!lean_is_exclusive(v___x_6917_)) as u8;
                    if v_isSharedCheck_6934_ == 0 {
                        v___x_6929_ = v___x_6917_;
                        v_isShared_6930_ = v_isSharedCheck_6934_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6927_);
                        lean_dec(v___x_6917_);
                        v___x_6929_ = lean_box(0);
                        v_isShared_6930_ = v_isSharedCheck_6934_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6921_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6921_, 0, v_config_6908_);
                if v_isShared_6920_ == 0 {
                    lean_ctor_set(v___x_6919_, 0, v___x_6921_);
                    v___x_6923_ = v___x_6919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6924_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6924_, 0, v___x_6921_);
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
                    v_reuseFailAlloc_6933_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6933_, 0, v_a_6927_);
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
    mut v_a_6935_: *mut LeanObject,
    mut v_config_6936_: *mut LeanObject,
    mut v_____r_6937_: *mut LeanObject,
    mut v___y_6938_: *mut LeanObject,
    mut v___y_6939_: *mut LeanObject,
    mut v___y_6940_: *mut LeanObject,
    mut v___y_6941_: *mut LeanObject,
    mut v___y_6942_: *mut LeanObject,
    mut v___y_6943_: *mut LeanObject,
    mut v___y_6944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6945_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6943_);
    lean_dec_ref(v___y_6942_);
    lean_dec(v___y_6941_);
    lean_dec_ref(v___y_6940_);
    lean_dec(v___y_6939_);
    lean_dec_ref(v___y_6938_);
    return v_res_6945_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(
    mut v___f_6946_: *mut LeanObject,
    mut v_x_6947_: *mut LeanObject,
    mut v___y_6948_: *mut LeanObject,
    mut v___y_6949_: *mut LeanObject,
    mut v___y_6950_: *mut LeanObject,
    mut v___y_6951_: *mut LeanObject,
    mut v___y_6952_: *mut LeanObject,
    mut v___y_6953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut LeanObject = core::ptr::null_mut();
    v___x_6955_ = lean_box(0);
    lean_inc(v___y_6953_);
    lean_inc_ref(v___y_6952_);
    lean_inc(v___y_6951_);
    lean_inc_ref(v___y_6950_);
    lean_inc(v___y_6949_);
    lean_inc_ref(v___y_6948_);
    v___x_6956_ = lean_apply_8(
        v___f_6946_,
        v___x_6955_,
        v___y_6948_,
        v___y_6949_,
        v___y_6950_,
        v___y_6951_,
        v___y_6952_,
        v___y_6953_,
        lean_box(0),
    );
    return v___x_6956_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1___boxed(
    mut v___f_6957_: *mut LeanObject,
    mut v_x_6958_: *mut LeanObject,
    mut v___y_6959_: *mut LeanObject,
    mut v___y_6960_: *mut LeanObject,
    mut v___y_6961_: *mut LeanObject,
    mut v___y_6962_: *mut LeanObject,
    mut v___y_6963_: *mut LeanObject,
    mut v___y_6964_: *mut LeanObject,
    mut v___y_6965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6966_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6964_);
    lean_dec_ref(v___y_6963_);
    lean_dec(v___y_6962_);
    lean_dec_ref(v___y_6961_);
    lean_dec(v___y_6960_);
    lean_dec_ref(v___y_6959_);
    lean_dec_ref(v_x_6958_);
    return v_res_6966_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(
    mut v_eval_6967_: *mut LeanObject,
    mut v_config_6968_: *mut LeanObject,
    mut v_item_6969_: *mut LeanObject,
    mut v_logExceptions_6970_: u8,
    mut v_a_6971_: *mut LeanObject,
    mut v_a_6972_: *mut LeanObject,
    mut v_a_6973_: *mut LeanObject,
    mut v_a_6974_: *mut LeanObject,
    mut v_a_6975_: *mut LeanObject,
    mut v_a_6976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6983_: u8 = 0;
    let mut v_a_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6988_: u8 = 0;
    let mut v_a_6989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6992_: u8 = 0;
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6996_: u8 = 0;
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7001_: u8 = 0;
    let mut v___x_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7004_: u8 = 0;
    let mut v_extra_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: u8 = 0;
    let mut v___x_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7016_: u8 = 0;
    let mut v_unused_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: u8 = 0;
    let mut v___x_7019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_6976_);
                lean_inc_ref(v_a_6975_);
                lean_inc(v_a_6974_);
                lean_inc_ref(v_a_6973_);
                lean_inc(v_a_6972_);
                lean_inc_ref(v_a_6971_);
                lean_inc(v_config_6968_);
                v___x_6997_ = lean_apply_9(
                    v_eval_6967_,
                    v_config_6968_,
                    v_item_6969_,
                    v_a_6971_,
                    v_a_6972_,
                    v_a_6973_,
                    v_a_6974_,
                    v_a_6975_,
                    v_a_6976_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6997_) == 0 {
                    lean_dec(v_config_6968_);
                    return v___x_6997_;
                } else {
                    v_a_6998_ = lean_ctor_get(v___x_6997_, 0);
                    lean_inc_n(v_a_6998_, 2);
                    lean_inc(v_config_6968_);
                    v___f_6999_ = lean_alloc_closure(
                        l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        2,
                    );
                    lean_closure_set(v___f_6999_, 0, v_a_6998_);
                    lean_closure_set(v___f_6999_, 1, v_config_6968_);
                    v___x_7018_ = l_Lean_Exception_isInterrupt(v_a_6998_);
                    if v___x_7018_ == 0 {
                        lean_inc(v_a_6998_);
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
                if lean_obj_tag(v___y_6979_) == 0 {
                    v_a_6980_ = lean_ctor_get(v___y_6979_, 0);
                    v_isSharedCheck_6988_ = (!lean_is_exclusive(v___y_6979_)) as u8;
                    if v_isSharedCheck_6988_ == 0 {
                        v___x_6982_ = v___y_6979_;
                        v_isShared_6983_ = v_isSharedCheck_6988_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6980_);
                        lean_dec(v___y_6979_);
                        v___x_6982_ = lean_box(0);
                        v_isShared_6983_ = v_isSharedCheck_6988_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6989_ = lean_ctor_get(v___y_6979_, 0);
                    v_isSharedCheck_6996_ = (!lean_is_exclusive(v___y_6979_)) as u8;
                    if v_isSharedCheck_6996_ == 0 {
                        v___x_6991_ = v___y_6979_;
                        v_isShared_6992_ = v_isSharedCheck_6996_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6989_);
                        lean_dec(v___y_6979_);
                        v___x_6991_ = lean_box(0);
                        v_isShared_6992_ = v_isSharedCheck_6996_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_a_6984_ = lean_ctor_get(v_a_6980_, 0);
                lean_inc(v_a_6984_);
                lean_dec(v_a_6980_);
                if v_isShared_6983_ == 0 {
                    lean_ctor_set(v___x_6982_, 0, v_a_6984_);
                    v___x_6986_ = v___x_6982_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6987_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6987_, 0, v_a_6984_);
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
                    v_reuseFailAlloc_6995_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6995_, 0, v_a_6989_);
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
                        lean_dec_ref(v___f_6999_);
                        lean_dec(v_a_6998_);
                        lean_dec(v_config_6968_);
                        return v___x_6997_;
                    } else {
                        v_isSharedCheck_7016_ = (!lean_is_exclusive(v___x_6997_)) as u8;
                        if v_isSharedCheck_7016_ == 0 {
                            v_unused_7017_ = lean_ctor_get(v___x_6997_, 0);
                            lean_dec(v_unused_7017_);
                            v___x_7003_ = v___x_6997_;
                            v_isShared_7004_ = v_isSharedCheck_7016_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v___x_6997_);
                            v___x_7003_ = lean_box(0);
                            v_isShared_7004_ = v_isSharedCheck_7016_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___f_6999_);
                    lean_dec(v_a_6998_);
                    lean_dec(v_config_6968_);
                    return v___x_6997_;
                }
            }
            7 => {
                if lean_obj_tag(v_a_6998_) == 1 {
                    v_extra_7005_ = lean_ctor_get(v_a_6998_, 1);
                    if lean_obj_tag(v_extra_7005_) == 0 {
                        lean_dec_ref(v___f_6999_);
                        v_id_7006_ = lean_ctor_get(v_a_6998_, 0);
                        v___x_7007_ = l_Lean_Elab_abortTermExceptionId;
                        v___x_7008_ =
                            l_Lean_instBEqInternalExceptionId_beq(v_id_7006_, v___x_7007_);
                        if v___x_7008_ == 0 {
                            lean_del_object(v___x_7003_);
                            v___x_7009_ = lean_box(0);
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
                            lean_dec_ref_known(v_a_6998_, 2);
                            if v_isShared_7004_ == 0 {
                                lean_ctor_set_tag(v___x_7003_, 0);
                                lean_ctor_set(v___x_7003_, 0, v_config_6968_);
                                v___x_7012_ = v___x_7003_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_7013_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7013_, 0, v_config_6968_);
                                v___x_7012_ = v_reuseFailAlloc_7013_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_7003_);
                        lean_dec(v_config_6968_);
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
                        lean_dec_ref_known(v_a_6998_, 2);
                        v___y_6979_ = v___x_7014_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7003_);
                    lean_dec(v_config_6968_);
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
                    lean_dec(v_a_6998_);
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
    mut v_eval_7020_: *mut LeanObject,
    mut v_config_7021_: *mut LeanObject,
    mut v_item_7022_: *mut LeanObject,
    mut v_logExceptions_7023_: *mut LeanObject,
    mut v_a_7024_: *mut LeanObject,
    mut v_a_7025_: *mut LeanObject,
    mut v_a_7026_: *mut LeanObject,
    mut v_a_7027_: *mut LeanObject,
    mut v_a_7028_: *mut LeanObject,
    mut v_a_7029_: *mut LeanObject,
    mut v_a_7030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7031_: u8 = 0;
    let mut v_res_7032_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7031_ = (lean_unbox(v_logExceptions_7023_) as u8);
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
    lean_dec(v_a_7029_);
    lean_dec_ref(v_a_7028_);
    lean_dec(v_a_7027_);
    lean_dec_ref(v_a_7026_);
    lean_dec(v_a_7025_);
    lean_dec_ref(v_a_7024_);
    return v_res_7032_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(
    mut v_00_u03b1_7033_: *mut LeanObject,
    mut v_eval_7034_: *mut LeanObject,
    mut v_config_7035_: *mut LeanObject,
    mut v_item_7036_: *mut LeanObject,
    mut v_logExceptions_7037_: u8,
    mut v_a_7038_: *mut LeanObject,
    mut v_a_7039_: *mut LeanObject,
    mut v_a_7040_: *mut LeanObject,
    mut v_a_7041_: *mut LeanObject,
    mut v_a_7042_: *mut LeanObject,
    mut v_a_7043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_7046_: *mut LeanObject,
    mut v_eval_7047_: *mut LeanObject,
    mut v_config_7048_: *mut LeanObject,
    mut v_item_7049_: *mut LeanObject,
    mut v_logExceptions_7050_: *mut LeanObject,
    mut v_a_7051_: *mut LeanObject,
    mut v_a_7052_: *mut LeanObject,
    mut v_a_7053_: *mut LeanObject,
    mut v_a_7054_: *mut LeanObject,
    mut v_a_7055_: *mut LeanObject,
    mut v_a_7056_: *mut LeanObject,
    mut v_a_7057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7058_: u8 = 0;
    let mut v_res_7059_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7058_ = (lean_unbox(v_logExceptions_7050_) as u8);
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
    lean_dec(v_a_7056_);
    lean_dec_ref(v_a_7055_);
    lean_dec(v_a_7054_);
    lean_dec_ref(v_a_7053_);
    lean_dec(v_a_7052_);
    lean_dec_ref(v_a_7051_);
    return v_res_7059_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(
    mut v_ref_7060_: *mut LeanObject,
    mut v_msgData_7061_: *mut LeanObject,
    mut v_severity_7062_: u8,
    mut v_isSilent_7063_: u8,
    mut v___y_7064_: *mut LeanObject,
    mut v___y_7065_: *mut LeanObject,
    mut v___y_7066_: *mut LeanObject,
    mut v___y_7067_: *mut LeanObject,
    mut v___y_7068_: *mut LeanObject,
    mut v___y_7069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    v___x_7071_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_7060_, v_msgData_7061_, v_severity_7062_, v_isSilent_7063_, v___y_7066_, v___y_7067_, v___y_7068_, v___y_7069_);
    return v___x_7071_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___boxed(
    mut v_ref_7072_: *mut LeanObject,
    mut v_msgData_7073_: *mut LeanObject,
    mut v_severity_7074_: *mut LeanObject,
    mut v_isSilent_7075_: *mut LeanObject,
    mut v___y_7076_: *mut LeanObject,
    mut v___y_7077_: *mut LeanObject,
    mut v___y_7078_: *mut LeanObject,
    mut v___y_7079_: *mut LeanObject,
    mut v___y_7080_: *mut LeanObject,
    mut v___y_7081_: *mut LeanObject,
    mut v___y_7082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_7083_: u8 = 0;
    let mut v_isSilent_boxed_7084_: u8 = 0;
    let mut v_res_7085_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_7083_ = (lean_unbox(v_severity_7074_) as u8);
    v_isSilent_boxed_7084_ = (lean_unbox(v_isSilent_7075_) as u8);
    v_res_7085_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(v_ref_7072_, v_msgData_7073_, v_severity_boxed_7083_, v_isSilent_boxed_7084_, v___y_7076_, v___y_7077_, v___y_7078_, v___y_7079_, v___y_7080_, v___y_7081_);
    lean_dec(v___y_7081_);
    lean_dec_ref(v___y_7080_);
    lean_dec(v___y_7079_);
    lean_dec_ref(v___y_7078_);
    lean_dec(v___y_7077_);
    lean_dec_ref(v___y_7076_);
    lean_dec(v_ref_7072_);
    return v_res_7085_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut LeanObject = core::ptr::null_mut();
    v___x_7086_ = lean_box(0);
    v___x_7087_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_7088_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_7088_, 0, v___x_7087_);
    lean_ctor_set(v___x_7088_, 1, v___x_7086_);
    return v___x_7088_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_7090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut LeanObject = core::ptr::null_mut();
    v___x_7090_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0);
    v___x_7091_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7091_, 0, v___x_7090_);
    return v___x_7091_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___boxed(
    mut v___y_7092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7093_: *mut LeanObject = core::ptr::null_mut();
    v_res_7093_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
    return v_res_7093_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(
    mut v_00_u03b1_7094_: *mut LeanObject,
    mut v___y_7095_: *mut LeanObject,
    mut v___y_7096_: *mut LeanObject,
    mut v___y_7097_: *mut LeanObject,
    mut v___y_7098_: *mut LeanObject,
    mut v___y_7099_: *mut LeanObject,
    mut v___y_7100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7102_: *mut LeanObject = core::ptr::null_mut();
    v___x_7102_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
    return v___x_7102_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___boxed(
    mut v_00_u03b1_7103_: *mut LeanObject,
    mut v___y_7104_: *mut LeanObject,
    mut v___y_7105_: *mut LeanObject,
    mut v___y_7106_: *mut LeanObject,
    mut v___y_7107_: *mut LeanObject,
    mut v___y_7108_: *mut LeanObject,
    mut v___y_7109_: *mut LeanObject,
    mut v___y_7110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7111_: *mut LeanObject = core::ptr::null_mut();
    v_res_7111_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(v_00_u03b1_7103_, v___y_7104_, v___y_7105_, v___y_7106_, v___y_7107_, v___y_7108_, v___y_7109_);
    lean_dec(v___y_7109_);
    lean_dec_ref(v___y_7108_);
    lean_dec(v___y_7107_);
    lean_dec_ref(v___y_7106_);
    lean_dec(v___y_7105_);
    lean_dec_ref(v___y_7104_);
    return v_res_7111_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut LeanObject = core::ptr::null_mut();
    v___x_7115_ = lean_unsigned_to_nat(1);
    v___x_7116_ = l_Lean_Level_ofNat(v___x_7115_);
    return v___x_7116_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut LeanObject = core::ptr::null_mut();
    v___x_7117_ = lean_box(0);
    v___x_7118_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2,
    );
    v___x_7119_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_7119_, 0, v___x_7118_);
    lean_ctor_set(v___x_7119_, 1, v___x_7117_);
    return v___x_7119_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut LeanObject = core::ptr::null_mut();
    v___x_7120_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: *mut LeanObject = core::ptr::null_mut();
    v___x_7126_ = lean_box(0);
    v___x_7127_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6;
    v___x_7128_ = l_Lean_Expr_const___override(v___x_7127_, v___x_7126_);
    return v___x_7128_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(
    mut v_cfg_7132_: *mut LeanObject,
    mut v_cfgItem_7133_: *mut LeanObject,
    mut v_cfgType_x3f_7134_: *mut LeanObject,
    mut v_a_7135_: *mut LeanObject,
    mut v_a_7136_: *mut LeanObject,
    mut v_a_7137_: *mut LeanObject,
    mut v_a_7138_: *mut LeanObject,
    mut v_a_7139_: *mut LeanObject,
    mut v_a_7140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: u8 = 0;
    let mut v___x_7150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_7155_: u8 = 0;
    let mut v___x_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7159_: u8 = 0;
    let mut v___x_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: u8 = 0;
    let mut v___x_7168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: u8 = 0;
    let mut v___x_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_cfgType_x3f_7134_) == 1 {
                    v_val_7152_ = lean_ctor_get(v_cfgType_x3f_7134_, 0);
                    lean_inc(v_val_7152_);
                    lean_dec_ref_known(v_cfgType_x3f_7134_, 1);
                    v___x_7153_ = lean_st_ref_get(v_a_7140_);
                    v_infoState_7154_ = lean_ctor_get(v___x_7153_, 7);
                    lean_inc_ref(v_infoState_7154_);
                    lean_dec(v___x_7153_);
                    v_enabled_7155_ = lean_ctor_get_uint8(
                        v_infoState_7154_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    lean_dec_ref(v_infoState_7154_);
                    if v_enabled_7155_ == 0 {
                        lean_dec(v_val_7152_);
                        v___y_7143_ = v_a_7135_;
                        v___y_7144_ = v_a_7136_;
                        v___y_7145_ = v_a_7137_;
                        v___y_7146_ = v_a_7138_;
                        v___y_7147_ = v_a_7139_;
                        v___y_7148_ = v_a_7140_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7156_ = lean_unsigned_to_nat(0);
                        v___x_7157_ = l_Lean_Syntax_getArg(v_cfgItem_7133_, v___x_7156_);
                        v___x_7171_ = l_Lean_Syntax_isAtom(v___x_7157_);
                        if v___x_7171_ == 0 {
                            v___y_7159_ = v___x_7171_;
                            state = 2;
                            continue;
                        } else {
                            v___x_7172_ = lean_unsigned_to_nat(1);
                            v___x_7173_ = l_Lean_Syntax_getArg(v_cfgItem_7133_, v___x_7172_);
                            v___x_7174_ = l_Lean_Syntax_isMissing(v___x_7173_);
                            lean_dec(v___x_7173_);
                            v___y_7159_ = v___x_7174_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_cfgType_x3f_7134_);
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
                    lean_dec(v_cfg_7132_);
                    v___x_7150_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
                    return v___x_7150_;
                } else {
                    v___x_7151_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7151_, 0, v_cfg_7132_);
                    return v___x_7151_;
                }
            }
            2 => {
                if v___y_7159_ == 0 {
                    lean_dec(v___x_7157_);
                    lean_dec(v_val_7152_);
                    v___y_7143_ = v_a_7135_;
                    v___y_7144_ = v_a_7136_;
                    v___y_7145_ = v_a_7137_;
                    v___y_7146_ = v_a_7138_;
                    v___y_7147_ = v_a_7139_;
                    v___y_7148_ = v_a_7140_;
                    state = 1;
                    continue;
                } else {
                    v___x_7160_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once), _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4);
                    v___x_7161_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once), _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7);
                    v___x_7162_ = l_Lean_mkAppB(v___x_7160_, v_val_7152_, v___x_7161_);
                    v___x_7163_ =
                        l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9;
                    v___x_7164_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7164_, 0, v___x_7163_);
                    lean_ctor_set(v___x_7164_, 1, v___x_7157_);
                    v___x_7165_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2,
                    );
                    v___x_7166_ = lean_box(0);
                    v___x_7167_ = 0;
                    v___x_7168_ = lean_alloc_ctor(0, 4, (2) as u32);
                    lean_ctor_set(v___x_7168_, 0, v___x_7164_);
                    lean_ctor_set(v___x_7168_, 1, v___x_7165_);
                    lean_ctor_set(v___x_7168_, 2, v___x_7166_);
                    lean_ctor_set(v___x_7168_, 3, v___x_7162_);
                    lean_ctor_set_uint8(
                        v___x_7168_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v___x_7167_,
                    );
                    lean_ctor_set_uint8(
                        v___x_7168_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v___x_7167_,
                    );
                    v___x_7169_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7169_, 0, v___x_7168_);
                    lean_ctor_set(v___x_7169_, 1, v___x_7166_);
                    v___x_7170_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_7169_, v_a_7135_, v_a_7136_, v_a_7137_, v_a_7138_, v_a_7139_, v_a_7140_);
                    lean_dec_ref(v___x_7170_);
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
    mut v_cfg_7175_: *mut LeanObject,
    mut v_cfgItem_7176_: *mut LeanObject,
    mut v_cfgType_x3f_7177_: *mut LeanObject,
    mut v_a_7178_: *mut LeanObject,
    mut v_a_7179_: *mut LeanObject,
    mut v_a_7180_: *mut LeanObject,
    mut v_a_7181_: *mut LeanObject,
    mut v_a_7182_: *mut LeanObject,
    mut v_a_7183_: *mut LeanObject,
    mut v_a_7184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7185_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_7183_);
    lean_dec_ref(v_a_7182_);
    lean_dec(v_a_7181_);
    lean_dec_ref(v_a_7180_);
    lean_dec(v_a_7179_);
    lean_dec_ref(v_a_7178_);
    lean_dec(v_cfgItem_7176_);
    return v_res_7185_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(
    mut v_00_u03b1_7186_: *mut LeanObject,
    mut v_cfg_7187_: *mut LeanObject,
    mut v_cfgItem_7188_: *mut LeanObject,
    mut v_cfgType_x3f_7189_: *mut LeanObject,
    mut v_a_7190_: *mut LeanObject,
    mut v_a_7191_: *mut LeanObject,
    mut v_a_7192_: *mut LeanObject,
    mut v_a_7193_: *mut LeanObject,
    mut v_a_7194_: *mut LeanObject,
    mut v_a_7195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7197_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_7198_: *mut LeanObject,
    mut v_cfg_7199_: *mut LeanObject,
    mut v_cfgItem_7200_: *mut LeanObject,
    mut v_cfgType_x3f_7201_: *mut LeanObject,
    mut v_a_7202_: *mut LeanObject,
    mut v_a_7203_: *mut LeanObject,
    mut v_a_7204_: *mut LeanObject,
    mut v_a_7205_: *mut LeanObject,
    mut v_a_7206_: *mut LeanObject,
    mut v_a_7207_: *mut LeanObject,
    mut v_a_7208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7209_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_7207_);
    lean_dec_ref(v_a_7206_);
    lean_dec(v_a_7205_);
    lean_dec_ref(v_a_7204_);
    lean_dec(v_a_7203_);
    lean_dec_ref(v_a_7202_);
    lean_dec(v_cfgItem_7200_);
    return v_res_7209_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(
    mut v_s_7210_: *mut LeanObject,
    mut v_a_7211_: *mut LeanObject,
    mut v_b_7212_: u8,
) -> u8 {
    let mut v_str_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_7214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: u8 = 0;
    let mut v___x_7218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: u32 = 0;
    let mut v___x_7220_: u32 = 0;
    let mut v___x_7221_: u8 = 0;
    let mut v___x_7222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_7213_ = lean_ctor_get(v_s_7210_, 0);
                v_startInclusive_7214_ = lean_ctor_get(v_s_7210_, 1);
                v_endExclusive_7215_ = lean_ctor_get(v_s_7210_, 2);
                v___x_7216_ = lean_nat_sub(v_endExclusive_7215_, v_startInclusive_7214_);
                v___x_7217_ = lean_nat_dec_eq(v_a_7211_, v___x_7216_);
                lean_dec(v___x_7216_);
                if v___x_7217_ == 0 {
                    v___x_7218_ = lean_nat_add(v_startInclusive_7214_, v_a_7211_);
                    lean_dec(v_a_7211_);
                    v___x_7219_ = lean_string_utf8_get_fast(v_str_7213_, v___x_7218_);
                    v___x_7220_ = 46;
                    v___x_7221_ = lean_uint32_dec_eq(v___x_7219_, v___x_7220_);
                    if v___x_7221_ == 0 {
                        v___x_7222_ = lean_string_utf8_next_fast(v_str_7213_, v___x_7218_);
                        lean_dec(v___x_7218_);
                        v___x_7223_ = lean_nat_sub(v___x_7222_, v_startInclusive_7214_);
                        v_a_7211_ = v___x_7223_;
                        v_b_7212_ = v___x_7221_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_7218_);
                        return v___x_7221_;
                    }
                } else {
                    lean_dec(v_a_7211_);
                    return v_b_7212_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_s_7225_: *mut LeanObject,
    mut v_a_7226_: *mut LeanObject,
    mut v_b_7227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_7228_: u8 = 0;
    let mut v_res_7229_: u8 = 0;
    let mut v_r_7230_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_7228_ = (lean_unbox(v_b_7227_) as u8);
    v_res_7229_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_7225_, v_a_7226_, v_b_boxed_7228_);
    lean_dec_ref(v_s_7225_);
    v_r_7230_ = lean_box((v_res_7229_) as usize);
    return v_r_7230_;
}
pub unsafe fn l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(
    mut v_s_7231_: *mut LeanObject,
) -> u8 {
    let mut v_searcher_7232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: u8 = 0;
    let mut v___x_7234_: u8 = 0;
    v_searcher_7232_ = lean_unsigned_to_nat(0);
    v___x_7233_ = 0;
    v___x_7234_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_7231_, v_searcher_7232_, v___x_7233_);
    return v___x_7234_;
}
pub unsafe fn l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0___boxed(
    mut v_s_7235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7236_: u8 = 0;
    let mut v_r_7237_: *mut LeanObject = core::ptr::null_mut();
    v_res_7236_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v_s_7235_);
    lean_dec_ref(v_s_7235_);
    v_r_7237_ = lean_box((v_res_7236_) as usize);
    return v_r_7237_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(
    mut v_si_7238_: *mut LeanObject,
    mut v_val_7239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: u8 = 0;
    let mut v___x_7251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7247_ = lean_unsigned_to_nat(0);
                v___x_7248_ = lean_string_utf8_byte_size(v_val_7239_);
                lean_inc_ref(v_val_7239_);
                v___x_7249_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_7249_, 0, v_val_7239_);
                lean_ctor_set(v___x_7249_, 1, v___x_7247_);
                lean_ctor_set(v___x_7249_, 2, v___x_7248_);
                v___x_7250_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v___x_7249_);
                lean_dec_ref_known(v___x_7249_, 3);
                if v___x_7250_ == 0 {
                    v___x_7251_ = lean_box(0);
                    lean_inc_ref(v_val_7239_);
                    v___x_7252_ = l_Lean_Name_str___override(v___x_7251_, v_val_7239_);
                    v___y_7241_ = v___x_7252_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_val_7239_);
                    v___x_7253_ = l_String_toName(v_val_7239_);
                    v___y_7241_ = v___x_7253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7242_ = lean_unsigned_to_nat(0);
                v___x_7243_ = lean_string_utf8_byte_size(v_val_7239_);
                v___x_7244_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_7244_, 0, v_val_7239_);
                lean_ctor_set(v___x_7244_, 1, v___x_7242_);
                lean_ctor_set(v___x_7244_, 2, v___x_7243_);
                v___x_7245_ = lean_box(0);
                v___x_7246_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_7246_, 0, v_si_7238_);
                lean_ctor_set(v___x_7246_, 1, v___x_7244_);
                lean_ctor_set(v___x_7246_, 2, v___y_7241_);
                lean_ctor_set(v___x_7246_, 3, v___x_7245_);
                return v___x_7246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(
    mut v_eval_7255_: *mut LeanObject,
    mut v_logExceptions_7256_: u8,
    mut v_onErr_7257_: *mut LeanObject,
    mut v_init_7258_: *mut LeanObject,
    mut v_cfgs_7259_: *mut LeanObject,
    mut v___y_7260_: *mut LeanObject,
    mut v___y_7261_: *mut LeanObject,
    mut v___y_7262_: *mut LeanObject,
    mut v___y_7263_: *mut LeanObject,
    mut v___y_7264_: *mut LeanObject,
    mut v___y_7265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: u8 = 0;
    v___x_7267_ = lean_unsigned_to_nat(0);
    v___x_7268_ = lean_array_get_size(v_cfgs_7259_);
    v___x_7269_ = lean_nat_dec_lt(v___x_7267_, v___x_7268_);
    if v___x_7269_ == 0 {
        let mut v___x_7270_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_onErr_7257_);
        lean_dec_ref(v_eval_7255_);
        v___x_7270_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_7270_, 0, v_init_7258_);
        return v___x_7270_;
    } else {
        let mut v___x_7271_: u8 = 0;
        v___x_7271_ = lean_nat_dec_le(v___x_7268_, v___x_7268_);
        if v___x_7271_ == 0 {
            if v___x_7269_ == 0 {
                let mut v___x_7272_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_onErr_7257_);
                lean_dec_ref(v_eval_7255_);
                v___x_7272_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7272_, 0, v_init_7258_);
                return v___x_7272_;
            } else {
                let mut v___x_7273_: usize = 0;
                let mut v___x_7274_: usize = 0;
                let mut v___x_7275_: *mut LeanObject = core::ptr::null_mut();
                v___x_7273_ = 0usize;
                v___x_7274_ = lean_usize_of_nat(v___x_7268_);
                v___x_7275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_7255_, v_logExceptions_7256_, v_onErr_7257_, v_cfgs_7259_, v___x_7273_, v___x_7274_, v_init_7258_, v___y_7260_, v___y_7261_, v___y_7262_, v___y_7263_, v___y_7264_, v___y_7265_);
                return v___x_7275_;
            }
        } else {
            let mut v___x_7276_: usize = 0;
            let mut v___x_7277_: usize = 0;
            let mut v___x_7278_: *mut LeanObject = core::ptr::null_mut();
            v___x_7276_ = 0usize;
            v___x_7277_ = lean_usize_of_nat(v___x_7268_);
            v___x_7278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_7255_, v_logExceptions_7256_, v_onErr_7257_, v_cfgs_7259_, v___x_7276_, v___x_7277_, v_init_7258_, v___y_7260_, v___y_7261_, v___y_7262_, v___y_7263_, v___y_7264_, v___y_7265_);
            return v___x_7278_;
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(
    mut v_eval_7279_: *mut LeanObject,
    mut v_logExceptions_7280_: u8,
    mut v_onErr_7281_: *mut LeanObject,
    mut v_init_7282_: *mut LeanObject,
    mut v_cfg_7283_: *mut LeanObject,
    mut v___y_7284_: *mut LeanObject,
    mut v___y_7285_: *mut LeanObject,
    mut v___y_7286_: *mut LeanObject,
    mut v___y_7287_: *mut LeanObject,
    mut v___y_7288_: *mut LeanObject,
    mut v___y_7289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_7303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7315_: u8 = 0;
    let mut v_cancelTk_x3f_7316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7317_: u8 = 0;
    let mut v_inheritedTraceOptions_7318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: u8 = 0;
    let mut v___x_7324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7326_: u8 = 0;
    let mut v_atomAsIdent_7327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7328_: u8 = 0;
    let mut v_info_7329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7347_: u8 = 0;
    let mut v___x_7348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7349_: u8 = 0;
    let mut v___x_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: u8 = 0;
    let mut v___x_7360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: u8 = 0;
    let mut v___x_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: u8 = 0;
    let mut v___x_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7365_: u8 = 0;
    let mut v___x_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7322_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1;
                lean_inc(v_cfg_7283_);
                v___x_7323_ = l_Lean_Syntax_isOfKind(v_cfg_7283_, v___x_7322_);
                if v___x_7323_ == 0 {
                    v___x_7324_ = l_Lean_Syntax_getNumArgs(v_cfg_7283_);
                    v___x_7325_ = lean_unsigned_to_nat(1);
                    v___x_7326_ = lean_nat_dec_eq(v___x_7324_, v___x_7325_);
                    if v___x_7326_ == 0 {
                        v_atomAsIdent_7327_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0;
                        v___x_7328_ = lean_nat_dec_le(v___x_7325_, v___x_7324_);
                        if v___x_7328_ == 0 {
                            lean_dec(v___x_7324_);
                            if lean_obj_tag(v_cfg_7283_) == 2 {
                                lean_dec_ref(v_onErr_7281_);
                                v_info_7329_ = lean_ctor_get(v_cfg_7283_, 0);
                                v_val_7330_ = lean_ctor_get(v_cfg_7283_, 1);
                                lean_inc_ref(v_val_7330_);
                                lean_inc(v_info_7329_);
                                v___x_7331_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(v_info_7329_, v_val_7330_);
                                v___x_7332_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7;
                                v___x_7333_ =
                                    l_Lean_mkCIdentFrom(v_cfg_7283_, v___x_7332_, v___x_7326_);
                                v___x_7334_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8;
                                v___x_7335_ = l_Lean_TSyntax_getId(v___x_7331_);
                                v___x_7336_ = lean_erase_macro_scopes(v___x_7335_);
                                v___x_7337_ = lean_box(0);
                                lean_inc(v___x_7331_);
                                v___x_7338_ =
                                    l_Lean_Syntax_identComponents(v___x_7331_, v___x_7337_);
                                v___x_7339_ = lean_box(0);
                                v___x_7340_ = lean_alloc_ctor(0, 7, (0) as u32);
                                lean_ctor_set(v___x_7340_, 0, v_cfg_7283_);
                                lean_ctor_set(v___x_7340_, 1, v___x_7331_);
                                lean_ctor_set(v___x_7340_, 2, v___x_7333_);
                                lean_ctor_set(v___x_7340_, 3, v___x_7334_);
                                lean_ctor_set(v___x_7340_, 4, v___x_7336_);
                                lean_ctor_set(v___x_7340_, 5, v___x_7338_);
                                lean_ctor_set(v___x_7340_, 6, v___x_7339_);
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
                                lean_dec_ref(v_eval_7279_);
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_7342_ = lean_unsigned_to_nat(0);
                            v___x_7343_ = l_Lean_Syntax_getArg(v_cfg_7283_, v___x_7342_);
                            if lean_obj_tag(v___x_7343_) == 2 {
                                v_val_7344_ = lean_ctor_get(v___x_7343_, 1);
                                lean_inc_ref(v_val_7344_);
                                v___x_7358_ =
                                    l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11;
                                v___x_7359_ = lean_string_dec_eq(v_val_7344_, v___x_7358_);
                                if v___x_7359_ == 0 {
                                    v___x_7360_ =
                                        l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12;
                                    v___x_7361_ = lean_string_dec_eq(v_val_7344_, v___x_7360_);
                                    if v___x_7361_ == 0 {
                                        lean_dec_ref_known(v___x_7343_, 2);
                                        v___x_7362_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13;
                                        v___x_7363_ = lean_string_dec_eq(v_val_7344_, v___x_7362_);
                                        lean_dec_ref(v_val_7344_);
                                        if v___x_7363_ == 0 {
                                            lean_dec(v___x_7324_);
                                            lean_dec_ref(v_eval_7279_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_7364_ = lean_unsigned_to_nat(5);
                                            v___x_7365_ = lean_nat_dec_le(v___x_7324_, v___x_7364_);
                                            lean_dec(v___x_7324_);
                                            if v___x_7365_ == 0 {
                                                lean_dec_ref(v_eval_7279_);
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_7366_ =
                                                    l_Lean_Syntax_getArg(v_cfg_7283_, v___x_7325_);
                                                v___x_7367_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_7327_, v___x_7366_);
                                                if lean_obj_tag(v___x_7367_) == 1 {
                                                    lean_dec_ref(v_onErr_7281_);
                                                    v_val_7368_ = lean_ctor_get(v___x_7367_, 0);
                                                    lean_inc_n(v_val_7368_, 2);
                                                    lean_dec_ref_known(v___x_7367_, 1);
                                                    v___x_7369_ = lean_unsigned_to_nat(3);
                                                    v___x_7370_ = l_Lean_Syntax_getArg(
                                                        v_cfg_7283_,
                                                        v___x_7369_,
                                                    );
                                                    v___x_7371_ = lean_box(0);
                                                    v___x_7372_ = l_Lean_TSyntax_getId(v_val_7368_);
                                                    v___x_7373_ =
                                                        lean_erase_macro_scopes(v___x_7372_);
                                                    v___x_7374_ = l_Lean_Syntax_identComponents(
                                                        v_val_7368_,
                                                        v___x_7371_,
                                                    );
                                                    v___x_7375_ = lean_box(0);
                                                    v___x_7376_ = lean_alloc_ctor(0, 7, (0) as u32);
                                                    lean_ctor_set(v___x_7376_, 0, v_cfg_7283_);
                                                    lean_ctor_set(v___x_7376_, 1, v_val_7368_);
                                                    lean_ctor_set(v___x_7376_, 2, v___x_7370_);
                                                    lean_ctor_set(v___x_7376_, 3, v___x_7371_);
                                                    lean_ctor_set(v___x_7376_, 4, v___x_7373_);
                                                    lean_ctor_set(v___x_7376_, 5, v___x_7374_);
                                                    lean_ctor_set(v___x_7376_, 6, v___x_7375_);
                                                    v___x_7377_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_7279_, v_init_7282_, v___x_7376_, v_logExceptions_7280_, v___y_7284_, v___y_7285_, v___y_7286_, v___y_7287_, v___y_7288_, v___y_7289_);
                                                    return v___x_7377_;
                                                } else {
                                                    lean_dec(v___x_7367_);
                                                    lean_dec_ref(v_eval_7279_);
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v_val_7344_);
                                        v___x_7378_ = lean_box((v___x_7326_) as usize);
                                        v___x_7379_ = lean_alloc_ctor(1, 1, (0) as u32);
                                        lean_ctor_set(v___x_7379_, 0, v___x_7378_);
                                        v___y_7346_ = v___x_7379_;
                                        v_val_7347_ = v___x_7326_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_val_7344_);
                                    v___x_7380_ = lean_box((v___x_7359_) as usize);
                                    v___x_7381_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_7381_, 0, v___x_7380_);
                                    v___y_7346_ = v___x_7381_;
                                    v_val_7347_ = v___x_7359_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_7343_);
                                lean_dec(v___x_7324_);
                                lean_dec_ref(v_eval_7279_);
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_7324_);
                        v___x_7382_ = lean_unsigned_to_nat(0);
                        v___x_7383_ = l_Lean_Syntax_getArg(v_cfg_7283_, v___x_7382_);
                        lean_dec(v_cfg_7283_);
                        v_cfg_7283_ = v___x_7383_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_7385_ = l_Lean_Syntax_getArgs(v_cfg_7283_);
                    lean_dec(v_cfg_7283_);
                    v___x_7386_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7279_, v_logExceptions_7280_, v_onErr_7281_, v_init_7282_, v___x_7385_, v___y_7284_, v___y_7285_, v___y_7286_, v___y_7287_, v___y_7288_, v___y_7289_);
                    lean_dec_ref(v___x_7385_);
                    return v___x_7386_;
                }
            }
            1 => {
                v___x_7295_ = l_Lean_TSyntax_getId(v___y_7292_);
                v___x_7296_ = lean_erase_macro_scopes(v___x_7295_);
                v___x_7297_ = lean_box(0);
                lean_inc(v___y_7292_);
                v___x_7298_ = l_Lean_Syntax_identComponents(v___y_7292_, v___x_7297_);
                v___x_7299_ = lean_box(0);
                v___x_7300_ = lean_alloc_ctor(0, 7, (0) as u32);
                lean_ctor_set(v___x_7300_, 0, v_cfg_7283_);
                lean_ctor_set(v___x_7300_, 1, v___y_7292_);
                lean_ctor_set(v___x_7300_, 2, v___y_7294_);
                lean_ctor_set(v___x_7300_, 3, v___y_7293_);
                lean_ctor_set(v___x_7300_, 4, v___x_7296_);
                lean_ctor_set(v___x_7300_, 5, v___x_7298_);
                lean_ctor_set(v___x_7300_, 6, v___x_7299_);
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
                v_fileName_7303_ = lean_ctor_get(v___y_7288_, 0);
                v_fileMap_7304_ = lean_ctor_get(v___y_7288_, 1);
                v_options_7305_ = lean_ctor_get(v___y_7288_, 2);
                v_currRecDepth_7306_ = lean_ctor_get(v___y_7288_, 3);
                v_maxRecDepth_7307_ = lean_ctor_get(v___y_7288_, 4);
                v_ref_7308_ = lean_ctor_get(v___y_7288_, 5);
                v_currNamespace_7309_ = lean_ctor_get(v___y_7288_, 6);
                v_openDecls_7310_ = lean_ctor_get(v___y_7288_, 7);
                v_initHeartbeats_7311_ = lean_ctor_get(v___y_7288_, 8);
                v_maxHeartbeats_7312_ = lean_ctor_get(v___y_7288_, 9);
                v_quotContext_7313_ = lean_ctor_get(v___y_7288_, 10);
                v_currMacroScope_7314_ = lean_ctor_get(v___y_7288_, 11);
                v_diag_7315_ = lean_ctor_get_uint8(
                    v___y_7288_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7316_ = lean_ctor_get(v___y_7288_, 12);
                v_suppressElabErrors_7317_ = lean_ctor_get_uint8(
                    v___y_7288_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7318_ = lean_ctor_get(v___y_7288_, 13);
                v_ref_7319_ = l_Lean_replaceRef(v_cfg_7283_, v_ref_7308_);
                lean_inc_ref(v_inheritedTraceOptions_7318_);
                lean_inc(v_cancelTk_x3f_7316_);
                lean_inc(v_currMacroScope_7314_);
                lean_inc(v_quotContext_7313_);
                lean_inc(v_maxHeartbeats_7312_);
                lean_inc(v_initHeartbeats_7311_);
                lean_inc(v_openDecls_7310_);
                lean_inc(v_currNamespace_7309_);
                lean_inc(v_maxRecDepth_7307_);
                lean_inc(v_currRecDepth_7306_);
                lean_inc_ref(v_options_7305_);
                lean_inc_ref(v_fileMap_7304_);
                lean_inc_ref(v_fileName_7303_);
                v___x_7320_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_7320_, 0, v_fileName_7303_);
                lean_ctor_set(v___x_7320_, 1, v_fileMap_7304_);
                lean_ctor_set(v___x_7320_, 2, v_options_7305_);
                lean_ctor_set(v___x_7320_, 3, v_currRecDepth_7306_);
                lean_ctor_set(v___x_7320_, 4, v_maxRecDepth_7307_);
                lean_ctor_set(v___x_7320_, 5, v_ref_7319_);
                lean_ctor_set(v___x_7320_, 6, v_currNamespace_7309_);
                lean_ctor_set(v___x_7320_, 7, v_openDecls_7310_);
                lean_ctor_set(v___x_7320_, 8, v_initHeartbeats_7311_);
                lean_ctor_set(v___x_7320_, 9, v_maxHeartbeats_7312_);
                lean_ctor_set(v___x_7320_, 10, v_quotContext_7313_);
                lean_ctor_set(v___x_7320_, 11, v_currMacroScope_7314_);
                lean_ctor_set(v___x_7320_, 12, v_cancelTk_x3f_7316_);
                lean_ctor_set(v___x_7320_, 13, v_inheritedTraceOptions_7318_);
                lean_ctor_set_uint8(
                    v___x_7320_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_7315_,
                );
                lean_ctor_set_uint8(
                    v___x_7320_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7317_,
                );
                lean_inc(v___y_7289_);
                lean_inc(v___y_7287_);
                lean_inc_ref(v___y_7286_);
                lean_inc(v___y_7285_);
                lean_inc_ref(v___y_7284_);
                v___x_7321_ = lean_apply_9(
                    v_onErr_7281_,
                    v_init_7282_,
                    v_cfg_7283_,
                    v___y_7284_,
                    v___y_7285_,
                    v___y_7286_,
                    v___y_7287_,
                    v___x_7320_,
                    v___y_7289_,
                    lean_box(0),
                );
                return v___x_7321_;
            }
            3 => {
                v___x_7348_ = lean_unsigned_to_nat(2);
                v___x_7349_ = lean_nat_dec_eq(v___x_7324_, v___x_7348_);
                lean_dec(v___x_7324_);
                if v___x_7349_ == 0 {
                    lean_dec(v___y_7346_);
                    lean_dec_ref_known(v___x_7343_, 2);
                    lean_dec_ref(v_eval_7279_);
                    state = 2;
                    continue;
                } else {
                    v___x_7350_ = l_Lean_Syntax_getArg(v_cfg_7283_, v___x_7325_);
                    v___x_7351_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(
                        v_atomAsIdent_7327_,
                        v___x_7350_,
                    );
                    if lean_obj_tag(v___x_7351_) == 1 {
                        lean_dec_ref(v_onErr_7281_);
                        if v_val_7347_ == 0 {
                            v_val_7352_ = lean_ctor_get(v___x_7351_, 0);
                            lean_inc(v_val_7352_);
                            lean_dec_ref_known(v___x_7351_, 1);
                            v___x_7353_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10;
                            v___x_7354_ =
                                l_Lean_mkCIdentFrom(v___x_7343_, v___x_7353_, v___x_7326_);
                            lean_dec_ref_known(v___x_7343_, 2);
                            v___y_7292_ = v_val_7352_;
                            v___y_7293_ = v___y_7346_;
                            v___y_7294_ = v___x_7354_;
                            state = 1;
                            continue;
                        } else {
                            v_val_7355_ = lean_ctor_get(v___x_7351_, 0);
                            lean_inc(v_val_7355_);
                            lean_dec_ref_known(v___x_7351_, 1);
                            v___x_7356_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7;
                            v___x_7357_ =
                                l_Lean_mkCIdentFrom(v___x_7343_, v___x_7356_, v___x_7326_);
                            lean_dec_ref_known(v___x_7343_, 2);
                            v___y_7292_ = v_val_7355_;
                            v___y_7293_ = v___y_7346_;
                            v___y_7294_ = v___x_7357_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_7351_);
                        lean_dec(v___y_7346_);
                        lean_dec_ref_known(v___x_7343_, 2);
                        lean_dec_ref(v_eval_7279_);
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
    mut v_eval_7387_: *mut LeanObject,
    mut v_logExceptions_7388_: u8,
    mut v_onErr_7389_: *mut LeanObject,
    mut v_as_7390_: *mut LeanObject,
    mut v_i_7391_: usize,
    mut v_stop_7392_: usize,
    mut v_b_7393_: *mut LeanObject,
    mut v___y_7394_: *mut LeanObject,
    mut v___y_7395_: *mut LeanObject,
    mut v___y_7396_: *mut LeanObject,
    mut v___y_7397_: *mut LeanObject,
    mut v___y_7398_: *mut LeanObject,
    mut v___y_7399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7401_: u8 = 0;
    let mut v___x_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: usize = 0;
    let mut v___x_7406_: usize = 0;
    let mut v___x_7408_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7401_ = lean_usize_dec_eq(v_i_7391_, v_stop_7392_);
                if v___x_7401_ == 0 {
                    v___x_7402_ = lean_array_uget_borrowed(v_as_7390_, v_i_7391_);
                    lean_inc(v___x_7402_);
                    lean_inc_ref(v_onErr_7389_);
                    lean_inc_ref(v_eval_7387_);
                    v___x_7403_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7387_, v_logExceptions_7388_, v_onErr_7389_, v_b_7393_, v___x_7402_, v___y_7394_, v___y_7395_, v___y_7396_, v___y_7397_, v___y_7398_, v___y_7399_);
                    if lean_obj_tag(v___x_7403_) == 0 {
                        v_a_7404_ = lean_ctor_get(v___x_7403_, 0);
                        lean_inc(v_a_7404_);
                        lean_dec_ref_known(v___x_7403_, 1);
                        v___x_7405_ = 1usize;
                        v___x_7406_ = lean_usize_add(v_i_7391_, v___x_7405_);
                        v_i_7391_ = v___x_7406_;
                        v_b_7393_ = v_a_7404_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_onErr_7389_);
                        lean_dec_ref(v_eval_7387_);
                        return v___x_7403_;
                    }
                } else {
                    lean_dec_ref(v_onErr_7389_);
                    lean_dec_ref(v_eval_7387_);
                    v___x_7408_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7408_, 0, v_b_7393_);
                    return v___x_7408_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_eval_7409_: *mut LeanObject,
    mut v_logExceptions_7410_: *mut LeanObject,
    mut v_onErr_7411_: *mut LeanObject,
    mut v_as_7412_: *mut LeanObject,
    mut v_i_7413_: *mut LeanObject,
    mut v_stop_7414_: *mut LeanObject,
    mut v_b_7415_: *mut LeanObject,
    mut v___y_7416_: *mut LeanObject,
    mut v___y_7417_: *mut LeanObject,
    mut v___y_7418_: *mut LeanObject,
    mut v___y_7419_: *mut LeanObject,
    mut v___y_7420_: *mut LeanObject,
    mut v___y_7421_: *mut LeanObject,
    mut v___y_7422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7423_: u8 = 0;
    let mut v_i_boxed_7424_: usize = 0;
    let mut v_stop_boxed_7425_: usize = 0;
    let mut v_res_7426_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7423_ = (lean_unbox(v_logExceptions_7410_) as u8);
    v_i_boxed_7424_ = lean_unbox_usize(v_i_7413_);
    lean_dec(v_i_7413_);
    v_stop_boxed_7425_ = lean_unbox_usize(v_stop_7414_);
    lean_dec(v_stop_7414_);
    v_res_7426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_7409_, v_logExceptions_boxed_7423_, v_onErr_7411_, v_as_7412_, v_i_boxed_7424_, v_stop_boxed_7425_, v_b_7415_, v___y_7416_, v___y_7417_, v___y_7418_, v___y_7419_, v___y_7420_, v___y_7421_);
    lean_dec(v___y_7421_);
    lean_dec_ref(v___y_7420_);
    lean_dec(v___y_7419_);
    lean_dec_ref(v___y_7418_);
    lean_dec(v___y_7417_);
    lean_dec_ref(v___y_7416_);
    lean_dec_ref(v_as_7412_);
    return v_res_7426_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg___boxed(
    mut v_eval_7427_: *mut LeanObject,
    mut v_logExceptions_7428_: *mut LeanObject,
    mut v_onErr_7429_: *mut LeanObject,
    mut v_init_7430_: *mut LeanObject,
    mut v_cfgs_7431_: *mut LeanObject,
    mut v___y_7432_: *mut LeanObject,
    mut v___y_7433_: *mut LeanObject,
    mut v___y_7434_: *mut LeanObject,
    mut v___y_7435_: *mut LeanObject,
    mut v___y_7436_: *mut LeanObject,
    mut v___y_7437_: *mut LeanObject,
    mut v___y_7438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7439_: u8 = 0;
    let mut v_res_7440_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7439_ = (lean_unbox(v_logExceptions_7428_) as u8);
    v_res_7440_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7427_, v_logExceptions_boxed_7439_, v_onErr_7429_, v_init_7430_, v_cfgs_7431_, v___y_7432_, v___y_7433_, v___y_7434_, v___y_7435_, v___y_7436_, v___y_7437_);
    lean_dec(v___y_7437_);
    lean_dec_ref(v___y_7436_);
    lean_dec(v___y_7435_);
    lean_dec_ref(v___y_7434_);
    lean_dec(v___y_7433_);
    lean_dec_ref(v___y_7432_);
    lean_dec_ref(v_cfgs_7431_);
    return v_res_7440_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___boxed(
    mut v_eval_7441_: *mut LeanObject,
    mut v_logExceptions_7442_: *mut LeanObject,
    mut v_onErr_7443_: *mut LeanObject,
    mut v_init_7444_: *mut LeanObject,
    mut v_cfg_7445_: *mut LeanObject,
    mut v___y_7446_: *mut LeanObject,
    mut v___y_7447_: *mut LeanObject,
    mut v___y_7448_: *mut LeanObject,
    mut v___y_7449_: *mut LeanObject,
    mut v___y_7450_: *mut LeanObject,
    mut v___y_7451_: *mut LeanObject,
    mut v___y_7452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7453_: u8 = 0;
    let mut v_res_7454_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7453_ = (lean_unbox(v_logExceptions_7442_) as u8);
    v_res_7454_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7441_, v_logExceptions_boxed_7453_, v_onErr_7443_, v_init_7444_, v_cfg_7445_, v___y_7446_, v___y_7447_, v___y_7448_, v___y_7449_, v___y_7450_, v___y_7451_);
    lean_dec(v___y_7451_);
    lean_dec_ref(v___y_7450_);
    lean_dec(v___y_7449_);
    lean_dec_ref(v___y_7448_);
    lean_dec(v___y_7447_);
    lean_dec_ref(v___y_7446_);
    return v_res_7454_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(
    mut v_eval_7455_: *mut LeanObject,
    mut v_init_7456_: *mut LeanObject,
    mut v_cfg_7457_: *mut LeanObject,
    mut v_onErr_7458_: *mut LeanObject,
    mut v_logExceptions_7459_: u8,
    mut v_a_7460_: *mut LeanObject,
    mut v_a_7461_: *mut LeanObject,
    mut v_a_7462_: *mut LeanObject,
    mut v_a_7463_: *mut LeanObject,
    mut v_a_7464_: *mut LeanObject,
    mut v_a_7465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7467_: *mut LeanObject = core::ptr::null_mut();
    v___x_7467_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7455_, v_logExceptions_7459_, v_onErr_7458_, v_init_7456_, v_cfg_7457_, v_a_7460_, v_a_7461_, v_a_7462_, v_a_7463_, v_a_7464_, v_a_7465_);
    return v___x_7467_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg___boxed(
    mut v_eval_7468_: *mut LeanObject,
    mut v_init_7469_: *mut LeanObject,
    mut v_cfg_7470_: *mut LeanObject,
    mut v_onErr_7471_: *mut LeanObject,
    mut v_logExceptions_7472_: *mut LeanObject,
    mut v_a_7473_: *mut LeanObject,
    mut v_a_7474_: *mut LeanObject,
    mut v_a_7475_: *mut LeanObject,
    mut v_a_7476_: *mut LeanObject,
    mut v_a_7477_: *mut LeanObject,
    mut v_a_7478_: *mut LeanObject,
    mut v_a_7479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7480_: u8 = 0;
    let mut v_res_7481_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7480_ = (lean_unbox(v_logExceptions_7472_) as u8);
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
    lean_dec(v_a_7478_);
    lean_dec_ref(v_a_7477_);
    lean_dec(v_a_7476_);
    lean_dec_ref(v_a_7475_);
    lean_dec(v_a_7474_);
    lean_dec_ref(v_a_7473_);
    return v_res_7481_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(
    mut v_00_u03b1_7482_: *mut LeanObject,
    mut v_eval_7483_: *mut LeanObject,
    mut v_init_7484_: *mut LeanObject,
    mut v_cfg_7485_: *mut LeanObject,
    mut v_onErr_7486_: *mut LeanObject,
    mut v_logExceptions_7487_: u8,
    mut v_a_7488_: *mut LeanObject,
    mut v_a_7489_: *mut LeanObject,
    mut v_a_7490_: *mut LeanObject,
    mut v_a_7491_: *mut LeanObject,
    mut v_a_7492_: *mut LeanObject,
    mut v_a_7493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7495_: *mut LeanObject = core::ptr::null_mut();
    v___x_7495_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7483_, v_logExceptions_7487_, v_onErr_7486_, v_init_7484_, v_cfg_7485_, v_a_7488_, v_a_7489_, v_a_7490_, v_a_7491_, v_a_7492_, v_a_7493_);
    return v___x_7495_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___boxed(
    mut v_00_u03b1_7496_: *mut LeanObject,
    mut v_eval_7497_: *mut LeanObject,
    mut v_init_7498_: *mut LeanObject,
    mut v_cfg_7499_: *mut LeanObject,
    mut v_onErr_7500_: *mut LeanObject,
    mut v_logExceptions_7501_: *mut LeanObject,
    mut v_a_7502_: *mut LeanObject,
    mut v_a_7503_: *mut LeanObject,
    mut v_a_7504_: *mut LeanObject,
    mut v_a_7505_: *mut LeanObject,
    mut v_a_7506_: *mut LeanObject,
    mut v_a_7507_: *mut LeanObject,
    mut v_a_7508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7509_: u8 = 0;
    let mut v_res_7510_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7509_ = (lean_unbox(v_logExceptions_7501_) as u8);
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
    lean_dec(v_a_7507_);
    lean_dec_ref(v_a_7506_);
    lean_dec(v_a_7505_);
    lean_dec_ref(v_a_7504_);
    lean_dec(v_a_7503_);
    lean_dec_ref(v_a_7502_);
    return v_res_7510_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(
    mut v_00_u03b1_7511_: *mut LeanObject,
    mut v_eval_7512_: *mut LeanObject,
    mut v_logExceptions_7513_: u8,
    mut v_onErr_7514_: *mut LeanObject,
    mut v_init_7515_: *mut LeanObject,
    mut v_cfg_7516_: *mut LeanObject,
    mut v___y_7517_: *mut LeanObject,
    mut v___y_7518_: *mut LeanObject,
    mut v___y_7519_: *mut LeanObject,
    mut v___y_7520_: *mut LeanObject,
    mut v___y_7521_: *mut LeanObject,
    mut v___y_7522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7524_: *mut LeanObject = core::ptr::null_mut();
    v___x_7524_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_7512_, v_logExceptions_7513_, v_onErr_7514_, v_init_7515_, v_cfg_7516_, v___y_7517_, v___y_7518_, v___y_7519_, v___y_7520_, v___y_7521_, v___y_7522_);
    return v___x_7524_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___boxed(
    mut v_00_u03b1_7525_: *mut LeanObject,
    mut v_eval_7526_: *mut LeanObject,
    mut v_logExceptions_7527_: *mut LeanObject,
    mut v_onErr_7528_: *mut LeanObject,
    mut v_init_7529_: *mut LeanObject,
    mut v_cfg_7530_: *mut LeanObject,
    mut v___y_7531_: *mut LeanObject,
    mut v___y_7532_: *mut LeanObject,
    mut v___y_7533_: *mut LeanObject,
    mut v___y_7534_: *mut LeanObject,
    mut v___y_7535_: *mut LeanObject,
    mut v___y_7536_: *mut LeanObject,
    mut v___y_7537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7538_: u8 = 0;
    let mut v_res_7539_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7538_ = (lean_unbox(v_logExceptions_7527_) as u8);
    v_res_7539_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(v_00_u03b1_7525_, v_eval_7526_, v_logExceptions_boxed_7538_, v_onErr_7528_, v_init_7529_, v_cfg_7530_, v___y_7531_, v___y_7532_, v___y_7533_, v___y_7534_, v___y_7535_, v___y_7536_);
    lean_dec(v___y_7536_);
    lean_dec_ref(v___y_7535_);
    lean_dec(v___y_7534_);
    lean_dec_ref(v___y_7533_);
    lean_dec(v___y_7532_);
    lean_dec_ref(v___y_7531_);
    return v_res_7539_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(
    mut v_00_u03b1_7540_: *mut LeanObject,
    mut v_eval_7541_: *mut LeanObject,
    mut v_logExceptions_7542_: u8,
    mut v_onErr_7543_: *mut LeanObject,
    mut v_init_7544_: *mut LeanObject,
    mut v_cfgs_7545_: *mut LeanObject,
    mut v___y_7546_: *mut LeanObject,
    mut v___y_7547_: *mut LeanObject,
    mut v___y_7548_: *mut LeanObject,
    mut v___y_7549_: *mut LeanObject,
    mut v___y_7550_: *mut LeanObject,
    mut v___y_7551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7553_: *mut LeanObject = core::ptr::null_mut();
    v___x_7553_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7541_, v_logExceptions_7542_, v_onErr_7543_, v_init_7544_, v_cfgs_7545_, v___y_7546_, v___y_7547_, v___y_7548_, v___y_7549_, v___y_7550_, v___y_7551_);
    return v___x_7553_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___boxed(
    mut v_00_u03b1_7554_: *mut LeanObject,
    mut v_eval_7555_: *mut LeanObject,
    mut v_logExceptions_7556_: *mut LeanObject,
    mut v_onErr_7557_: *mut LeanObject,
    mut v_init_7558_: *mut LeanObject,
    mut v_cfgs_7559_: *mut LeanObject,
    mut v___y_7560_: *mut LeanObject,
    mut v___y_7561_: *mut LeanObject,
    mut v___y_7562_: *mut LeanObject,
    mut v___y_7563_: *mut LeanObject,
    mut v___y_7564_: *mut LeanObject,
    mut v___y_7565_: *mut LeanObject,
    mut v___y_7566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7567_: u8 = 0;
    let mut v_res_7568_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7567_ = (lean_unbox(v_logExceptions_7556_) as u8);
    v_res_7568_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(v_00_u03b1_7554_, v_eval_7555_, v_logExceptions_boxed_7567_, v_onErr_7557_, v_init_7558_, v_cfgs_7559_, v___y_7560_, v___y_7561_, v___y_7562_, v___y_7563_, v___y_7564_, v___y_7565_);
    lean_dec(v___y_7565_);
    lean_dec_ref(v___y_7564_);
    lean_dec(v___y_7563_);
    lean_dec_ref(v___y_7562_);
    lean_dec(v___y_7561_);
    lean_dec_ref(v___y_7560_);
    lean_dec_ref(v_cfgs_7559_);
    return v_res_7568_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(
    mut v_s_7569_: *mut LeanObject,
    mut v_inst_7570_: *mut LeanObject,
    mut v_R_7571_: *mut LeanObject,
    mut v_a_7572_: *mut LeanObject,
    mut v_b_7573_: u8,
    mut v_c_7574_: *mut LeanObject,
) -> u8 {
    let mut v___x_7575_: u8 = 0;
    v___x_7575_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_7569_, v_a_7572_, v_b_7573_);
    return v___x_7575_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___boxed(
    mut v_s_7576_: *mut LeanObject,
    mut v_inst_7577_: *mut LeanObject,
    mut v_R_7578_: *mut LeanObject,
    mut v_a_7579_: *mut LeanObject,
    mut v_b_7580_: *mut LeanObject,
    mut v_c_7581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_7582_: u8 = 0;
    let mut v_res_7583_: u8 = 0;
    let mut v_r_7584_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_7582_ = (lean_unbox(v_b_7580_) as u8);
    v_res_7583_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(v_s_7576_, v_inst_7577_, v_R_7578_, v_a_7579_, v_b_boxed_7582_, v_c_7581_);
    lean_dec_ref(v_s_7576_);
    v_r_7584_ = lean_box((v_res_7583_) as usize);
    return v_r_7584_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(
    mut v_00_u03b1_7585_: *mut LeanObject,
    mut v_eval_7586_: *mut LeanObject,
    mut v_logExceptions_7587_: u8,
    mut v_onErr_7588_: *mut LeanObject,
    mut v_as_7589_: *mut LeanObject,
    mut v_i_7590_: usize,
    mut v_stop_7591_: usize,
    mut v_b_7592_: *mut LeanObject,
    mut v___y_7593_: *mut LeanObject,
    mut v___y_7594_: *mut LeanObject,
    mut v___y_7595_: *mut LeanObject,
    mut v___y_7596_: *mut LeanObject,
    mut v___y_7597_: *mut LeanObject,
    mut v___y_7598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7600_: *mut LeanObject = core::ptr::null_mut();
    v___x_7600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_7586_, v_logExceptions_7587_, v_onErr_7588_, v_as_7589_, v_i_7590_, v_stop_7591_, v_b_7592_, v___y_7593_, v___y_7594_, v___y_7595_, v___y_7596_, v___y_7597_, v___y_7598_);
    return v___x_7600_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_7601_: *mut LeanObject,
    mut v_eval_7602_: *mut LeanObject,
    mut v_logExceptions_7603_: *mut LeanObject,
    mut v_onErr_7604_: *mut LeanObject,
    mut v_as_7605_: *mut LeanObject,
    mut v_i_7606_: *mut LeanObject,
    mut v_stop_7607_: *mut LeanObject,
    mut v_b_7608_: *mut LeanObject,
    mut v___y_7609_: *mut LeanObject,
    mut v___y_7610_: *mut LeanObject,
    mut v___y_7611_: *mut LeanObject,
    mut v___y_7612_: *mut LeanObject,
    mut v___y_7613_: *mut LeanObject,
    mut v___y_7614_: *mut LeanObject,
    mut v___y_7615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7616_: u8 = 0;
    let mut v_i_boxed_7617_: usize = 0;
    let mut v_stop_boxed_7618_: usize = 0;
    let mut v_res_7619_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7616_ = (lean_unbox(v_logExceptions_7603_) as u8);
    v_i_boxed_7617_ = lean_unbox_usize(v_i_7606_);
    lean_dec(v_i_7606_);
    v_stop_boxed_7618_ = lean_unbox_usize(v_stop_7607_);
    lean_dec(v_stop_7607_);
    v_res_7619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(v_00_u03b1_7601_, v_eval_7602_, v_logExceptions_boxed_7616_, v_onErr_7604_, v_as_7605_, v_i_boxed_7617_, v_stop_boxed_7618_, v_b_7608_, v___y_7609_, v___y_7610_, v___y_7611_, v___y_7612_, v___y_7613_, v___y_7614_);
    lean_dec(v___y_7614_);
    lean_dec_ref(v___y_7613_);
    lean_dec(v___y_7612_);
    lean_dec_ref(v___y_7611_);
    lean_dec(v___y_7610_);
    lean_dec_ref(v___y_7609_);
    lean_dec_ref(v_as_7605_);
    return v_res_7619_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(
    mut v_eval_7620_: *mut LeanObject,
    mut v_init_7621_: *mut LeanObject,
    mut v_cfgs_7622_: *mut LeanObject,
    mut v_onErr_7623_: *mut LeanObject,
    mut v_logExceptions_7624_: u8,
    mut v_a_7625_: *mut LeanObject,
    mut v_a_7626_: *mut LeanObject,
    mut v_a_7627_: *mut LeanObject,
    mut v_a_7628_: *mut LeanObject,
    mut v_a_7629_: *mut LeanObject,
    mut v_a_7630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7632_: *mut LeanObject = core::ptr::null_mut();
    v___x_7632_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7620_, v_logExceptions_7624_, v_onErr_7623_, v_init_7621_, v_cfgs_7622_, v_a_7625_, v_a_7626_, v_a_7627_, v_a_7628_, v_a_7629_, v_a_7630_);
    return v___x_7632_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg___boxed(
    mut v_eval_7633_: *mut LeanObject,
    mut v_init_7634_: *mut LeanObject,
    mut v_cfgs_7635_: *mut LeanObject,
    mut v_onErr_7636_: *mut LeanObject,
    mut v_logExceptions_7637_: *mut LeanObject,
    mut v_a_7638_: *mut LeanObject,
    mut v_a_7639_: *mut LeanObject,
    mut v_a_7640_: *mut LeanObject,
    mut v_a_7641_: *mut LeanObject,
    mut v_a_7642_: *mut LeanObject,
    mut v_a_7643_: *mut LeanObject,
    mut v_a_7644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7645_: u8 = 0;
    let mut v_res_7646_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7645_ = (lean_unbox(v_logExceptions_7637_) as u8);
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
    lean_dec(v_a_7643_);
    lean_dec_ref(v_a_7642_);
    lean_dec(v_a_7641_);
    lean_dec_ref(v_a_7640_);
    lean_dec(v_a_7639_);
    lean_dec_ref(v_a_7638_);
    lean_dec_ref(v_cfgs_7635_);
    return v_res_7646_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(
    mut v_00_u03b1_7647_: *mut LeanObject,
    mut v_eval_7648_: *mut LeanObject,
    mut v_init_7649_: *mut LeanObject,
    mut v_cfgs_7650_: *mut LeanObject,
    mut v_onErr_7651_: *mut LeanObject,
    mut v_logExceptions_7652_: u8,
    mut v_a_7653_: *mut LeanObject,
    mut v_a_7654_: *mut LeanObject,
    mut v_a_7655_: *mut LeanObject,
    mut v_a_7656_: *mut LeanObject,
    mut v_a_7657_: *mut LeanObject,
    mut v_a_7658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7660_: *mut LeanObject = core::ptr::null_mut();
    v___x_7660_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_7648_, v_logExceptions_7652_, v_onErr_7651_, v_init_7649_, v_cfgs_7650_, v_a_7653_, v_a_7654_, v_a_7655_, v_a_7656_, v_a_7657_, v_a_7658_);
    return v___x_7660_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___boxed(
    mut v_00_u03b1_7661_: *mut LeanObject,
    mut v_eval_7662_: *mut LeanObject,
    mut v_init_7663_: *mut LeanObject,
    mut v_cfgs_7664_: *mut LeanObject,
    mut v_onErr_7665_: *mut LeanObject,
    mut v_logExceptions_7666_: *mut LeanObject,
    mut v_a_7667_: *mut LeanObject,
    mut v_a_7668_: *mut LeanObject,
    mut v_a_7669_: *mut LeanObject,
    mut v_a_7670_: *mut LeanObject,
    mut v_a_7671_: *mut LeanObject,
    mut v_a_7672_: *mut LeanObject,
    mut v_a_7673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7674_: u8 = 0;
    let mut v_res_7675_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7674_ = (lean_unbox(v_logExceptions_7666_) as u8);
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
    lean_dec(v_a_7672_);
    lean_dec_ref(v_a_7671_);
    lean_dec(v_a_7670_);
    lean_dec_ref(v_a_7669_);
    lean_dec(v_a_7668_);
    lean_dec_ref(v_a_7667_);
    lean_dec_ref(v_cfgs_7664_);
    return v_res_7675_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(
    mut v_x_7676_: *mut LeanObject,
) -> u8 {
    let mut v___x_7677_: u8 = 0;
    v___x_7677_ = 0;
    return v___x_7677_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed(
    mut v_x_7678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7679_: u8 = 0;
    let mut v_r_7680_: *mut LeanObject = core::ptr::null_mut();
    v_res_7679_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(v_x_7678_);
    lean_dec(v_x_7678_);
    v_r_7680_ = lean_box((v_res_7679_) as usize);
    return v_r_7680_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(
    mut v___x_7681_: *mut LeanObject,
    mut v_ctx_x3f_7682_: *mut LeanObject,
    mut v_sz_7683_: usize,
    mut v_i_7684_: usize,
    mut v_bs_7685_: *mut LeanObject,
    mut v___y_7686_: *mut LeanObject,
    mut v___y_7687_: *mut LeanObject,
    mut v___y_7688_: *mut LeanObject,
    mut v___y_7689_: *mut LeanObject,
    mut v___y_7690_: *mut LeanObject,
    mut v___y_7691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7693_: u8 = 0;
    let mut v___x_7694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_7695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: usize = 0;
    let mut v___x_7704_: usize = 0;
    let mut v___x_7705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_7707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7713_: u8 = 0;
    let mut v___x_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7693_ = lean_usize_dec_lt(v_i_7684_, v_sz_7683_);
                if v___x_7693_ == 0 {
                    lean_dec_ref(v_ctx_x3f_7682_);
                    v___x_7694_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7694_, 0, v_bs_7685_);
                    return v___x_7694_;
                } else {
                    v_assignment_7695_ = lean_ctor_get(v___x_7681_, 0);
                    lean_inc_ref(v_ctx_x3f_7682_);
                    lean_inc(v___y_7691_);
                    lean_inc_ref(v___y_7690_);
                    lean_inc(v___y_7689_);
                    lean_inc_ref(v___y_7688_);
                    lean_inc(v___y_7687_);
                    lean_inc_ref(v___y_7686_);
                    v___x_7696_ = lean_apply_7(
                        v_ctx_x3f_7682_,
                        v___y_7686_,
                        v___y_7687_,
                        v___y_7688_,
                        v___y_7689_,
                        v___y_7690_,
                        v___y_7691_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_7696_) == 0 {
                        v_a_7697_ = lean_ctor_get(v___x_7696_, 0);
                        lean_inc(v_a_7697_);
                        lean_dec_ref_known(v___x_7696_, 1);
                        v_v_7698_ = lean_array_uget(v_bs_7685_, v_i_7684_);
                        v___x_7699_ = lean_unsigned_to_nat(0);
                        v_bs_x27_7700_ = lean_array_uset(v_bs_7685_, v_i_7684_, v___x_7699_);
                        v_tree_7707_ =
                            l_Lean_Elab_InfoTree_substitute(v_v_7698_, v_assignment_7695_);
                        if lean_obj_tag(v_a_7697_) == 0 {
                            v_a_7702_ = v_tree_7707_;
                            state = 1;
                            continue;
                        } else {
                            v_val_7708_ = lean_ctor_get(v_a_7697_, 0);
                            lean_inc(v_val_7708_);
                            lean_dec_ref_known(v_a_7697_, 1);
                            v___x_7709_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_7709_, 0, v_val_7708_);
                            lean_ctor_set(v___x_7709_, 1, v_tree_7707_);
                            v_a_7702_ = v___x_7709_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_bs_7685_);
                        lean_dec_ref(v_ctx_x3f_7682_);
                        v_a_7710_ = lean_ctor_get(v___x_7696_, 0);
                        v_isSharedCheck_7717_ = (!lean_is_exclusive(v___x_7696_)) as u8;
                        if v_isSharedCheck_7717_ == 0 {
                            v___x_7712_ = v___x_7696_;
                            v_isShared_7713_ = v_isSharedCheck_7717_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_7710_);
                            lean_dec(v___x_7696_);
                            v___x_7712_ = lean_box(0);
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
                    v_reuseFailAlloc_7716_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7716_, 0, v_a_7710_);
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
    mut v___x_7718_: *mut LeanObject,
    mut v_ctx_x3f_7719_: *mut LeanObject,
    mut v_sz_7720_: *mut LeanObject,
    mut v_i_7721_: *mut LeanObject,
    mut v_bs_7722_: *mut LeanObject,
    mut v___y_7723_: *mut LeanObject,
    mut v___y_7724_: *mut LeanObject,
    mut v___y_7725_: *mut LeanObject,
    mut v___y_7726_: *mut LeanObject,
    mut v___y_7727_: *mut LeanObject,
    mut v___y_7728_: *mut LeanObject,
    mut v___y_7729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7730_: usize = 0;
    let mut v_i_boxed_7731_: usize = 0;
    let mut v_res_7732_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7730_ = lean_unbox_usize(v_sz_7720_);
    lean_dec(v_sz_7720_);
    v_i_boxed_7731_ = lean_unbox_usize(v_i_7721_);
    lean_dec(v_i_7721_);
    v_res_7732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_7718_, v_ctx_x3f_7719_, v_sz_boxed_7730_, v_i_boxed_7731_, v_bs_7722_, v___y_7723_, v___y_7724_, v___y_7725_, v___y_7726_, v___y_7727_, v___y_7728_);
    lean_dec(v___y_7728_);
    lean_dec_ref(v___y_7727_);
    lean_dec(v___y_7726_);
    lean_dec_ref(v___y_7725_);
    lean_dec(v___y_7724_);
    lean_dec_ref(v___y_7723_);
    lean_dec_ref(v___x_7718_);
    return v_res_7732_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(
    mut v___x_7733_: *mut LeanObject,
    mut v_ctx_x3f_7734_: *mut LeanObject,
    mut v_x_7735_: *mut LeanObject,
    mut v___y_7736_: *mut LeanObject,
    mut v___y_7737_: *mut LeanObject,
    mut v___y_7738_: *mut LeanObject,
    mut v___y_7739_: *mut LeanObject,
    mut v___y_7740_: *mut LeanObject,
    mut v___y_7741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_7743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7746_: u8 = 0;
    let mut v_sz_7747_: usize = 0;
    let mut v___x_7748_: usize = 0;
    let mut v___x_7749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7753_: u8 = 0;
    let mut v___x_7755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7760_: u8 = 0;
    let mut v_a_7761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7764_: u8 = 0;
    let mut v___x_7766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7768_: u8 = 0;
    let mut v_isSharedCheck_7769_: u8 = 0;
    let mut v_vs_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7773_: u8 = 0;
    let mut v_sz_7774_: usize = 0;
    let mut v___x_7775_: usize = 0;
    let mut v___x_7776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7780_: u8 = 0;
    let mut v___x_7782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7787_: u8 = 0;
    let mut v_a_7788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7791_: u8 = 0;
    let mut v___x_7793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7795_: u8 = 0;
    let mut v_isSharedCheck_7796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7735_) == 0 {
                    v_cs_7743_ = lean_ctor_get(v_x_7735_, 0);
                    v_isSharedCheck_7769_ = (!lean_is_exclusive(v_x_7735_)) as u8;
                    if v_isSharedCheck_7769_ == 0 {
                        v___x_7745_ = v_x_7735_;
                        v_isShared_7746_ = v_isSharedCheck_7769_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_7743_);
                        lean_dec(v_x_7735_);
                        v___x_7745_ = lean_box(0);
                        v_isShared_7746_ = v_isSharedCheck_7769_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_7770_ = lean_ctor_get(v_x_7735_, 0);
                    v_isSharedCheck_7796_ = (!lean_is_exclusive(v_x_7735_)) as u8;
                    if v_isSharedCheck_7796_ == 0 {
                        v___x_7772_ = v_x_7735_;
                        v_isShared_7773_ = v_isSharedCheck_7796_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_vs_7770_);
                        lean_dec(v_x_7735_);
                        v___x_7772_ = lean_box(0);
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
                if lean_obj_tag(v___x_7749_) == 0 {
                    v_a_7750_ = lean_ctor_get(v___x_7749_, 0);
                    v_isSharedCheck_7760_ = (!lean_is_exclusive(v___x_7749_)) as u8;
                    if v_isSharedCheck_7760_ == 0 {
                        v___x_7752_ = v___x_7749_;
                        v_isShared_7753_ = v_isSharedCheck_7760_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7750_);
                        lean_dec(v___x_7749_);
                        v___x_7752_ = lean_box(0);
                        v_isShared_7753_ = v_isSharedCheck_7760_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7745_);
                    v_a_7761_ = lean_ctor_get(v___x_7749_, 0);
                    v_isSharedCheck_7768_ = (!lean_is_exclusive(v___x_7749_)) as u8;
                    if v_isSharedCheck_7768_ == 0 {
                        v___x_7763_ = v___x_7749_;
                        v_isShared_7764_ = v_isSharedCheck_7768_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7761_);
                        lean_dec(v___x_7749_);
                        v___x_7763_ = lean_box(0);
                        v_isShared_7764_ = v_isSharedCheck_7768_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7746_ == 0 {
                    lean_ctor_set(v___x_7745_, 0, v_a_7750_);
                    v___x_7755_ = v___x_7745_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7759_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7759_, 0, v_a_7750_);
                    v___x_7755_ = v_reuseFailAlloc_7759_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7753_ == 0 {
                    lean_ctor_set(v___x_7752_, 0, v___x_7755_);
                    v___x_7757_ = v___x_7752_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7758_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7758_, 0, v___x_7755_);
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
                    v_reuseFailAlloc_7767_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7767_, 0, v_a_7761_);
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
                if lean_obj_tag(v___x_7776_) == 0 {
                    v_a_7777_ = lean_ctor_get(v___x_7776_, 0);
                    v_isSharedCheck_7787_ = (!lean_is_exclusive(v___x_7776_)) as u8;
                    if v_isSharedCheck_7787_ == 0 {
                        v___x_7779_ = v___x_7776_;
                        v_isShared_7780_ = v_isSharedCheck_7787_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_7777_);
                        lean_dec(v___x_7776_);
                        v___x_7779_ = lean_box(0);
                        v_isShared_7780_ = v_isSharedCheck_7787_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7772_);
                    v_a_7788_ = lean_ctor_get(v___x_7776_, 0);
                    v_isSharedCheck_7795_ = (!lean_is_exclusive(v___x_7776_)) as u8;
                    if v_isSharedCheck_7795_ == 0 {
                        v___x_7790_ = v___x_7776_;
                        v_isShared_7791_ = v_isSharedCheck_7795_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_7788_);
                        lean_dec(v___x_7776_);
                        v___x_7790_ = lean_box(0);
                        v_isShared_7791_ = v_isSharedCheck_7795_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_7773_ == 0 {
                    lean_ctor_set(v___x_7772_, 0, v_a_7777_);
                    v___x_7782_ = v___x_7772_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7786_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7786_, 0, v_a_7777_);
                    v___x_7782_ = v_reuseFailAlloc_7786_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_7780_ == 0 {
                    lean_ctor_set(v___x_7779_, 0, v___x_7782_);
                    v___x_7784_ = v___x_7779_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7785_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7785_, 0, v___x_7782_);
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
                    v_reuseFailAlloc_7794_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7794_, 0, v_a_7788_);
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
    mut v___x_7797_: *mut LeanObject,
    mut v_ctx_x3f_7798_: *mut LeanObject,
    mut v_sz_7799_: usize,
    mut v_i_7800_: usize,
    mut v_bs_7801_: *mut LeanObject,
    mut v___y_7802_: *mut LeanObject,
    mut v___y_7803_: *mut LeanObject,
    mut v___y_7804_: *mut LeanObject,
    mut v___y_7805_: *mut LeanObject,
    mut v___y_7806_: *mut LeanObject,
    mut v___y_7807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7809_: u8 = 0;
    let mut v___x_7810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7816_: usize = 0;
    let mut v___x_7817_: usize = 0;
    let mut v___x_7818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7823_: u8 = 0;
    let mut v___x_7825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7809_ = lean_usize_dec_lt(v_i_7800_, v_sz_7799_);
                if v___x_7809_ == 0 {
                    lean_dec_ref(v_ctx_x3f_7798_);
                    v___x_7810_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7810_, 0, v_bs_7801_);
                    return v___x_7810_;
                } else {
                    v_v_7811_ = lean_array_uget_borrowed(v_bs_7801_, v_i_7800_);
                    lean_inc(v_v_7811_);
                    lean_inc_ref(v_ctx_x3f_7798_);
                    v___x_7812_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_7797_, v_ctx_x3f_7798_, v_v_7811_, v___y_7802_, v___y_7803_, v___y_7804_, v___y_7805_, v___y_7806_, v___y_7807_);
                    if lean_obj_tag(v___x_7812_) == 0 {
                        v_a_7813_ = lean_ctor_get(v___x_7812_, 0);
                        lean_inc(v_a_7813_);
                        lean_dec_ref_known(v___x_7812_, 1);
                        v___x_7814_ = lean_unsigned_to_nat(0);
                        v_bs_x27_7815_ = lean_array_uset(v_bs_7801_, v_i_7800_, v___x_7814_);
                        v___x_7816_ = 1usize;
                        v___x_7817_ = lean_usize_add(v_i_7800_, v___x_7816_);
                        v___x_7818_ = lean_array_uset(v_bs_x27_7815_, v_i_7800_, v_a_7813_);
                        v_i_7800_ = v___x_7817_;
                        v_bs_7801_ = v___x_7818_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_7801_);
                        lean_dec_ref(v_ctx_x3f_7798_);
                        v_a_7820_ = lean_ctor_get(v___x_7812_, 0);
                        v_isSharedCheck_7827_ = (!lean_is_exclusive(v___x_7812_)) as u8;
                        if v_isSharedCheck_7827_ == 0 {
                            v___x_7822_ = v___x_7812_;
                            v_isShared_7823_ = v_isSharedCheck_7827_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7820_);
                            lean_dec(v___x_7812_);
                            v___x_7822_ = lean_box(0);
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
                    v_reuseFailAlloc_7826_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7826_, 0, v_a_7820_);
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
    mut v___x_7828_: *mut LeanObject,
    mut v_ctx_x3f_7829_: *mut LeanObject,
    mut v_sz_7830_: *mut LeanObject,
    mut v_i_7831_: *mut LeanObject,
    mut v_bs_7832_: *mut LeanObject,
    mut v___y_7833_: *mut LeanObject,
    mut v___y_7834_: *mut LeanObject,
    mut v___y_7835_: *mut LeanObject,
    mut v___y_7836_: *mut LeanObject,
    mut v___y_7837_: *mut LeanObject,
    mut v___y_7838_: *mut LeanObject,
    mut v___y_7839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7840_: usize = 0;
    let mut v_i_boxed_7841_: usize = 0;
    let mut v_res_7842_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7840_ = lean_unbox_usize(v_sz_7830_);
    lean_dec(v_sz_7830_);
    v_i_boxed_7841_ = lean_unbox_usize(v_i_7831_);
    lean_dec(v_i_7831_);
    v_res_7842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_7828_, v_ctx_x3f_7829_, v_sz_boxed_7840_, v_i_boxed_7841_, v_bs_7832_, v___y_7833_, v___y_7834_, v___y_7835_, v___y_7836_, v___y_7837_, v___y_7838_);
    lean_dec(v___y_7838_);
    lean_dec_ref(v___y_7837_);
    lean_dec(v___y_7836_);
    lean_dec_ref(v___y_7835_);
    lean_dec(v___y_7834_);
    lean_dec_ref(v___y_7833_);
    lean_dec_ref(v___x_7828_);
    return v_res_7842_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5___boxed(
    mut v___x_7843_: *mut LeanObject,
    mut v_ctx_x3f_7844_: *mut LeanObject,
    mut v_x_7845_: *mut LeanObject,
    mut v___y_7846_: *mut LeanObject,
    mut v___y_7847_: *mut LeanObject,
    mut v___y_7848_: *mut LeanObject,
    mut v___y_7849_: *mut LeanObject,
    mut v___y_7850_: *mut LeanObject,
    mut v___y_7851_: *mut LeanObject,
    mut v___y_7852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7853_: *mut LeanObject = core::ptr::null_mut();
    v_res_7853_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_7843_, v_ctx_x3f_7844_, v_x_7845_, v___y_7846_, v___y_7847_, v___y_7848_, v___y_7849_, v___y_7850_, v___y_7851_);
    lean_dec(v___y_7851_);
    lean_dec_ref(v___y_7850_);
    lean_dec(v___y_7849_);
    lean_dec_ref(v___y_7848_);
    lean_dec(v___y_7847_);
    lean_dec_ref(v___y_7846_);
    lean_dec_ref(v___x_7843_);
    return v_res_7853_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(
    mut v___x_7854_: *mut LeanObject,
    mut v_ctx_x3f_7855_: *mut LeanObject,
    mut v_t_7856_: *mut LeanObject,
    mut v___y_7857_: *mut LeanObject,
    mut v___y_7858_: *mut LeanObject,
    mut v___y_7859_: *mut LeanObject,
    mut v___y_7860_: *mut LeanObject,
    mut v___y_7861_: *mut LeanObject,
    mut v___y_7862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_7867_: usize = 0;
    let mut v_tailOff_7868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7871_: u8 = 0;
    let mut v___x_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7874_: usize = 0;
    let mut v___x_7875_: usize = 0;
    let mut v___x_7876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7880_: u8 = 0;
    let mut v___x_7882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7887_: u8 = 0;
    let mut v_a_7888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7891_: u8 = 0;
    let mut v___x_7893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7895_: u8 = 0;
    let mut v_a_7896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7899_: u8 = 0;
    let mut v___x_7901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7903_: u8 = 0;
    let mut v_isSharedCheck_7904_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_7864_ = lean_ctor_get(v_t_7856_, 0);
                v_tail_7865_ = lean_ctor_get(v_t_7856_, 1);
                v_size_7866_ = lean_ctor_get(v_t_7856_, 2);
                v_shift_7867_ = lean_ctor_get_usize(v_t_7856_, 4);
                v_tailOff_7868_ = lean_ctor_get(v_t_7856_, 3);
                v_isSharedCheck_7904_ = (!lean_is_exclusive(v_t_7856_)) as u8;
                if v_isSharedCheck_7904_ == 0 {
                    v___x_7870_ = v_t_7856_;
                    v_isShared_7871_ = v_isSharedCheck_7904_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_7868_);
                    lean_inc(v_size_7866_);
                    lean_inc(v_tail_7865_);
                    lean_inc(v_root_7864_);
                    lean_dec(v_t_7856_);
                    v___x_7870_ = lean_box(0);
                    v_isShared_7871_ = v_isSharedCheck_7904_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_ctx_x3f_7855_);
                v___x_7872_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_7854_, v_ctx_x3f_7855_, v_root_7864_, v___y_7857_, v___y_7858_, v___y_7859_, v___y_7860_, v___y_7861_, v___y_7862_);
                if lean_obj_tag(v___x_7872_) == 0 {
                    v_a_7873_ = lean_ctor_get(v___x_7872_, 0);
                    lean_inc(v_a_7873_);
                    lean_dec_ref_known(v___x_7872_, 1);
                    v_sz_7874_ = lean_array_size(v_tail_7865_);
                    v___x_7875_ = 0usize;
                    v___x_7876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_7854_, v_ctx_x3f_7855_, v_sz_7874_, v___x_7875_, v_tail_7865_, v___y_7857_, v___y_7858_, v___y_7859_, v___y_7860_, v___y_7861_, v___y_7862_);
                    if lean_obj_tag(v___x_7876_) == 0 {
                        v_a_7877_ = lean_ctor_get(v___x_7876_, 0);
                        v_isSharedCheck_7887_ = (!lean_is_exclusive(v___x_7876_)) as u8;
                        if v_isSharedCheck_7887_ == 0 {
                            v___x_7879_ = v___x_7876_;
                            v_isShared_7880_ = v_isSharedCheck_7887_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_7877_);
                            lean_dec(v___x_7876_);
                            v___x_7879_ = lean_box(0);
                            v_isShared_7880_ = v_isSharedCheck_7887_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_7873_);
                        lean_del_object(v___x_7870_);
                        lean_dec(v_tailOff_7868_);
                        lean_dec(v_size_7866_);
                        v_a_7888_ = lean_ctor_get(v___x_7876_, 0);
                        v_isSharedCheck_7895_ = (!lean_is_exclusive(v___x_7876_)) as u8;
                        if v_isSharedCheck_7895_ == 0 {
                            v___x_7890_ = v___x_7876_;
                            v_isShared_7891_ = v_isSharedCheck_7895_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_7888_);
                            lean_dec(v___x_7876_);
                            v___x_7890_ = lean_box(0);
                            v_isShared_7891_ = v_isSharedCheck_7895_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_7870_);
                    lean_dec(v_tailOff_7868_);
                    lean_dec(v_size_7866_);
                    lean_dec_ref(v_tail_7865_);
                    lean_dec_ref(v_ctx_x3f_7855_);
                    v_a_7896_ = lean_ctor_get(v___x_7872_, 0);
                    v_isSharedCheck_7903_ = (!lean_is_exclusive(v___x_7872_)) as u8;
                    if v_isSharedCheck_7903_ == 0 {
                        v___x_7898_ = v___x_7872_;
                        v_isShared_7899_ = v_isSharedCheck_7903_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_7896_);
                        lean_dec(v___x_7872_);
                        v___x_7898_ = lean_box(0);
                        v_isShared_7899_ = v_isSharedCheck_7903_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7871_ == 0 {
                    lean_ctor_set(v___x_7870_, 1, v_a_7877_);
                    lean_ctor_set(v___x_7870_, 0, v_a_7873_);
                    v___x_7882_ = v___x_7870_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7886_ =
                        lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7886_, 0, v_a_7873_);
                    lean_ctor_set(v_reuseFailAlloc_7886_, 1, v_a_7877_);
                    lean_ctor_set(v_reuseFailAlloc_7886_, 2, v_size_7866_);
                    lean_ctor_set(v_reuseFailAlloc_7886_, 3, v_tailOff_7868_);
                    lean_ctor_set_usize(v_reuseFailAlloc_7886_, 4, v_shift_7867_);
                    v___x_7882_ = v_reuseFailAlloc_7886_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7880_ == 0 {
                    lean_ctor_set(v___x_7879_, 0, v___x_7882_);
                    v___x_7884_ = v___x_7879_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7885_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7885_, 0, v___x_7882_);
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
                    v_reuseFailAlloc_7894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7894_, 0, v_a_7888_);
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
                    v_reuseFailAlloc_7902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7902_, 0, v_a_7896_);
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
    mut v___x_7905_: *mut LeanObject,
    mut v_ctx_x3f_7906_: *mut LeanObject,
    mut v_t_7907_: *mut LeanObject,
    mut v___y_7908_: *mut LeanObject,
    mut v___y_7909_: *mut LeanObject,
    mut v___y_7910_: *mut LeanObject,
    mut v___y_7911_: *mut LeanObject,
    mut v___y_7912_: *mut LeanObject,
    mut v___y_7913_: *mut LeanObject,
    mut v___y_7914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7915_: *mut LeanObject = core::ptr::null_mut();
    v_res_7915_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v___x_7905_, v_ctx_x3f_7906_, v_t_7907_, v___y_7908_, v___y_7909_, v___y_7910_, v___y_7911_, v___y_7912_, v___y_7913_);
    lean_dec(v___y_7913_);
    lean_dec_ref(v___y_7912_);
    lean_dec(v___y_7911_);
    lean_dec_ref(v___y_7910_);
    lean_dec(v___y_7909_);
    lean_dec_ref(v___y_7908_);
    lean_dec_ref(v___x_7905_);
    return v_res_7915_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(
    mut v___y_7916_: *mut LeanObject,
    mut v_ctx_x3f_7917_: *mut LeanObject,
    mut v___y_7918_: *mut LeanObject,
    mut v___y_7919_: *mut LeanObject,
    mut v___y_7920_: *mut LeanObject,
    mut v___y_7921_: *mut LeanObject,
    mut v___y_7922_: *mut LeanObject,
    mut v_a_7923_: *mut LeanObject,
    mut v_a_x3f_7924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_7927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_7928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7933_: u8 = 0;
    let mut v___x_7934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_7935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_7938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_7940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_7941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_7942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7946_: u8 = 0;
    let mut v_enabled_7947_: u8 = 0;
    let mut v_assignment_7948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_7949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7952_: u8 = 0;
    let mut v___x_7953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7965_: u8 = 0;
    let mut v_unused_7966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7967_: u8 = 0;
    let mut v_isSharedCheck_7968_: u8 = 0;
    let mut v_a_7969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7972_: u8 = 0;
    let mut v___x_7974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7926_ = lean_st_ref_get(v___y_7916_);
                v_infoState_7927_ = lean_ctor_get(v___x_7926_, 7);
                lean_inc_ref(v_infoState_7927_);
                lean_dec(v___x_7926_);
                v_trees_7928_ = lean_ctor_get(v_infoState_7927_, 2);
                lean_inc_ref(v_trees_7928_);
                v___x_7929_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v_infoState_7927_, v_ctx_x3f_7917_, v_trees_7928_, v___y_7918_, v___y_7919_, v___y_7920_, v___y_7921_, v___y_7922_, v___y_7916_);
                lean_dec_ref(v_infoState_7927_);
                if lean_obj_tag(v___x_7929_) == 0 {
                    v_a_7930_ = lean_ctor_get(v___x_7929_, 0);
                    v_isSharedCheck_7968_ = (!lean_is_exclusive(v___x_7929_)) as u8;
                    if v_isSharedCheck_7968_ == 0 {
                        v___x_7932_ = v___x_7929_;
                        v_isShared_7933_ = v_isSharedCheck_7968_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7930_);
                        lean_dec(v___x_7929_);
                        v___x_7932_ = lean_box(0);
                        v_isShared_7933_ = v_isSharedCheck_7968_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_7923_);
                    v_a_7969_ = lean_ctor_get(v___x_7929_, 0);
                    v_isSharedCheck_7976_ = (!lean_is_exclusive(v___x_7929_)) as u8;
                    if v_isSharedCheck_7976_ == 0 {
                        v___x_7971_ = v___x_7929_;
                        v_isShared_7972_ = v_isSharedCheck_7976_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_7969_);
                        lean_dec(v___x_7929_);
                        v___x_7971_ = lean_box(0);
                        v_isShared_7972_ = v_isSharedCheck_7976_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7934_ = lean_st_ref_take(v___y_7916_);
                v_infoState_7935_ = lean_ctor_get(v___x_7934_, 7);
                v_env_7936_ = lean_ctor_get(v___x_7934_, 0);
                v_nextMacroScope_7937_ = lean_ctor_get(v___x_7934_, 1);
                v_ngen_7938_ = lean_ctor_get(v___x_7934_, 2);
                v_auxDeclNGen_7939_ = lean_ctor_get(v___x_7934_, 3);
                v_traceState_7940_ = lean_ctor_get(v___x_7934_, 4);
                v_cache_7941_ = lean_ctor_get(v___x_7934_, 5);
                v_messages_7942_ = lean_ctor_get(v___x_7934_, 6);
                v_snapshotTasks_7943_ = lean_ctor_get(v___x_7934_, 8);
                v_isSharedCheck_7967_ = (!lean_is_exclusive(v___x_7934_)) as u8;
                if v_isSharedCheck_7967_ == 0 {
                    v___x_7945_ = v___x_7934_;
                    v_isShared_7946_ = v_isSharedCheck_7967_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_7943_);
                    lean_inc(v_infoState_7935_);
                    lean_inc(v_messages_7942_);
                    lean_inc(v_cache_7941_);
                    lean_inc(v_traceState_7940_);
                    lean_inc(v_auxDeclNGen_7939_);
                    lean_inc(v_ngen_7938_);
                    lean_inc(v_nextMacroScope_7937_);
                    lean_inc(v_env_7936_);
                    lean_dec(v___x_7934_);
                    v___x_7945_ = lean_box(0);
                    v_isShared_7946_ = v_isSharedCheck_7967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_7947_ = lean_ctor_get_uint8(
                    v_infoState_7935_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_7948_ = lean_ctor_get(v_infoState_7935_, 0);
                v_lazyAssignment_7949_ = lean_ctor_get(v_infoState_7935_, 1);
                v_isSharedCheck_7965_ = (!lean_is_exclusive(v_infoState_7935_)) as u8;
                if v_isSharedCheck_7965_ == 0 {
                    v_unused_7966_ = lean_ctor_get(v_infoState_7935_, 2);
                    lean_dec(v_unused_7966_);
                    v___x_7951_ = v_infoState_7935_;
                    v_isShared_7952_ = v_isSharedCheck_7965_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_7949_);
                    lean_inc(v_assignment_7948_);
                    lean_dec(v_infoState_7935_);
                    v___x_7951_ = lean_box(0);
                    v_isShared_7952_ = v_isSharedCheck_7965_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7953_ = l_Lean_PersistentArray_append___redArg(v_a_7923_, v_a_7930_);
                lean_dec(v_a_7930_);
                if v_isShared_7952_ == 0 {
                    lean_ctor_set(v___x_7951_, 2, v___x_7953_);
                    v___x_7955_ = v___x_7951_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7964_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7964_, 0, v_assignment_7948_);
                    lean_ctor_set(v_reuseFailAlloc_7964_, 1, v_lazyAssignment_7949_);
                    lean_ctor_set(v_reuseFailAlloc_7964_, 2, v___x_7953_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7964_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_7947_,
                    );
                    v___x_7955_ = v_reuseFailAlloc_7964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7946_ == 0 {
                    lean_ctor_set(v___x_7945_, 7, v___x_7955_);
                    v___x_7957_ = v___x_7945_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7963_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7963_, 0, v_env_7936_);
                    lean_ctor_set(v_reuseFailAlloc_7963_, 1, v_nextMacroScope_7937_);
                    lean_ctor_set(v_reuseFailAlloc_7963_, 2, v_ngen_7938_);
                    lean_ctor_set(v_reuseFailAlloc_7963_, 3, v_auxDeclNGen_7939_);
                    lean_ctor_set(v_reuseFailAlloc_7963_, 4, v_traceState_7940_);
                    lean_ctor_set(v_reuseFailAlloc_7963_, 5, v_cache_7941_);
                    lean_ctor_set(v_reuseFailAlloc_7963_, 6, v_messages_7942_);
                    lean_ctor_set(v_reuseFailAlloc_7963_, 7, v___x_7955_);
                    lean_ctor_set(v_reuseFailAlloc_7963_, 8, v_snapshotTasks_7943_);
                    v___x_7957_ = v_reuseFailAlloc_7963_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7958_ = lean_st_ref_set(v___y_7916_, v___x_7957_);
                v___x_7959_ = lean_box(0);
                if v_isShared_7933_ == 0 {
                    lean_ctor_set(v___x_7932_, 0, v___x_7959_);
                    v___x_7961_ = v___x_7932_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7962_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7962_, 0, v___x_7959_);
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
                    v_reuseFailAlloc_7975_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7975_, 0, v_a_7969_);
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
    mut v___y_7977_: *mut LeanObject,
    mut v_ctx_x3f_7978_: *mut LeanObject,
    mut v___y_7979_: *mut LeanObject,
    mut v___y_7980_: *mut LeanObject,
    mut v___y_7981_: *mut LeanObject,
    mut v___y_7982_: *mut LeanObject,
    mut v___y_7983_: *mut LeanObject,
    mut v_a_7984_: *mut LeanObject,
    mut v_a_x3f_7985_: *mut LeanObject,
    mut v___y_7986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7987_: *mut LeanObject = core::ptr::null_mut();
    v_res_7987_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_7977_, v_ctx_x3f_7978_, v___y_7979_, v___y_7980_, v___y_7981_, v___y_7982_, v___y_7983_, v_a_7984_, v_a_x3f_7985_);
    lean_dec(v_a_x3f_7985_);
    lean_dec_ref(v___y_7983_);
    lean_dec(v___y_7982_);
    lean_dec_ref(v___y_7981_);
    lean_dec(v___y_7980_);
    lean_dec_ref(v___y_7979_);
    lean_dec(v___y_7977_);
    return v_res_7987_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(
    mut v___y_7988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_7991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_7994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_7997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_7999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_8000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_8001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_8002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8005_: u8 = 0;
    let mut v_enabled_8006_: u8 = 0;
    let mut v_assignment_8007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_8008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8011_: u8 = 0;
    let mut v___x_8012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8023_: u8 = 0;
    let mut v_unused_8024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7990_ = lean_st_ref_get(v___y_7988_);
                v_infoState_7991_ = lean_ctor_get(v___x_7990_, 7);
                lean_inc_ref(v_infoState_7991_);
                lean_dec(v___x_7990_);
                v_trees_7992_ = lean_ctor_get(v_infoState_7991_, 2);
                lean_inc_ref(v_trees_7992_);
                lean_dec_ref(v_infoState_7991_);
                v___x_7993_ = lean_st_ref_take(v___y_7988_);
                v_infoState_7994_ = lean_ctor_get(v___x_7993_, 7);
                v_env_7995_ = lean_ctor_get(v___x_7993_, 0);
                v_nextMacroScope_7996_ = lean_ctor_get(v___x_7993_, 1);
                v_ngen_7997_ = lean_ctor_get(v___x_7993_, 2);
                v_auxDeclNGen_7998_ = lean_ctor_get(v___x_7993_, 3);
                v_traceState_7999_ = lean_ctor_get(v___x_7993_, 4);
                v_cache_8000_ = lean_ctor_get(v___x_7993_, 5);
                v_messages_8001_ = lean_ctor_get(v___x_7993_, 6);
                v_snapshotTasks_8002_ = lean_ctor_get(v___x_7993_, 8);
                v_isSharedCheck_8025_ = (!lean_is_exclusive(v___x_7993_)) as u8;
                if v_isSharedCheck_8025_ == 0 {
                    v___x_8004_ = v___x_7993_;
                    v_isShared_8005_ = v_isSharedCheck_8025_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_8002_);
                    lean_inc(v_infoState_7994_);
                    lean_inc(v_messages_8001_);
                    lean_inc(v_cache_8000_);
                    lean_inc(v_traceState_7999_);
                    lean_inc(v_auxDeclNGen_7998_);
                    lean_inc(v_ngen_7997_);
                    lean_inc(v_nextMacroScope_7996_);
                    lean_inc(v_env_7995_);
                    lean_dec(v___x_7993_);
                    v___x_8004_ = lean_box(0);
                    v_isShared_8005_ = v_isSharedCheck_8025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_8006_ = lean_ctor_get_uint8(
                    v_infoState_7994_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_8007_ = lean_ctor_get(v_infoState_7994_, 0);
                v_lazyAssignment_8008_ = lean_ctor_get(v_infoState_7994_, 1);
                v_isSharedCheck_8023_ = (!lean_is_exclusive(v_infoState_7994_)) as u8;
                if v_isSharedCheck_8023_ == 0 {
                    v_unused_8024_ = lean_ctor_get(v_infoState_7994_, 2);
                    lean_dec(v_unused_8024_);
                    v___x_8010_ = v_infoState_7994_;
                    v_isShared_8011_ = v_isSharedCheck_8023_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_8008_);
                    lean_inc(v_assignment_8007_);
                    lean_dec(v_infoState_7994_);
                    v___x_8010_ = lean_box(0);
                    v_isShared_8011_ = v_isSharedCheck_8023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8012_ = lean_unsigned_to_nat(32);
                v___x_8013_ = lean_mk_empty_array_with_capacity(v___x_8012_);
                lean_dec_ref(v___x_8013_);
                v___x_8014_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
                if v_isShared_8011_ == 0 {
                    lean_ctor_set(v___x_8010_, 2, v___x_8014_);
                    v___x_8016_ = v___x_8010_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8022_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8022_, 0, v_assignment_8007_);
                    lean_ctor_set(v_reuseFailAlloc_8022_, 1, v_lazyAssignment_8008_);
                    lean_ctor_set(v_reuseFailAlloc_8022_, 2, v___x_8014_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8022_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_8006_,
                    );
                    v___x_8016_ = v_reuseFailAlloc_8022_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8005_ == 0 {
                    lean_ctor_set(v___x_8004_, 7, v___x_8016_);
                    v___x_8018_ = v___x_8004_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8021_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8021_, 0, v_env_7995_);
                    lean_ctor_set(v_reuseFailAlloc_8021_, 1, v_nextMacroScope_7996_);
                    lean_ctor_set(v_reuseFailAlloc_8021_, 2, v_ngen_7997_);
                    lean_ctor_set(v_reuseFailAlloc_8021_, 3, v_auxDeclNGen_7998_);
                    lean_ctor_set(v_reuseFailAlloc_8021_, 4, v_traceState_7999_);
                    lean_ctor_set(v_reuseFailAlloc_8021_, 5, v_cache_8000_);
                    lean_ctor_set(v_reuseFailAlloc_8021_, 6, v_messages_8001_);
                    lean_ctor_set(v_reuseFailAlloc_8021_, 7, v___x_8016_);
                    lean_ctor_set(v_reuseFailAlloc_8021_, 8, v_snapshotTasks_8002_);
                    v___x_8018_ = v_reuseFailAlloc_8021_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8019_ = lean_st_ref_set(v___y_7988_, v___x_8018_);
                v___x_8020_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8020_, 0, v_trees_7992_);
                return v___x_8020_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg___boxed(
    mut v___y_8026_: *mut LeanObject,
    mut v___y_8027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8028_: *mut LeanObject = core::ptr::null_mut();
    v_res_8028_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_8026_);
    lean_dec(v___y_8026_);
    return v_res_8028_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(
    mut v_x_8029_: *mut LeanObject,
    mut v_ctx_x3f_8030_: *mut LeanObject,
    mut v___y_8031_: *mut LeanObject,
    mut v___y_8032_: *mut LeanObject,
    mut v___y_8033_: *mut LeanObject,
    mut v___y_8034_: *mut LeanObject,
    mut v___y_8035_: *mut LeanObject,
    mut v___y_8036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_8039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_8040_: u8 = 0;
    let mut v___x_8041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_8044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8048_: u8 = 0;
    let mut v___x_8050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8054_: u8 = 0;
    let mut v___x_8056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8058_: u8 = 0;
    let mut v_unused_8059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8063_: u8 = 0;
    let mut v___x_8065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8067_: u8 = 0;
    let mut v_reuseFailAlloc_8068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8069_: u8 = 0;
    let mut v_a_8070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8075_: u8 = 0;
    let mut v___x_8077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8079_: u8 = 0;
    let mut v_unused_8080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8084_: u8 = 0;
    let mut v___x_8086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8038_ = lean_st_ref_get(v___y_8036_);
                v_infoState_8039_ = lean_ctor_get(v___x_8038_, 7);
                lean_inc_ref(v_infoState_8039_);
                lean_dec(v___x_8038_);
                v_enabled_8040_ = lean_ctor_get_uint8(
                    v_infoState_8039_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_8039_);
                if v_enabled_8040_ == 0 {
                    lean_dec_ref(v_ctx_x3f_8030_);
                    lean_inc(v___y_8036_);
                    lean_inc_ref(v___y_8035_);
                    lean_inc(v___y_8034_);
                    lean_inc_ref(v___y_8033_);
                    lean_inc(v___y_8032_);
                    lean_inc_ref(v___y_8031_);
                    v___x_8041_ = lean_apply_7(
                        v_x_8029_,
                        v___y_8031_,
                        v___y_8032_,
                        v___y_8033_,
                        v___y_8034_,
                        v___y_8035_,
                        v___y_8036_,
                        lean_box(0),
                    );
                    return v___x_8041_;
                } else {
                    v___x_8042_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_8036_);
                    v_a_8043_ = lean_ctor_get(v___x_8042_, 0);
                    lean_inc(v_a_8043_);
                    lean_dec_ref(v___x_8042_);
                    lean_inc(v___y_8036_);
                    lean_inc_ref(v___y_8035_);
                    lean_inc(v___y_8034_);
                    lean_inc_ref(v___y_8033_);
                    lean_inc(v___y_8032_);
                    lean_inc_ref(v___y_8031_);
                    v_r_8044_ = lean_apply_7(
                        v_x_8029_,
                        v___y_8031_,
                        v___y_8032_,
                        v___y_8033_,
                        v___y_8034_,
                        v___y_8035_,
                        v___y_8036_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_8044_) == 0 {
                        v_a_8045_ = lean_ctor_get(v_r_8044_, 0);
                        v_isSharedCheck_8069_ = (!lean_is_exclusive(v_r_8044_)) as u8;
                        if v_isSharedCheck_8069_ == 0 {
                            v___x_8047_ = v_r_8044_;
                            v_isShared_8048_ = v_isSharedCheck_8069_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8045_);
                            lean_dec(v_r_8044_);
                            v___x_8047_ = lean_box(0);
                            v_isShared_8048_ = v_isSharedCheck_8069_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_8070_ = lean_ctor_get(v_r_8044_, 0);
                        lean_inc(v_a_8070_);
                        lean_dec_ref_known(v_r_8044_, 1);
                        v___x_8071_ = lean_box(0);
                        v___x_8072_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_8036_, v_ctx_x3f_8030_, v___y_8031_, v___y_8032_, v___y_8033_, v___y_8034_, v___y_8035_, v_a_8043_, v___x_8071_);
                        if lean_obj_tag(v___x_8072_) == 0 {
                            v_isSharedCheck_8079_ = (!lean_is_exclusive(v___x_8072_)) as u8;
                            if v_isSharedCheck_8079_ == 0 {
                                v_unused_8080_ = lean_ctor_get(v___x_8072_, 0);
                                lean_dec(v_unused_8080_);
                                v___x_8074_ = v___x_8072_;
                                v_isShared_8075_ = v_isSharedCheck_8079_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_8072_);
                                v___x_8074_ = lean_box(0);
                                v_isShared_8075_ = v_isSharedCheck_8079_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_8070_);
                            v_a_8081_ = lean_ctor_get(v___x_8072_, 0);
                            v_isSharedCheck_8088_ = (!lean_is_exclusive(v___x_8072_)) as u8;
                            if v_isSharedCheck_8088_ == 0 {
                                v___x_8083_ = v___x_8072_;
                                v_isShared_8084_ = v_isSharedCheck_8088_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_8081_);
                                lean_dec(v___x_8072_);
                                v___x_8083_ = lean_box(0);
                                v_isShared_8084_ = v_isSharedCheck_8088_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_8045_);
                if v_isShared_8048_ == 0 {
                    lean_ctor_set_tag(v___x_8047_, 1);
                    v___x_8050_ = v___x_8047_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8068_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8068_, 0, v_a_8045_);
                    v___x_8050_ = v_reuseFailAlloc_8068_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8051_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_8036_, v_ctx_x3f_8030_, v___y_8031_, v___y_8032_, v___y_8033_, v___y_8034_, v___y_8035_, v_a_8043_, v___x_8050_);
                lean_dec_ref(v___x_8050_);
                if lean_obj_tag(v___x_8051_) == 0 {
                    v_isSharedCheck_8058_ = (!lean_is_exclusive(v___x_8051_)) as u8;
                    if v_isSharedCheck_8058_ == 0 {
                        v_unused_8059_ = lean_ctor_get(v___x_8051_, 0);
                        lean_dec(v_unused_8059_);
                        v___x_8053_ = v___x_8051_;
                        v_isShared_8054_ = v_isSharedCheck_8058_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_8051_);
                        v___x_8053_ = lean_box(0);
                        v_isShared_8054_ = v_isSharedCheck_8058_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_8045_);
                    v_a_8060_ = lean_ctor_get(v___x_8051_, 0);
                    v_isSharedCheck_8067_ = (!lean_is_exclusive(v___x_8051_)) as u8;
                    if v_isSharedCheck_8067_ == 0 {
                        v___x_8062_ = v___x_8051_;
                        v_isShared_8063_ = v_isSharedCheck_8067_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_8060_);
                        lean_dec(v___x_8051_);
                        v___x_8062_ = lean_box(0);
                        v_isShared_8063_ = v_isSharedCheck_8067_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_8054_ == 0 {
                    lean_ctor_set(v___x_8053_, 0, v_a_8045_);
                    v___x_8056_ = v___x_8053_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8057_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8057_, 0, v_a_8045_);
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
                    v_reuseFailAlloc_8066_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8066_, 0, v_a_8060_);
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
                    lean_ctor_set_tag(v___x_8074_, 1);
                    lean_ctor_set(v___x_8074_, 0, v_a_8070_);
                    v___x_8077_ = v___x_8074_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8078_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8078_, 0, v_a_8070_);
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
                    v_reuseFailAlloc_8087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8087_, 0, v_a_8081_);
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
    mut v_x_8089_: *mut LeanObject,
    mut v_ctx_x3f_8090_: *mut LeanObject,
    mut v___y_8091_: *mut LeanObject,
    mut v___y_8092_: *mut LeanObject,
    mut v___y_8093_: *mut LeanObject,
    mut v___y_8094_: *mut LeanObject,
    mut v___y_8095_: *mut LeanObject,
    mut v___y_8096_: *mut LeanObject,
    mut v___y_8097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8098_: *mut LeanObject = core::ptr::null_mut();
    v_res_8098_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_8089_, v_ctx_x3f_8090_, v___y_8091_, v___y_8092_, v___y_8093_, v___y_8094_, v___y_8095_, v___y_8096_);
    lean_dec(v___y_8096_);
    lean_dec_ref(v___y_8095_);
    lean_dec(v___y_8094_);
    lean_dec_ref(v___y_8093_);
    lean_dec(v___y_8092_);
    lean_dec_ref(v___y_8091_);
    return v_res_8098_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(
    mut v___y_8099_: *mut LeanObject,
    mut v___y_8100_: *mut LeanObject,
    mut v___y_8101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_8104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_8106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_8107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_8108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_8109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_8111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: *mut LeanObject = core::ptr::null_mut();
    v___x_8103_ = lean_st_ref_get(v___y_8101_);
    v_env_8104_ = lean_ctor_get(v___x_8103_, 0);
    lean_inc_ref(v_env_8104_);
    lean_dec(v___x_8103_);
    v___x_8105_ = lean_st_ref_get(v___y_8099_);
    v_mctx_8106_ = lean_ctor_get(v___x_8105_, 0);
    lean_inc_ref(v_mctx_8106_);
    lean_dec(v___x_8105_);
    v_options_8107_ = lean_ctor_get(v___y_8100_, 2);
    v_currNamespace_8108_ = lean_ctor_get(v___y_8100_, 6);
    v_openDecls_8109_ = lean_ctor_get(v___y_8100_, 7);
    v___x_8110_ = lean_st_ref_get(v___y_8101_);
    v_ngen_8111_ = lean_ctor_get(v___x_8110_, 2);
    lean_inc_ref(v_ngen_8111_);
    lean_dec(v___x_8110_);
    v___x_8112_ = lean_box(0);
    v___x_8113_ = l_Lean_instInhabitedFileMap_default;
    lean_inc(v_openDecls_8109_);
    lean_inc(v_currNamespace_8108_);
    lean_inc_ref(v_options_8107_);
    v___x_8114_ = lean_alloc_ctor(0, 8, (0) as u32);
    lean_ctor_set(v___x_8114_, 0, v_env_8104_);
    lean_ctor_set(v___x_8114_, 1, v___x_8112_);
    lean_ctor_set(v___x_8114_, 2, v___x_8113_);
    lean_ctor_set(v___x_8114_, 3, v_mctx_8106_);
    lean_ctor_set(v___x_8114_, 4, v_options_8107_);
    lean_ctor_set(v___x_8114_, 5, v_currNamespace_8108_);
    lean_ctor_set(v___x_8114_, 6, v_openDecls_8109_);
    lean_ctor_set(v___x_8114_, 7, v_ngen_8111_);
    v___x_8115_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8115_, 0, v___x_8114_);
    return v___x_8115_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg___boxed(
    mut v___y_8116_: *mut LeanObject,
    mut v___y_8117_: *mut LeanObject,
    mut v___y_8118_: *mut LeanObject,
    mut v___y_8119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8120_: *mut LeanObject = core::ptr::null_mut();
    v_res_8120_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_8116_, v___y_8117_, v___y_8118_);
    lean_dec(v___y_8118_);
    lean_dec_ref(v___y_8117_);
    lean_dec(v___y_8116_);
    return v_res_8120_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(
    mut v___y_8121_: *mut LeanObject,
    mut v___y_8122_: *mut LeanObject,
    mut v___y_8123_: *mut LeanObject,
    mut v___y_8124_: *mut LeanObject,
    mut v___y_8125_: *mut LeanObject,
    mut v___y_8126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8132_: u8 = 0;
    let mut v_fileMap_8133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_8134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_8135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_8136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_8137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_8138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_8139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8142_: u8 = 0;
    let mut v___x_8143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8150_: u8 = 0;
    let mut v_unused_8151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8128_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_8124_, v___y_8125_, v___y_8126_);
                v_a_8129_ = lean_ctor_get(v___x_8128_, 0);
                v_isSharedCheck_8153_ = (!lean_is_exclusive(v___x_8128_)) as u8;
                if v_isSharedCheck_8153_ == 0 {
                    v___x_8131_ = v___x_8128_;
                    v_isShared_8132_ = v_isSharedCheck_8153_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_8129_);
                    lean_dec(v___x_8128_);
                    v___x_8131_ = lean_box(0);
                    v_isShared_8132_ = v_isSharedCheck_8153_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_8133_ = lean_ctor_get(v___y_8125_, 1);
                v_env_8134_ = lean_ctor_get(v_a_8129_, 0);
                v_mctx_8135_ = lean_ctor_get(v_a_8129_, 3);
                v_options_8136_ = lean_ctor_get(v_a_8129_, 4);
                v_currNamespace_8137_ = lean_ctor_get(v_a_8129_, 5);
                v_openDecls_8138_ = lean_ctor_get(v_a_8129_, 6);
                v_ngen_8139_ = lean_ctor_get(v_a_8129_, 7);
                v_isSharedCheck_8150_ = (!lean_is_exclusive(v_a_8129_)) as u8;
                if v_isSharedCheck_8150_ == 0 {
                    v_unused_8151_ = lean_ctor_get(v_a_8129_, 2);
                    lean_dec(v_unused_8151_);
                    v_unused_8152_ = lean_ctor_get(v_a_8129_, 1);
                    lean_dec(v_unused_8152_);
                    v___x_8141_ = v_a_8129_;
                    v_isShared_8142_ = v_isSharedCheck_8150_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_ngen_8139_);
                    lean_inc(v_openDecls_8138_);
                    lean_inc(v_currNamespace_8137_);
                    lean_inc(v_options_8136_);
                    lean_inc(v_mctx_8135_);
                    lean_inc(v_env_8134_);
                    lean_dec(v_a_8129_);
                    v___x_8141_ = lean_box(0);
                    v_isShared_8142_ = v_isSharedCheck_8150_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8143_ = lean_box(0);
                lean_inc_ref(v_fileMap_8133_);
                if v_isShared_8142_ == 0 {
                    lean_ctor_set(v___x_8141_, 2, v_fileMap_8133_);
                    lean_ctor_set(v___x_8141_, 1, v___x_8143_);
                    v___x_8145_ = v___x_8141_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8149_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8149_, 0, v_env_8134_);
                    lean_ctor_set(v_reuseFailAlloc_8149_, 1, v___x_8143_);
                    lean_ctor_set(v_reuseFailAlloc_8149_, 2, v_fileMap_8133_);
                    lean_ctor_set(v_reuseFailAlloc_8149_, 3, v_mctx_8135_);
                    lean_ctor_set(v_reuseFailAlloc_8149_, 4, v_options_8136_);
                    lean_ctor_set(v_reuseFailAlloc_8149_, 5, v_currNamespace_8137_);
                    lean_ctor_set(v_reuseFailAlloc_8149_, 6, v_openDecls_8138_);
                    lean_ctor_set(v_reuseFailAlloc_8149_, 7, v_ngen_8139_);
                    v___x_8145_ = v_reuseFailAlloc_8149_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8132_ == 0 {
                    lean_ctor_set(v___x_8131_, 0, v___x_8145_);
                    v___x_8147_ = v___x_8131_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8148_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8148_, 0, v___x_8145_);
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
    mut v___y_8154_: *mut LeanObject,
    mut v___y_8155_: *mut LeanObject,
    mut v___y_8156_: *mut LeanObject,
    mut v___y_8157_: *mut LeanObject,
    mut v___y_8158_: *mut LeanObject,
    mut v___y_8159_: *mut LeanObject,
    mut v___y_8160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8161_: *mut LeanObject = core::ptr::null_mut();
    v_res_8161_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_8154_, v___y_8155_, v___y_8156_, v___y_8157_, v___y_8158_, v___y_8159_);
    lean_dec(v___y_8159_);
    lean_dec_ref(v___y_8158_);
    lean_dec(v___y_8157_);
    lean_dec_ref(v___y_8156_);
    lean_dec(v___y_8155_);
    lean_dec_ref(v___y_8154_);
    return v_res_8161_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(
    mut v___y_8162_: *mut LeanObject,
    mut v___y_8163_: *mut LeanObject,
    mut v___y_8164_: *mut LeanObject,
    mut v___y_8165_: *mut LeanObject,
    mut v___y_8166_: *mut LeanObject,
    mut v___y_8167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8173_: u8 = 0;
    let mut v___x_8174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8169_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_8162_, v___y_8163_, v___y_8164_, v___y_8165_, v___y_8166_, v___y_8167_);
                v_a_8170_ = lean_ctor_get(v___x_8169_, 0);
                v_isSharedCheck_8179_ = (!lean_is_exclusive(v___x_8169_)) as u8;
                if v_isSharedCheck_8179_ == 0 {
                    v___x_8172_ = v___x_8169_;
                    v_isShared_8173_ = v_isSharedCheck_8179_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_8170_);
                    lean_dec(v___x_8169_);
                    v___x_8172_ = lean_box(0);
                    v_isShared_8173_ = v_isSharedCheck_8179_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8174_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8174_, 0, v_a_8170_);
                v___x_8175_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_8175_, 0, v___x_8174_);
                if v_isShared_8173_ == 0 {
                    lean_ctor_set(v___x_8172_, 0, v___x_8175_);
                    v___x_8177_ = v___x_8172_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8178_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8178_, 0, v___x_8175_);
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
    mut v___y_8180_: *mut LeanObject,
    mut v___y_8181_: *mut LeanObject,
    mut v___y_8182_: *mut LeanObject,
    mut v___y_8183_: *mut LeanObject,
    mut v___y_8184_: *mut LeanObject,
    mut v___y_8185_: *mut LeanObject,
    mut v___y_8186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8187_: *mut LeanObject = core::ptr::null_mut();
    v_res_8187_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(v___y_8180_, v___y_8181_, v___y_8182_, v___y_8183_, v___y_8184_, v___y_8185_);
    lean_dec(v___y_8185_);
    lean_dec_ref(v___y_8184_);
    lean_dec(v___y_8183_);
    lean_dec_ref(v___y_8182_);
    lean_dec(v___y_8181_);
    lean_dec_ref(v___y_8180_);
    return v_res_8187_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(
    mut v_x_8189_: *mut LeanObject,
    mut v___y_8190_: *mut LeanObject,
    mut v___y_8191_: *mut LeanObject,
    mut v___y_8192_: *mut LeanObject,
    mut v___y_8193_: *mut LeanObject,
    mut v___y_8194_: *mut LeanObject,
    mut v___y_8195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8198_: *mut LeanObject = core::ptr::null_mut();
    v___f_8197_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0;
    v___x_8198_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_8189_, v___f_8197_, v___y_8190_, v___y_8191_, v___y_8192_, v___y_8193_, v___y_8194_, v___y_8195_);
    return v___x_8198_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___boxed(
    mut v_x_8199_: *mut LeanObject,
    mut v___y_8200_: *mut LeanObject,
    mut v___y_8201_: *mut LeanObject,
    mut v___y_8202_: *mut LeanObject,
    mut v___y_8203_: *mut LeanObject,
    mut v___y_8204_: *mut LeanObject,
    mut v___y_8205_: *mut LeanObject,
    mut v___y_8206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8207_: *mut LeanObject = core::ptr::null_mut();
    v_res_8207_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_8199_, v___y_8200_, v___y_8201_, v___y_8202_, v___y_8203_, v___y_8204_, v___y_8205_);
    lean_dec(v___y_8205_);
    lean_dec_ref(v___y_8204_);
    lean_dec(v___y_8203_);
    lean_dec_ref(v___y_8202_);
    lean_dec(v___y_8201_);
    lean_dec_ref(v___y_8200_);
    return v_res_8207_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(
    mut v_00_u03b1_8208_: *mut LeanObject,
    mut v_x_8209_: *mut LeanObject,
    mut v___y_8210_: *mut LeanObject,
    mut v___y_8211_: *mut LeanObject,
    mut v___y_8212_: *mut LeanObject,
    mut v___y_8213_: *mut LeanObject,
    mut v___y_8214_: *mut LeanObject,
    mut v___y_8215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8217_: *mut LeanObject = core::ptr::null_mut();
    v___x_8217_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_8209_, v___y_8210_, v___y_8211_, v___y_8212_, v___y_8213_, v___y_8214_, v___y_8215_);
    return v___x_8217_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed(
    mut v_00_u03b1_8218_: *mut LeanObject,
    mut v_x_8219_: *mut LeanObject,
    mut v___y_8220_: *mut LeanObject,
    mut v___y_8221_: *mut LeanObject,
    mut v___y_8222_: *mut LeanObject,
    mut v___y_8223_: *mut LeanObject,
    mut v___y_8224_: *mut LeanObject,
    mut v___y_8225_: *mut LeanObject,
    mut v___y_8226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8227_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_8225_);
    lean_dec_ref(v___y_8224_);
    lean_dec(v___y_8223_);
    lean_dec_ref(v___y_8222_);
    lean_dec(v___y_8221_);
    lean_dec_ref(v___y_8220_);
    return v_res_8227_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4() -> u64 {
    let mut v___x_8245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8246_: u64 = 0;
    v___x_8245_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3;
    v___x_8246_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_8245_);
    return v___x_8246_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5() -> *mut LeanObject {
    let mut v___x_8247_: u64 = 0;
    let mut v___x_8248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8249_: *mut LeanObject = core::ptr::null_mut();
    v___x_8247_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4,
    );
    v___x_8248_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3;
    v___x_8249_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_8249_, 0, v___x_8248_);
    lean_ctor_set_uint64(
        v___x_8249_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_8247_,
    );
    return v___x_8249_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6() -> *mut LeanObject {
    let mut v___x_8250_: u8 = 0;
    let mut v___x_8251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8256_: u8 = 0;
    let mut v___x_8257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8258_: *mut LeanObject = core::ptr::null_mut();
    v___x_8250_ = 1;
    v___x_8251_ = lean_unsigned_to_nat(0);
    v___x_8252_ = lean_box(0);
    v___x_8253_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1;
    v___x_8254_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2,
    );
    v___x_8255_ = lean_box(1);
    v___x_8256_ = 0;
    v___x_8257_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5,
    );
    v___x_8258_ = lean_alloc_ctor(0, 7, (4) as u32);
    lean_ctor_set(v___x_8258_, 0, v___x_8257_);
    lean_ctor_set(v___x_8258_, 1, v___x_8255_);
    lean_ctor_set(v___x_8258_, 2, v___x_8254_);
    lean_ctor_set(v___x_8258_, 3, v___x_8253_);
    lean_ctor_set(v___x_8258_, 4, v___x_8252_);
    lean_ctor_set(v___x_8258_, 5, v___x_8251_);
    lean_ctor_set(v___x_8258_, 6, v___x_8252_);
    lean_ctor_set_uint8(
        v___x_8258_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
        v___x_8256_,
    );
    lean_ctor_set_uint8(
        v___x_8258_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
        v___x_8256_,
    );
    lean_ctor_set_uint8(
        v___x_8258_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
        v___x_8256_,
    );
    lean_ctor_set_uint8(
        v___x_8258_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
        v___x_8250_,
    );
    return v___x_8258_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_8259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8261_: *mut LeanObject = core::ptr::null_mut();
    v___x_8259_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1,
    );
    v___x_8260_ = lean_unsigned_to_nat(0);
    v___x_8261_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_8261_, 0, v___x_8260_);
    lean_ctor_set(v___x_8261_, 1, v___x_8260_);
    lean_ctor_set(v___x_8261_, 2, v___x_8260_);
    lean_ctor_set(v___x_8261_, 3, v___x_8260_);
    lean_ctor_set(v___x_8261_, 4, v___x_8259_);
    lean_ctor_set(v___x_8261_, 5, v___x_8259_);
    lean_ctor_set(v___x_8261_, 6, v___x_8259_);
    lean_ctor_set(v___x_8261_, 7, v___x_8259_);
    lean_ctor_set(v___x_8261_, 8, v___x_8259_);
    lean_ctor_set(v___x_8261_, 9, v___x_8259_);
    return v___x_8261_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8() -> *mut LeanObject {
    let mut v___x_8262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8263_: *mut LeanObject = core::ptr::null_mut();
    v___x_8262_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1,
    );
    v___x_8263_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_8263_, 0, v___x_8262_);
    lean_ctor_set(v___x_8263_, 1, v___x_8262_);
    lean_ctor_set(v___x_8263_, 2, v___x_8262_);
    lean_ctor_set(v___x_8263_, 3, v___x_8262_);
    lean_ctor_set(v___x_8263_, 4, v___x_8262_);
    lean_ctor_set(v___x_8263_, 5, v___x_8262_);
    return v___x_8263_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9() -> *mut LeanObject {
    let mut v___x_8264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8265_: *mut LeanObject = core::ptr::null_mut();
    v___x_8264_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1,
    );
    v___x_8265_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_8265_, 0, v___x_8264_);
    lean_ctor_set(v___x_8265_, 1, v___x_8264_);
    lean_ctor_set(v___x_8265_, 2, v___x_8264_);
    lean_ctor_set(v___x_8265_, 3, v___x_8264_);
    lean_ctor_set(v___x_8265_, 4, v___x_8264_);
    return v___x_8265_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10() -> *mut LeanObject
{
    let mut v___x_8266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8271_: *mut LeanObject = core::ptr::null_mut();
    v___x_8266_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9,
    );
    v___x_8267_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_8268_ = lean_box(1);
    v___x_8269_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8,
    );
    v___x_8270_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once),
        _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7,
    );
    v___x_8271_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_8271_, 0, v___x_8270_);
    lean_ctor_set(v___x_8271_, 1, v___x_8269_);
    lean_ctor_set(v___x_8271_, 2, v___x_8268_);
    lean_ctor_set(v___x_8271_, 3, v___x_8267_);
    lean_ctor_set(v___x_8271_, 4, v___x_8266_);
    return v___x_8271_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___redArg(
    mut v_mx_8275_: *mut LeanObject,
    mut v_a_8276_: *mut LeanObject,
    mut v_a_8277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8289_: u8 = 0;
    let mut v___x_8290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8295_: u8 = 0;
    let mut v_a_8296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8299_: u8 = 0;
    let mut v___x_8301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8279_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2;
                v___x_8280_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6,
                );
                v___x_8281_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10,
                );
                v___x_8282_ = lean_st_mk_ref(v___x_8281_);
                v___x_8283_ = lean_alloc_closure(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed as *mut core::ffi::c_void, 9, 2);
                lean_closure_set(v___x_8283_, 0, lean_box(0));
                lean_closure_set(v___x_8283_, 1, v_mx_8275_);
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
                if lean_obj_tag(v___x_8285_) == 0 {
                    v_a_8286_ = lean_ctor_get(v___x_8285_, 0);
                    v_isSharedCheck_8295_ = (!lean_is_exclusive(v___x_8285_)) as u8;
                    if v_isSharedCheck_8295_ == 0 {
                        v___x_8288_ = v___x_8285_;
                        v_isShared_8289_ = v_isSharedCheck_8295_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8286_);
                        lean_dec(v___x_8285_);
                        v___x_8288_ = lean_box(0);
                        v_isShared_8289_ = v_isSharedCheck_8295_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_8282_);
                    v_a_8296_ = lean_ctor_get(v___x_8285_, 0);
                    v_isSharedCheck_8303_ = (!lean_is_exclusive(v___x_8285_)) as u8;
                    if v_isSharedCheck_8303_ == 0 {
                        v___x_8298_ = v___x_8285_;
                        v_isShared_8299_ = v_isSharedCheck_8303_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8296_);
                        lean_dec(v___x_8285_);
                        v___x_8298_ = lean_box(0);
                        v_isShared_8299_ = v_isSharedCheck_8303_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8290_ = lean_st_ref_get(v___x_8282_);
                lean_dec(v___x_8282_);
                lean_dec(v___x_8290_);
                v_fst_8291_ = lean_ctor_get(v_a_8286_, 0);
                lean_inc(v_fst_8291_);
                lean_dec(v_a_8286_);
                if v_isShared_8289_ == 0 {
                    lean_ctor_set(v___x_8288_, 0, v_fst_8291_);
                    v___x_8293_ = v___x_8288_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8294_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8294_, 0, v_fst_8291_);
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
                    v_reuseFailAlloc_8302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8302_, 0, v_a_8296_);
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
    mut v_mx_8304_: *mut LeanObject,
    mut v_a_8305_: *mut LeanObject,
    mut v_a_8306_: *mut LeanObject,
    mut v_a_8307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8308_: *mut LeanObject = core::ptr::null_mut();
    v_res_8308_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_8304_, v_a_8305_, v_a_8306_);
    lean_dec(v_a_8306_);
    lean_dec_ref(v_a_8305_);
    return v_res_8308_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab(
    mut v_00_u03b1_8309_: *mut LeanObject,
    mut v_mx_8310_: *mut LeanObject,
    mut v_a_8311_: *mut LeanObject,
    mut v_a_8312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8314_: *mut LeanObject = core::ptr::null_mut();
    v___x_8314_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_8310_, v_a_8311_, v_a_8312_);
    return v___x_8314_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_runConfigElab___boxed(
    mut v_00_u03b1_8315_: *mut LeanObject,
    mut v_mx_8316_: *mut LeanObject,
    mut v_a_8317_: *mut LeanObject,
    mut v_a_8318_: *mut LeanObject,
    mut v_a_8319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8320_: *mut LeanObject = core::ptr::null_mut();
    v_res_8320_ =
        l_Lean_Elab_ConfigEval_runConfigElab(v_00_u03b1_8315_, v_mx_8316_, v_a_8317_, v_a_8318_);
    lean_dec(v_a_8318_);
    lean_dec_ref(v_a_8317_);
    return v_res_8320_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(
    mut v___y_8321_: *mut LeanObject,
    mut v___y_8322_: *mut LeanObject,
    mut v___y_8323_: *mut LeanObject,
    mut v___y_8324_: *mut LeanObject,
    mut v___y_8325_: *mut LeanObject,
    mut v___y_8326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8328_: *mut LeanObject = core::ptr::null_mut();
    v___x_8328_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_8324_, v___y_8325_, v___y_8326_);
    return v___x_8328_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___boxed(
    mut v___y_8329_: *mut LeanObject,
    mut v___y_8330_: *mut LeanObject,
    mut v___y_8331_: *mut LeanObject,
    mut v___y_8332_: *mut LeanObject,
    mut v___y_8333_: *mut LeanObject,
    mut v___y_8334_: *mut LeanObject,
    mut v___y_8335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8336_: *mut LeanObject = core::ptr::null_mut();
    v_res_8336_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(v___y_8329_, v___y_8330_, v___y_8331_, v___y_8332_, v___y_8333_, v___y_8334_);
    lean_dec(v___y_8334_);
    lean_dec_ref(v___y_8333_);
    lean_dec(v___y_8332_);
    lean_dec_ref(v___y_8331_);
    lean_dec(v___y_8330_);
    lean_dec_ref(v___y_8329_);
    return v_res_8336_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(
    mut v___y_8337_: *mut LeanObject,
    mut v___y_8338_: *mut LeanObject,
    mut v___y_8339_: *mut LeanObject,
    mut v___y_8340_: *mut LeanObject,
    mut v___y_8341_: *mut LeanObject,
    mut v___y_8342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8344_: *mut LeanObject = core::ptr::null_mut();
    v___x_8344_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_8342_);
    return v___x_8344_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___boxed(
    mut v___y_8345_: *mut LeanObject,
    mut v___y_8346_: *mut LeanObject,
    mut v___y_8347_: *mut LeanObject,
    mut v___y_8348_: *mut LeanObject,
    mut v___y_8349_: *mut LeanObject,
    mut v___y_8350_: *mut LeanObject,
    mut v___y_8351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8352_: *mut LeanObject = core::ptr::null_mut();
    v_res_8352_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(v___y_8345_, v___y_8346_, v___y_8347_, v___y_8348_, v___y_8349_, v___y_8350_);
    lean_dec(v___y_8350_);
    lean_dec_ref(v___y_8349_);
    lean_dec(v___y_8348_);
    lean_dec_ref(v___y_8347_);
    lean_dec(v___y_8346_);
    lean_dec_ref(v___y_8345_);
    return v_res_8352_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(
    mut v_00_u03b1_8353_: *mut LeanObject,
    mut v_x_8354_: *mut LeanObject,
    mut v_ctx_x3f_8355_: *mut LeanObject,
    mut v___y_8356_: *mut LeanObject,
    mut v___y_8357_: *mut LeanObject,
    mut v___y_8358_: *mut LeanObject,
    mut v___y_8359_: *mut LeanObject,
    mut v___y_8360_: *mut LeanObject,
    mut v___y_8361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8363_: *mut LeanObject = core::ptr::null_mut();
    v___x_8363_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_8354_, v_ctx_x3f_8355_, v___y_8356_, v___y_8357_, v___y_8358_, v___y_8359_, v___y_8360_, v___y_8361_);
    return v___x_8363_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___boxed(
    mut v_00_u03b1_8364_: *mut LeanObject,
    mut v_x_8365_: *mut LeanObject,
    mut v_ctx_x3f_8366_: *mut LeanObject,
    mut v___y_8367_: *mut LeanObject,
    mut v___y_8368_: *mut LeanObject,
    mut v___y_8369_: *mut LeanObject,
    mut v___y_8370_: *mut LeanObject,
    mut v___y_8371_: *mut LeanObject,
    mut v___y_8372_: *mut LeanObject,
    mut v___y_8373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8374_: *mut LeanObject = core::ptr::null_mut();
    v_res_8374_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(v_00_u03b1_8364_, v_x_8365_, v_ctx_x3f_8366_, v___y_8367_, v___y_8368_, v___y_8369_, v___y_8370_, v___y_8371_, v___y_8372_);
    lean_dec(v___y_8372_);
    lean_dec_ref(v___y_8371_);
    lean_dec(v___y_8370_);
    lean_dec_ref(v___y_8369_);
    lean_dec(v___y_8368_);
    lean_dec_ref(v___y_8367_);
    return v_res_8374_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(
    mut v_eval_8375_: *mut LeanObject,
    mut v_logExceptions_8376_: u8,
    mut v_onErr_8377_: *mut LeanObject,
    mut v_init_8378_: *mut LeanObject,
    mut v_cfg_8379_: *mut LeanObject,
    mut v___y_8380_: *mut LeanObject,
    mut v___y_8381_: *mut LeanObject,
    mut v___y_8382_: *mut LeanObject,
    mut v___y_8383_: *mut LeanObject,
    mut v___y_8384_: *mut LeanObject,
    mut v___y_8385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8387_: *mut LeanObject = core::ptr::null_mut();
    v___x_8387_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_8375_, v_logExceptions_8376_, v_onErr_8377_, v_init_8378_, v_cfg_8379_, v___y_8380_, v___y_8381_, v___y_8382_, v___y_8383_, v___y_8384_, v___y_8385_);
    return v___x_8387_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed(
    mut v_eval_8388_: *mut LeanObject,
    mut v_logExceptions_8389_: *mut LeanObject,
    mut v_onErr_8390_: *mut LeanObject,
    mut v_init_8391_: *mut LeanObject,
    mut v_cfg_8392_: *mut LeanObject,
    mut v___y_8393_: *mut LeanObject,
    mut v___y_8394_: *mut LeanObject,
    mut v___y_8395_: *mut LeanObject,
    mut v___y_8396_: *mut LeanObject,
    mut v___y_8397_: *mut LeanObject,
    mut v___y_8398_: *mut LeanObject,
    mut v___y_8399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_8400_: u8 = 0;
    let mut v_res_8401_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8400_ = (lean_unbox(v_logExceptions_8389_) as u8);
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
    lean_dec(v___y_8398_);
    lean_dec_ref(v___y_8397_);
    lean_dec(v___y_8396_);
    lean_dec_ref(v___y_8395_);
    lean_dec(v___y_8394_);
    lean_dec_ref(v___y_8393_);
    return v_res_8401_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
    mut v_eval_8402_: *mut LeanObject,
    mut v_init_8403_: *mut LeanObject,
    mut v_cfg_8404_: *mut LeanObject,
    mut v_onErr_8405_: *mut LeanObject,
    mut v_logExceptions_8406_: u8,
    mut v_a_8407_: *mut LeanObject,
    mut v_a_8408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8413_: u8 = 0;
    let mut v___x_8414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8417_: u8 = 0;
    let mut v___x_8418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8420_: u8 = 0;
    let mut v___x_8421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8410_ = lean_box((v_logExceptions_8406_) as usize);
                lean_inc_n(v_cfg_8404_, 2);
                lean_inc(v_init_8403_);
                v___f_8411_ = lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___f_8411_, 0, v_eval_8402_);
                lean_closure_set(v___f_8411_, 1, v___x_8410_);
                lean_closure_set(v___f_8411_, 2, v_onErr_8405_);
                lean_closure_set(v___f_8411_, 3, v_init_8403_);
                lean_closure_set(v___f_8411_, 4, v_cfg_8404_);
                v___x_8416_ = lean_unsigned_to_nat(0);
                v___x_8417_ = l_Lean_Syntax_matchesNull(v_cfg_8404_, v___x_8416_);
                if v___x_8417_ == 0 {
                    v___x_8418_ = l_Lean_Syntax_getNumArgs(v_cfg_8404_);
                    v___x_8419_ = lean_unsigned_to_nat(1);
                    v___x_8420_ = lean_nat_dec_eq(v___x_8418_, v___x_8419_);
                    lean_dec(v___x_8418_);
                    if v___x_8420_ == 0 {
                        lean_dec(v_cfg_8404_);
                        v___y_8413_ = v___x_8420_;
                        state = 1;
                        continue;
                    } else {
                        v___x_8421_ = l_Lean_Syntax_getArg(v_cfg_8404_, v___x_8416_);
                        lean_dec(v_cfg_8404_);
                        v___x_8422_ = l_Lean_Syntax_matchesNull(v___x_8421_, v___x_8416_);
                        v___y_8413_ = v___x_8422_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_cfg_8404_);
                    v___y_8413_ = v___x_8417_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_8413_ == 0 {
                    lean_dec(v_init_8403_);
                    v___x_8414_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(
                        v___f_8411_,
                        v_a_8407_,
                        v_a_8408_,
                    );
                    return v___x_8414_;
                } else {
                    lean_dec_ref(v___f_8411_);
                    v___x_8415_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8415_, 0, v_init_8403_);
                    return v___x_8415_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___boxed(
    mut v_eval_8423_: *mut LeanObject,
    mut v_init_8424_: *mut LeanObject,
    mut v_cfg_8425_: *mut LeanObject,
    mut v_onErr_8426_: *mut LeanObject,
    mut v_logExceptions_8427_: *mut LeanObject,
    mut v_a_8428_: *mut LeanObject,
    mut v_a_8429_: *mut LeanObject,
    mut v_a_8430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_8431_: u8 = 0;
    let mut v_res_8432_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8431_ = (lean_unbox(v_logExceptions_8427_) as u8);
    v_res_8432_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
        v_eval_8423_,
        v_init_8424_,
        v_cfg_8425_,
        v_onErr_8426_,
        v_logExceptions_boxed_8431_,
        v_a_8428_,
        v_a_8429_,
    );
    lean_dec(v_a_8429_);
    lean_dec_ref(v_a_8428_);
    return v_res_8432_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(
    mut v_00_u03b1_8433_: *mut LeanObject,
    mut v_eval_8434_: *mut LeanObject,
    mut v_init_8435_: *mut LeanObject,
    mut v_cfg_8436_: *mut LeanObject,
    mut v_onErr_8437_: *mut LeanObject,
    mut v_logExceptions_8438_: u8,
    mut v_a_8439_: *mut LeanObject,
    mut v_a_8440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8442_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_8443_: *mut LeanObject,
    mut v_eval_8444_: *mut LeanObject,
    mut v_init_8445_: *mut LeanObject,
    mut v_cfg_8446_: *mut LeanObject,
    mut v_onErr_8447_: *mut LeanObject,
    mut v_logExceptions_8448_: *mut LeanObject,
    mut v_a_8449_: *mut LeanObject,
    mut v_a_8450_: *mut LeanObject,
    mut v_a_8451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_8452_: u8 = 0;
    let mut v_res_8453_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8452_ = (lean_unbox(v_logExceptions_8448_) as u8);
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
    lean_dec(v_a_8450_);
    lean_dec_ref(v_a_8449_);
    return v_res_8453_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(
    mut v_eval_8454_: *mut LeanObject,
    mut v_logExceptions_8455_: u8,
    mut v_onErr_8456_: *mut LeanObject,
    mut v_init_8457_: *mut LeanObject,
    mut v_cfgs_8458_: *mut LeanObject,
    mut v___y_8459_: *mut LeanObject,
    mut v___y_8460_: *mut LeanObject,
    mut v___y_8461_: *mut LeanObject,
    mut v___y_8462_: *mut LeanObject,
    mut v___y_8463_: *mut LeanObject,
    mut v___y_8464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8466_: *mut LeanObject = core::ptr::null_mut();
    v___x_8466_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_8454_, v_logExceptions_8455_, v_onErr_8456_, v_init_8457_, v_cfgs_8458_, v___y_8459_, v___y_8460_, v___y_8461_, v___y_8462_, v___y_8463_, v___y_8464_);
    return v___x_8466_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed(
    mut v_eval_8467_: *mut LeanObject,
    mut v_logExceptions_8468_: *mut LeanObject,
    mut v_onErr_8469_: *mut LeanObject,
    mut v_init_8470_: *mut LeanObject,
    mut v_cfgs_8471_: *mut LeanObject,
    mut v___y_8472_: *mut LeanObject,
    mut v___y_8473_: *mut LeanObject,
    mut v___y_8474_: *mut LeanObject,
    mut v___y_8475_: *mut LeanObject,
    mut v___y_8476_: *mut LeanObject,
    mut v___y_8477_: *mut LeanObject,
    mut v___y_8478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_8479_: u8 = 0;
    let mut v_res_8480_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8479_ = (lean_unbox(v_logExceptions_8468_) as u8);
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
    lean_dec(v___y_8477_);
    lean_dec_ref(v___y_8476_);
    lean_dec(v___y_8475_);
    lean_dec_ref(v___y_8474_);
    lean_dec(v___y_8473_);
    lean_dec_ref(v___y_8472_);
    lean_dec_ref(v_cfgs_8471_);
    return v_res_8480_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(
    mut v_eval_8481_: *mut LeanObject,
    mut v_init_8482_: *mut LeanObject,
    mut v_cfgs_8483_: *mut LeanObject,
    mut v_onErr_8484_: *mut LeanObject,
    mut v_logExceptions_8485_: u8,
    mut v_a_8486_: *mut LeanObject,
    mut v_a_8487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8491_: u8 = 0;
    v___x_8489_ = lean_array_get_size(v_cfgs_8483_);
    v___x_8490_ = lean_unsigned_to_nat(0);
    v___x_8491_ = lean_nat_dec_eq(v___x_8489_, v___x_8490_);
    if v___x_8491_ == 0 {
        let mut v___x_8492_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_8493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8494_: *mut LeanObject = core::ptr::null_mut();
        v___x_8492_ = lean_box((v_logExceptions_8485_) as usize);
        v___f_8493_ = lean_alloc_closure(
            l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            12,
            5,
        );
        lean_closure_set(v___f_8493_, 0, v_eval_8481_);
        lean_closure_set(v___f_8493_, 1, v___x_8492_);
        lean_closure_set(v___f_8493_, 2, v_onErr_8484_);
        lean_closure_set(v___f_8493_, 3, v_init_8482_);
        lean_closure_set(v___f_8493_, 4, v_cfgs_8483_);
        v___x_8494_ =
            l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_8493_, v_a_8486_, v_a_8487_);
        return v___x_8494_;
    } else {
        let mut v___x_8495_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_onErr_8484_);
        lean_dec_ref(v_cfgs_8483_);
        lean_dec_ref(v_eval_8481_);
        v___x_8495_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_8495_, 0, v_init_8482_);
        return v___x_8495_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___boxed(
    mut v_eval_8496_: *mut LeanObject,
    mut v_init_8497_: *mut LeanObject,
    mut v_cfgs_8498_: *mut LeanObject,
    mut v_onErr_8499_: *mut LeanObject,
    mut v_logExceptions_8500_: *mut LeanObject,
    mut v_a_8501_: *mut LeanObject,
    mut v_a_8502_: *mut LeanObject,
    mut v_a_8503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_8504_: u8 = 0;
    let mut v_res_8505_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8504_ = (lean_unbox(v_logExceptions_8500_) as u8);
    v_res_8505_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(
        v_eval_8496_,
        v_init_8497_,
        v_cfgs_8498_,
        v_onErr_8499_,
        v_logExceptions_boxed_8504_,
        v_a_8501_,
        v_a_8502_,
    );
    lean_dec(v_a_8502_);
    lean_dec_ref(v_a_8501_);
    return v_res_8505_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(
    mut v_00_u03b1_8506_: *mut LeanObject,
    mut v_eval_8507_: *mut LeanObject,
    mut v_init_8508_: *mut LeanObject,
    mut v_cfgs_8509_: *mut LeanObject,
    mut v_onErr_8510_: *mut LeanObject,
    mut v_logExceptions_8511_: u8,
    mut v_a_8512_: *mut LeanObject,
    mut v_a_8513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8515_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_8516_: *mut LeanObject,
    mut v_eval_8517_: *mut LeanObject,
    mut v_init_8518_: *mut LeanObject,
    mut v_cfgs_8519_: *mut LeanObject,
    mut v_onErr_8520_: *mut LeanObject,
    mut v_logExceptions_8521_: *mut LeanObject,
    mut v_a_8522_: *mut LeanObject,
    mut v_a_8523_: *mut LeanObject,
    mut v_a_8524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_8525_: u8 = 0;
    let mut v_res_8526_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8525_ = (lean_unbox(v_logExceptions_8521_) as u8);
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
    lean_dec(v_a_8523_);
    lean_dec_ref(v_a_8522_);
    return v_res_8526_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ConfigEval_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ConfigEval_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ConfigEval_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_SyntheticMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval_Basic(builtin);
}
