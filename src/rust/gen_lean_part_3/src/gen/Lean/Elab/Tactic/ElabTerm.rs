// Lean compiler output
// Module: Lean.Elab.Tactic.ElabTerm
// Imports: Lean.Meta.Tactic.Constructor Lean.Meta.Tactic.Replace Lean.Meta.Tactic.Rename Lean.Elab.Tactic.Basic Lean.Elab.SyntheticMVars
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_array_uset, lean_checked_assign, lean_dbg_trace, lean_expr_eqv,
    lean_infer_type, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_shiftr, lean_nat_sub, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_append, lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt,
    lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::QSort::Basic::l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort;
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Syntax_getArg, l_Lean_Syntax_isIdent, l_Lean_Syntax_isOfKind,
    l_Lean_replaceRef, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Exception_isRuntime,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_quickLt;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::{
    l_Lean_Elab_abortTacticExceptionId, l_Lean_Elab_unsupportedSyntaxExceptionId,
};
use crate::r#gen::Lean::Elab::SyntheticMVars::{
    initialize_Lean_Elab_SyntheticMVars, l_Lean_Elab_Term_PostponeBehavior_ofBool,
    l_Lean_Elab_Term_synthesizeSyntheticMVars,
    l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing,
    runtime_initialize_Lean_Elab_SyntheticMVars,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_SavedState_restore___redArg,
    l_Lean_Elab_Tactic_evalTactic, l_Lean_Elab_Tactic_getMainGoal___redArg,
    l_Lean_Elab_Tactic_getMainTag___redArg, l_Lean_Elab_Tactic_getMainTarget,
    l_Lean_Elab_Tactic_popMainGoal___redArg, l_Lean_Elab_Tactic_pushGoal___redArg,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_saveState___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_tagUntaggedGoals,
    l_Lean_Elab_Tactic_withMainContext___redArg, l_Lean_Elab_Tactic_withoutRecover___boxed,
    l_Lean_Elab_Tactic_withoutRecover___redArg, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTerm___boxed, l_Lean_Elab_Term_isLetRecAuxMVar,
    l_Lean_Elab_Term_logUnassignedUsingErrorInfos, l_Lean_Elab_Term_resolveId_x3f,
    l_Lean_Elab_Term_throwTypeMismatchError___redArg,
    l_Lean_Elab_Term_withoutErrToSorryImp___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_getAppFn, l_Lean_Expr_getLambdaBody, l_Lean_Expr_hasMVar, l_Lean_Expr_headBeta,
    l_Lean_Expr_isMVar, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkMVar,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_isImplementationDetail, l_Lean_LocalDecl_type,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_MVarId_getKind,
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_instMonadMCtxMetaM,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::CollectMVars::{
    l_Lean_Meta_getMVars, l_Lean_Meta_getMVarsNoDelayed, l_Lean_Meta_getMVarsNoDelayed___boxed,
};
use crate::r#gen::Lean::Meta::Tactic::Apply::l_Lean_MVarId_apply;
use crate::r#gen::Lean::Meta::Tactic::Assert::l_Lean_MVarId_assert;
use crate::r#gen::Lean::Meta::Tactic::Constructor::{
    initialize_Lean_Meta_Tactic_Constructor, l_Lean_MVarId_constructor,
    runtime_initialize_Lean_Meta_Tactic_Constructor,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_Meta_intro1Core;
use crate::r#gen::Lean::Meta::Tactic::Rename::{
    initialize_Lean_Meta_Tactic_Rename, l_Lean_MVarId_rename,
    runtime_initialize_Lean_Meta_Tactic_Rename,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    initialize_Lean_Meta_Tactic_Replace, l_Lean_MVarId_replace,
    runtime_initialize_Lean_Meta_Tactic_Replace,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_MVarId_getType, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_getDecl, l_Lean_MetavarKind_isNatural, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::FindMVar::l_Lean_FindMVar_main;
pub static l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 101, 117, 115, 101, 0]};
static mut l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,129656885399133742 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject,8944050731725230368 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4_value: leanh::LeanStringObject<32> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [114, 101, 117, 115, 101, 32, 115, 116, 111, 112, 112, 101, 100, 58, 32, 103, 117, 97, 114, 100, 32, 102, 97, 105, 108, 101, 100, 32, 97, 116, 32, 0]};
static mut l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0_value:
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
static mut l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0_value:
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
        97, 116, 116, 101, 109, 112, 116, 105, 110, 103, 32, 116, 111, 32, 99, 108, 111, 115, 101,
        32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 117, 115, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        10, 116, 104, 105, 115, 32, 105, 115, 32, 111, 102, 116, 101, 110, 32, 100, 117, 101, 32,
        111, 99, 99, 117, 114, 115, 45, 99, 104, 101, 99, 107, 32, 102, 97, 105, 108, 117, 114,
        101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalExact___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_evalExact___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalExact___closed__1_value: leanh::LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_evalExact___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalExact___closed__2_value: leanh::LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_evalExact___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalExact___closed__3_value: leanh::LeanStringObject<6> =
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
static mut l_Lean_Elab_Tactic_evalExact___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalExact___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__3_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalExact___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalExact___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__3_value)
                as *mut leanh::LeanObject,
            12491960235595733941 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalExact___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 69, 120, 97, 99, 116, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0_value) as *mut leanh::LeanObject,16026764361405622880 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 71 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 26 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 78 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 26 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 71 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 30 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 71 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 39 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 30 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 39 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2_value:
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
static mut l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3_value:
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
static mut l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4_value:
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
static mut l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5_value:
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
static mut l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6_value:
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
    m_fun: l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_refineCore___lam__1___closed__0_value:
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
        96, 114, 101, 102, 105, 110, 101, 96, 32, 116, 97, 99, 116, 105, 99, 32, 102, 97, 105, 108,
        101, 100, 44, 32, 118, 97, 108, 117, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_refineCore___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_refineCore___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_refineCore___lam__1___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_refineCore___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_refineCore___lam__1___closed__2_value:
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
        10, 100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 116, 104, 101, 32, 109, 97, 105,
        110, 32, 103, 111, 97, 108, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32,
        96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_refineCore___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_refineCore___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_refineCore___lam__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_refineCore___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_refineCore___lam__1___closed__4_value:
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
static mut l_Lean_Elab_Tactic_refineCore___lam__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_refineCore___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_refineCore___lam__1___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalRefine___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [114, 101, 102, 105, 110, 101, 0],
    };
static mut l_Lean_Elab_Tactic_evalRefine___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRefine___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine___closed__0_value)
                as *mut leanh::LeanObject,
            17704266427038597681 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRefine___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRefine___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine___closed__0_value)
                as *mut leanh::LeanObject,
            16366337681428726512 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRefine___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 82, 101, 102, 105, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0_value) as *mut leanh::LeanObject,15052064682205942140 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 189 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 192 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 189 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 189 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 41 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 41 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRefine_x27___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [114, 101, 102, 105, 110, 101, 39, 0],
    };
static mut l_Lean_Elab_Tactic_evalRefine_x27___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine_x27___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine_x27___closed__0_value)
                as *mut leanh::LeanObject,
            7020564601827897195 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRefine_x27___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRefine_x27___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine_x27___closed__0_value)
                as *mut leanh::LeanObject,
            10703340676459142538 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRefine_x27___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRefine_x27___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 118, 97, 108, 82, 101, 102, 105, 110, 101, 39, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0_value) as *mut leanh::LeanObject,16229251266106510735 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 194 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 28 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 197 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 51 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 28 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 51 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 194 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 32 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 194 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 32 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0_value:
    leanh::LeanStringObject<95> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 95,
    m_capacity: 95,
    m_length: 94,
    m_data: [
        39, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 39, 32, 114, 101, 113, 117, 105, 114,
        101, 115, 32, 97, 32, 116, 101, 114, 109, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111,
        114, 109, 32, 96, 104, 32, 120, 95, 49, 32, 46, 46, 32, 120, 95, 110, 96, 32, 119, 104,
        101, 114, 101, 32, 96, 104, 96, 32, 97, 112, 112, 101, 97, 114, 115, 32, 105, 110, 32, 116,
        104, 101, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 0,
    ],
};
static mut l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalSpecialize___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0],
    };
static mut l_Lean_Elab_Tactic_evalSpecialize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSpecialize___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalSpecialize___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSpecialize___closed__0_value)
                as *mut leanh::LeanObject,
            204052483309453488 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSpecialize___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSpecialize___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 83, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0_value) as *mut leanh::LeanObject,1168765435100602392 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 199 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 212 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 199 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 35 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 199 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 49 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 35 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 49 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_elabTermForApply___closed__0_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 101, 114, 109, 0],
};
static mut l_Lean_Elab_Tactic_elabTermForApply___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabTermForApply___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0_value: leanh::LeanStringObject<
    18,
> = leanh::LeanStringObject {
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
        85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 101, 114, 109, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2_value: leanh::LeanStringObject<
    41,
> = leanh::LeanStringObject {
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
        96, 59, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 105, 110, 103, 108, 101, 32,
        114, 101, 102, 101, 114, 101, 110, 99, 101, 32, 116, 111, 32, 118, 97, 114, 105, 97, 98,
        108, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_getFVarIds___boxed__const__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + core::mem::size_of::<usize>() * 1) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(0 as *mut leanh::LeanObject)],
    };
pub static mut l_Lean_Elab_Tactic_getFVarIds___boxed__const__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_getFVarIds___boxed__const__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalApply___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [97, 112, 112, 108, 121, 0],
    };
static mut l_Lean_Elab_Tactic_evalApply___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalApply___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalApply___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalApply___closed__0_value)
                as *mut leanh::LeanObject,
            5826123769708379594 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalApply___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalApply___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 65, 112, 112, 108, 121, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0_value) as *mut leanh::LeanObject,5015957794065723106 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 303 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 306 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 303 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 303 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 56 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 56 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [16777472 as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalConstructor___redArg___closed__0_value:
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
    m_fun: l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_evalConstructor___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalConstructor___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0_value) as *mut leanh::LeanObject,980513800819686544 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 118, 97, 108, 67, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2_value) as *mut leanh::LeanObject,3806818481427354651 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 308 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 49 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 312 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 28 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 49 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 28 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 308 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 53 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 308 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 68 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 53 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 68 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_evalWithReducible___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalWithReducible___closed__0: u64 = 0;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0_value) as *mut leanh::LeanObject,6022092293134036165 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 118, 97, 108, 87, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2_value) as *mut leanh::LeanObject,7223893781142825268 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 314 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 51 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 315 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 36 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 51 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 36 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 314 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 55 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 314 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 72 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 55 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 72 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0: u64 = 0;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 65, 110, 100, 73, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0_value) as *mut leanh::LeanObject,3591675660578776960 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [101, 118, 97, 108, 87, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 65, 110, 100, 73, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2_value) as *mut leanh::LeanObject,8287192952810348866 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 317 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 318 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 317 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 67 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 317 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 96 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 67 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 96 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0: u64 = 0;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [119, 105, 116, 104, 85, 110, 102, 111, 108, 100, 105, 110, 103, 65, 108, 108, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0_value) as *mut leanh::LeanObject,9743594099429324326 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 118, 97, 108, 87, 105, 116, 104, 85, 110, 102, 111, 108, 100, 105, 110, 103, 65, 108, 108, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2_value) as *mut leanh::LeanObject,10833443650386498893 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 320 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 321 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 60 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 60 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 320 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 58 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 320 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 78 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 58 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 78 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0: u64 = 0;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [119, 105, 116, 104, 85, 110, 102, 111, 108, 100, 105, 110, 103, 78, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__0_value) as *mut leanh::LeanObject,6262213567091255464 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__2_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [101, 118, 97, 108, 87, 105, 116, 104, 85, 110, 102, 111, 108, 100, 105, 110, 103, 78, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__2_value) as *mut leanh::LeanObject,11457910782924207267 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0_value:
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
    m_data: [104, 0],
};
static mut l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        8738205681931236784 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRename___lam__0___closed__0_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 97, 32, 104, 121,
        112, 111, 116, 104, 101, 115, 105, 115, 32, 119, 105, 116, 104, 32, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_evalRename___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRename___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_evalRename___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalRename___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalRename___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [114, 101, 110, 97, 109, 101, 0],
    };
static mut l_Lean_Elab_Tactic_evalRename___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRename___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRename___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRename___closed__0_value)
                as *mut leanh::LeanObject,
            4936154207136772743 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRename___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRename___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRename___closed__2_value: leanh::LeanStringObject<6> =
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
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_Tactic_evalRename___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRename___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRename___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRename___closed__2_value)
                as *mut leanh::LeanObject,
            5117844058249666356 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRename___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRename___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 82, 101, 110, 97, 109, 101, 0]};
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalExact___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0_value) as *mut leanh::LeanObject,11782876247512346793 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 344 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 44 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 359 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 44 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 344 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 344 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 58 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 58 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(
    mut v_k_4657_: *mut leanh::LeanObject,
    mut v_mayPostpone_4658_: u8,
    mut v_a_4659_: *mut leanh::LeanObject,
    mut v_a_4660_: *mut leanh::LeanObject,
    mut v_a_4661_: *mut leanh::LeanObject,
    mut v_a_4662_: *mut leanh::LeanObject,
    mut v_a_4663_: *mut leanh::LeanObject,
    mut v_a_4664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: u8 = 0;
    let mut v___x_4669_: u8 = 0;
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4673_: u8 = 0;
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4677_: u8 = 0;
    let mut v_unused_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4682_: u8 = 0;
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_4664_);
                leanh::lean_inc_ref(v_a_4663_);
                leanh::lean_inc(v_a_4662_);
                leanh::lean_inc_ref(v_a_4661_);
                leanh::lean_inc(v_a_4660_);
                leanh::lean_inc_ref(v_a_4659_);
                v___x_4666_ = leanh::lean_apply_7(
                    v_k_4657_,
                    v_a_4659_,
                    v_a_4660_,
                    v_a_4661_,
                    v_a_4662_,
                    v_a_4663_,
                    v_a_4664_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4666_) == 0 {
                    v_a_4667_ = leanh::lean_ctor_get(v___x_4666_, 0);
                    leanh::lean_inc(v_a_4667_);
                    leanh::lean_dec_ref_known(v___x_4666_, 1);
                    v___x_4668_ = l_Lean_Elab_Term_PostponeBehavior_ofBool(v_mayPostpone_4658_);
                    v___x_4669_ = 0;
                    v___x_4670_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(
                        v___x_4668_,
                        v___x_4669_,
                        v_a_4659_,
                        v_a_4660_,
                        v_a_4661_,
                        v_a_4662_,
                        v_a_4663_,
                        v_a_4664_,
                    );
                    if leanh::lean_obj_tag(v___x_4670_) == 0 {
                        v_isSharedCheck_4677_ =
                            (!leanh::lean_is_exclusive(v___x_4670_)) as u8;
                        if v_isSharedCheck_4677_ == 0 {
                            v_unused_4678_ = leanh::lean_ctor_get(v___x_4670_, 0);
                            leanh::lean_dec(v_unused_4678_);
                            v___x_4672_ = v___x_4670_;
                            v_isShared_4673_ = v_isSharedCheck_4677_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4670_);
                            v___x_4672_ = leanh::lean_box(0);
                            v_isShared_4673_ = v_isSharedCheck_4677_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4667_);
                        v_a_4679_ = leanh::lean_ctor_get(v___x_4670_, 0);
                        v_isSharedCheck_4686_ =
                            (!leanh::lean_is_exclusive(v___x_4670_)) as u8;
                        if v_isSharedCheck_4686_ == 0 {
                            v___x_4681_ = v___x_4670_;
                            v_isShared_4682_ = v_isSharedCheck_4686_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4679_);
                            leanh::lean_dec(v___x_4670_);
                            v___x_4681_ = leanh::lean_box(0);
                            v_isShared_4682_ = v_isSharedCheck_4686_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    return v___x_4666_;
                }
            }
            1 => {
                if v_isShared_4673_ == 0 {
                    leanh::lean_ctor_set(v___x_4672_, 0, v_a_4667_);
                    v___x_4675_ = v___x_4672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4676_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4667_);
                    v___x_4675_ = v_reuseFailAlloc_4676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4675_;
            }
            3 => {
                if v_isShared_4682_ == 0 {
                    v___x_4684_ = v___x_4681_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
                    v___x_4684_ = v_reuseFailAlloc_4685_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg___boxed(
    mut v_k_4687_: *mut leanh::LeanObject,
    mut v_mayPostpone_4688_: *mut leanh::LeanObject,
    mut v_a_4689_: *mut leanh::LeanObject,
    mut v_a_4690_: *mut leanh::LeanObject,
    mut v_a_4691_: *mut leanh::LeanObject,
    mut v_a_4692_: *mut leanh::LeanObject,
    mut v_a_4693_: *mut leanh::LeanObject,
    mut v_a_4694_: *mut leanh::LeanObject,
    mut v_a_4695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mayPostpone_boxed_4696_: u8 = 0;
    let mut v_res_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_4696_ = (leanh::lean_unbox(v_mayPostpone_4688_) as u8);
    v_res_4697_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(
        v_k_4687_,
        v_mayPostpone_boxed_4696_,
        v_a_4689_,
        v_a_4690_,
        v_a_4691_,
        v_a_4692_,
        v_a_4693_,
        v_a_4694_,
    );
    leanh::lean_dec(v_a_4694_);
    leanh::lean_dec_ref(v_a_4693_);
    leanh::lean_dec(v_a_4692_);
    leanh::lean_dec_ref(v_a_4691_);
    leanh::lean_dec(v_a_4690_);
    leanh::lean_dec_ref(v_a_4689_);
    return v_res_4697_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go(
    mut v_00_u03b1_4698_: *mut leanh::LeanObject,
    mut v_k_4699_: *mut leanh::LeanObject,
    mut v_mayPostpone_4700_: u8,
    mut v_a_4701_: *mut leanh::LeanObject,
    mut v_a_4702_: *mut leanh::LeanObject,
    mut v_a_4703_: *mut leanh::LeanObject,
    mut v_a_4704_: *mut leanh::LeanObject,
    mut v_a_4705_: *mut leanh::LeanObject,
    mut v_a_4706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4708_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(
        v_k_4699_,
        v_mayPostpone_4700_,
        v_a_4701_,
        v_a_4702_,
        v_a_4703_,
        v_a_4704_,
        v_a_4705_,
        v_a_4706_,
    );
    return v___x_4708_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___boxed(
    mut v_00_u03b1_4709_: *mut leanh::LeanObject,
    mut v_k_4710_: *mut leanh::LeanObject,
    mut v_mayPostpone_4711_: *mut leanh::LeanObject,
    mut v_a_4712_: *mut leanh::LeanObject,
    mut v_a_4713_: *mut leanh::LeanObject,
    mut v_a_4714_: *mut leanh::LeanObject,
    mut v_a_4715_: *mut leanh::LeanObject,
    mut v_a_4716_: *mut leanh::LeanObject,
    mut v_a_4717_: *mut leanh::LeanObject,
    mut v_a_4718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mayPostpone_boxed_4719_: u8 = 0;
    let mut v_res_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_4719_ = (leanh::lean_unbox(v_mayPostpone_4711_) as u8);
    v_res_4720_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go(
        v_00_u03b1_4709_,
        v_k_4710_,
        v_mayPostpone_boxed_4719_,
        v_a_4712_,
        v_a_4713_,
        v_a_4714_,
        v_a_4715_,
        v_a_4716_,
        v_a_4717_,
    );
    leanh::lean_dec(v_a_4717_);
    leanh::lean_dec_ref(v_a_4716_);
    leanh::lean_dec(v_a_4715_);
    leanh::lean_dec_ref(v_a_4714_);
    leanh::lean_dec(v_a_4713_);
    leanh::lean_dec_ref(v_a_4712_);
    return v_res_4720_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(
    mut v_a_4721_: *mut leanh::LeanObject,
    mut v___y_4722_: *mut leanh::LeanObject,
    mut v___y_4723_: *mut leanh::LeanObject,
    mut v___y_4724_: *mut leanh::LeanObject,
    mut v___y_4725_: *mut leanh::LeanObject,
    mut v___y_4726_: *mut leanh::LeanObject,
    mut v___y_4727_: *mut leanh::LeanObject,
    mut v___y_4728_: *mut leanh::LeanObject,
    mut v___y_4729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4723_);
    leanh::lean_inc_ref(v___y_4722_);
    v___x_4731_ = leanh::lean_apply_2(v_a_4721_, v___y_4722_, v___y_4723_);
    v___x_4732_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v___x_4731_,
        v___y_4724_,
        v___y_4725_,
        v___y_4726_,
        v___y_4727_,
        v___y_4728_,
        v___y_4729_,
    );
    return v___x_4732_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg___boxed(
    mut v_a_4733_: *mut leanh::LeanObject,
    mut v___y_4734_: *mut leanh::LeanObject,
    mut v___y_4735_: *mut leanh::LeanObject,
    mut v___y_4736_: *mut leanh::LeanObject,
    mut v___y_4737_: *mut leanh::LeanObject,
    mut v___y_4738_: *mut leanh::LeanObject,
    mut v___y_4739_: *mut leanh::LeanObject,
    mut v___y_4740_: *mut leanh::LeanObject,
    mut v___y_4741_: *mut leanh::LeanObject,
    mut v___y_4742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4743_ =
        l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(
            v_a_4733_,
            v___y_4734_,
            v___y_4735_,
            v___y_4736_,
            v___y_4737_,
            v___y_4738_,
            v___y_4739_,
            v___y_4740_,
            v___y_4741_,
        );
    leanh::lean_dec(v___y_4741_);
    leanh::lean_dec_ref(v___y_4740_);
    leanh::lean_dec(v___y_4739_);
    leanh::lean_dec_ref(v___y_4738_);
    leanh::lean_dec(v___y_4737_);
    leanh::lean_dec_ref(v___y_4736_);
    leanh::lean_dec(v___y_4735_);
    leanh::lean_dec_ref(v___y_4734_);
    return v_res_4743_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0(
    mut v_00_u03b1_4744_: *mut leanh::LeanObject,
    mut v_a_4745_: *mut leanh::LeanObject,
    mut v___y_4746_: *mut leanh::LeanObject,
    mut v___y_4747_: *mut leanh::LeanObject,
    mut v___y_4748_: *mut leanh::LeanObject,
    mut v___y_4749_: *mut leanh::LeanObject,
    mut v___y_4750_: *mut leanh::LeanObject,
    mut v___y_4751_: *mut leanh::LeanObject,
    mut v___y_4752_: *mut leanh::LeanObject,
    mut v___y_4753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4755_ =
        l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(
            v_a_4745_,
            v___y_4746_,
            v___y_4747_,
            v___y_4748_,
            v___y_4749_,
            v___y_4750_,
            v___y_4751_,
            v___y_4752_,
            v___y_4753_,
        );
    return v___x_4755_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___boxed(
    mut v_00_u03b1_4756_: *mut leanh::LeanObject,
    mut v_a_4757_: *mut leanh::LeanObject,
    mut v___y_4758_: *mut leanh::LeanObject,
    mut v___y_4759_: *mut leanh::LeanObject,
    mut v___y_4760_: *mut leanh::LeanObject,
    mut v___y_4761_: *mut leanh::LeanObject,
    mut v___y_4762_: *mut leanh::LeanObject,
    mut v___y_4763_: *mut leanh::LeanObject,
    mut v___y_4764_: *mut leanh::LeanObject,
    mut v___y_4765_: *mut leanh::LeanObject,
    mut v___y_4766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4767_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0(
        v_00_u03b1_4756_,
        v_a_4757_,
        v___y_4758_,
        v___y_4759_,
        v___y_4760_,
        v___y_4761_,
        v___y_4762_,
        v___y_4763_,
        v___y_4764_,
        v___y_4765_,
    );
    leanh::lean_dec(v___y_4765_);
    leanh::lean_dec_ref(v___y_4764_);
    leanh::lean_dec(v___y_4763_);
    leanh::lean_dec_ref(v___y_4762_);
    leanh::lean_dec(v___y_4761_);
    leanh::lean_dec_ref(v___y_4760_);
    leanh::lean_dec(v___y_4759_);
    leanh::lean_dec_ref(v___y_4758_);
    return v_res_4767_;
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(
    mut v_cond_4768_: u8,
    mut v_____r_4769_: *mut leanh::LeanObject,
) -> u8 {
    if v_cond_4768_ == 0 {
        let mut v___x_4770_: u8 = 0;
        v___x_4770_ = 1;
        return v___x_4770_;
    } else {
        let mut v___x_4771_: u8 = 0;
        v___x_4771_ = 0;
        return v___x_4771_;
    }
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0___boxed(
    mut v_cond_4772_: *mut leanh::LeanObject,
    mut v_____r_4773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cond_boxed_4774_: u8 = 0;
    let mut v_res_4775_: u8 = 0;
    let mut v_r_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cond_boxed_4774_ = (leanh::lean_unbox(v_cond_4772_) as u8);
    v_res_4775_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_boxed_4774_, v_____r_4773_);
    v_r_4776_ = leanh::lean_box((v_res_4775_) as usize);
    return v_r_4776_;
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1(
    mut v___f_4777_: *mut leanh::LeanObject,
    mut v_x_4778_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: u8 = 0;
    v___x_4779_ = leanh::lean_box(0);
    v___x_4780_ = leanh::lean_apply_1(v___f_4777_, v___x_4779_);
    v___x_4781_ = (leanh::lean_unbox(v___x_4780_) as u8);
    return v___x_4781_;
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1___boxed(
    mut v___f_4782_: *mut leanh::LeanObject,
    mut v_x_4783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4784_: u8 = 0;
    let mut v_r_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4784_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1(v___f_4782_, v_x_4783_);
    v_r_4785_ = leanh::lean_box((v_res_4784_) as usize);
    return v_r_4785_;
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(
    mut v_cond_4794_: u8,
    mut v_act_4795_: *mut leanh::LeanObject,
    mut v___y_4796_: *mut leanh::LeanObject,
    mut v___y_4797_: *mut leanh::LeanObject,
    mut v___y_4798_: *mut leanh::LeanObject,
    mut v___y_4799_: *mut leanh::LeanObject,
    mut v___y_4800_: *mut leanh::LeanObject,
    mut v___y_4801_: *mut leanh::LeanObject,
    mut v___y_4802_: *mut leanh::LeanObject,
    mut v___y_4803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_x3f_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mayPostpone_4808_: u8 = 0;
    let mut v_errToSorry_4809_: u8 = 0;
    let mut v_autoBoundImplicitContext_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicitForbidden_4811_: *mut leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_sectionVars_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sectionFVars_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_implicitLambda_4814_: u8 = 0;
    let mut v_heedElabAsElim_4815_: u8 = 0;
    let mut v_isNoncomputableSection_4816_: u8 = 0;
    let mut v_isMetaSection_4817_: u8 = 0;
    let mut v_ignoreTCFailures_4818_: u8 = 0;
    let mut v_inPattern_4819_: u8 = 0;
    let mut v_tacSnap_x3f_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveRecAppSyntax_4821_: u8 = 0;
    let mut v_holesAsSyntheticOpaque_4822_: u8 = 0;
    let mut v_checkDeprecated_4823_: u8 = 0;
    let mut v_fixedTermElabs_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4830_: u8 = 0;
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_x3f_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: u8 = 0;
    let mut v_val_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4844_: u8 = 0;
    let mut v_stx_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: u8 = 0;
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: u8 = 0;
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4805_ = leanh::lean_ctor_get(v___y_4802_, 2);
                v_declName_x3f_4806_ = leanh::lean_ctor_get(v___y_4798_, 0);
                v_macroStack_4807_ = leanh::lean_ctor_get(v___y_4798_, 1);
                v_mayPostpone_4808_ = leanh::lean_ctor_get_uint8(
                    v___y_4798_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                v_errToSorry_4809_ = leanh::lean_ctor_get_uint8(
                    v___y_4798_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 1) as u32,
                );
                v_autoBoundImplicitContext_4810_ = leanh::lean_ctor_get(v___y_4798_, 2);
                v_autoBoundImplicitForbidden_4811_ = leanh::lean_ctor_get(v___y_4798_, 3);
                v_sectionVars_4812_ = leanh::lean_ctor_get(v___y_4798_, 4);
                v_sectionFVars_4813_ = leanh::lean_ctor_get(v___y_4798_, 5);
                v_implicitLambda_4814_ = leanh::lean_ctor_get_uint8(
                    v___y_4798_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                );
                v_heedElabAsElim_4815_ = leanh::lean_ctor_get_uint8(
                    v___y_4798_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 3) as u32,
                );
                v_isNoncomputableSection_4816_ = leanh::lean_ctor_get_uint8(
                    v___y_4798_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 4) as u32,
                );
                v_isMetaSection_4817_ = leanh::lean_ctor_get_uint8(
                    v___y_4798_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 5) as u32,
                );
                v_ignoreTCFailures_4818_ = leanh::lean_ctor_get_uint8(
                    v___y_4798_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 6) as u32,
                );
                v_inPattern_4819_ = leanh::lean_ctor_get_uint8(
                    v___y_4798_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 7) as u32,
                );
                v_tacSnap_x3f_4820_ = leanh::lean_ctor_get(v___y_4798_, 6);
                v_saveRecAppSyntax_4821_ = leanh::lean_ctor_get_uint8(
                    v___y_4798_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 8) as u32,
                );
                v_holesAsSyntheticOpaque_4822_ = leanh::lean_ctor_get_uint8(
                    v___y_4798_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 9) as u32,
                );
                v_checkDeprecated_4823_ = leanh::lean_ctor_get_uint8(
                    v___y_4798_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 10) as u32,
                );
                v_fixedTermElabs_4824_ = leanh::lean_ctor_get(v___y_4798_, 7);
                if leanh::lean_obj_tag(v_tacSnap_x3f_4820_) == 0 {
                    v___y_4826_ = v_tacSnap_x3f_4820_;
                    state = 1;
                    continue;
                } else {
                    v_val_4832_ = leanh::lean_ctor_get(v_tacSnap_x3f_4820_, 0);
                    v_old_x3f_4833_ = leanh::lean_ctor_get(v_val_4832_, 0);
                    v___x_4834_ = leanh::lean_box((v_cond_4794_) as usize);
                    v___f_4835_ = leanh::lean_alloc_closure(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    leanh::lean_closure_set(v___f_4835_, 0, v___x_4834_);
                    if leanh::lean_obj_tag(v_old_x3f_4833_) == 1 {
                        if v_cond_4794_ == 0 {
                            leanh::lean_dec_ref(v___f_4835_);
                            state = 3;
                            continue;
                        } else {
                            v_val_4839_ = leanh::lean_ctor_get(v_old_x3f_4833_, 0);
                            v_map_4840_ = leanh::lean_ctor_get(v_options_4805_, 0);
                            v___x_4841_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3;
                            v___x_4842_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4840_, v___x_4841_);
                            if leanh::lean_obj_tag(v___x_4842_) == 0 {
                                leanh::lean_dec_ref(v___f_4835_);
                                state = 3;
                                continue;
                            } else {
                                v_val_4843_ = leanh::lean_ctor_get(v___x_4842_, 0);
                                leanh::lean_inc(v_val_4843_);
                                leanh::lean_dec_ref_known(v___x_4842_, 1);
                                if leanh::lean_obj_tag(v_val_4843_) == 1 {
                                    v_v_4844_ =
                                        leanh::lean_ctor_get_uint8(v_val_4843_, 0 as u32);
                                    leanh::lean_dec_ref_known(v_val_4843_, 0);
                                    if v_v_4844_ == 0 {
                                        leanh::lean_dec_ref(v___f_4835_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v_stx_4845_ = leanh::lean_ctor_get(v_val_4839_, 0);
                                        v___f_4846_ = leanh::lean_alloc_closure(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                                        leanh::lean_closure_set(v___f_4846_, 0, v___f_4835_);
                                        v___x_4847_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4;
                                        v___x_4848_ = leanh::lean_box(0);
                                        v___x_4849_ = 0;
                                        leanh::lean_inc(v_stx_4845_);
                                        v___x_4850_ = l_Lean_Syntax_formatStx(
                                            v_stx_4845_,
                                            v___x_4848_,
                                            v___x_4849_,
                                        );
                                        v___x_4851_ = l_Std_Format_defWidth;
                                        v___x_4852_ = leanh::lean_unsigned_to_nat(0);
                                        v___x_4853_ = l_Std_Format_pretty(
                                            v___x_4850_,
                                            v___x_4851_,
                                            v___x_4852_,
                                            v___x_4852_,
                                        );
                                        v___x_4854_ = lean_string_append(v___x_4847_, v___x_4853_);
                                        leanh::lean_dec_ref(v___x_4853_);
                                        v___x_4855_ = lean_dbg_trace(v___x_4854_, v___f_4846_);
                                        v___x_4856_ = (leanh::lean_unbox(v___x_4855_) as u8);
                                        leanh::lean_dec(v___x_4855_);
                                        v___y_4830_ = v___x_4856_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_val_4843_);
                                    leanh::lean_dec_ref(v___f_4835_);
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___f_4835_);
                        v___x_4857_ = leanh::lean_box(0);
                        v___x_4858_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_4794_, v___x_4857_);
                        v___y_4830_ = v___x_4858_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_fixedTermElabs_4824_);
                leanh::lean_inc(v_sectionFVars_4813_);
                leanh::lean_inc(v_sectionVars_4812_);
                leanh::lean_inc_ref(v_autoBoundImplicitForbidden_4811_);
                leanh::lean_inc(v_autoBoundImplicitContext_4810_);
                leanh::lean_inc(v_macroStack_4807_);
                leanh::lean_inc(v_declName_x3f_4806_);
                v___x_4827_ = leanh::lean_alloc_ctor(0, 8, (11) as u32);
                leanh::lean_ctor_set(v___x_4827_, 0, v_declName_x3f_4806_);
                leanh::lean_ctor_set(v___x_4827_, 1, v_macroStack_4807_);
                leanh::lean_ctor_set(v___x_4827_, 2, v_autoBoundImplicitContext_4810_);
                leanh::lean_ctor_set(v___x_4827_, 3, v_autoBoundImplicitForbidden_4811_);
                leanh::lean_ctor_set(v___x_4827_, 4, v_sectionVars_4812_);
                leanh::lean_ctor_set(v___x_4827_, 5, v_sectionFVars_4813_);
                leanh::lean_ctor_set(v___x_4827_, 6, v___y_4826_);
                leanh::lean_ctor_set(v___x_4827_, 7, v_fixedTermElabs_4824_);
                leanh::lean_ctor_set_uint8(
                    v___x_4827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    v_mayPostpone_4808_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 1) as u32,
                    v_errToSorry_4809_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                    v_implicitLambda_4814_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 3) as u32,
                    v_heedElabAsElim_4815_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 4) as u32,
                    v_isNoncomputableSection_4816_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 5) as u32,
                    v_isMetaSection_4817_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 6) as u32,
                    v_ignoreTCFailures_4818_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 7) as u32,
                    v_inPattern_4819_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 8) as u32,
                    v_saveRecAppSyntax_4821_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 9) as u32,
                    v_holesAsSyntheticOpaque_4822_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 10) as u32,
                    v_checkDeprecated_4823_,
                );
                leanh::lean_inc(v___y_4803_);
                leanh::lean_inc_ref(v___y_4802_);
                leanh::lean_inc(v___y_4801_);
                leanh::lean_inc_ref(v___y_4800_);
                leanh::lean_inc(v___y_4799_);
                leanh::lean_inc(v___y_4797_);
                leanh::lean_inc_ref(v___y_4796_);
                v___x_4828_ = leanh::lean_apply_9(
                    v_act_4795_,
                    v___y_4796_,
                    v___y_4797_,
                    v___x_4827_,
                    v___y_4799_,
                    v___y_4800_,
                    v___y_4801_,
                    v___y_4802_,
                    v___y_4803_,
                    leanh::lean_box(0),
                );
                return v___x_4828_;
            }
            2 => {
                if v___y_4830_ == 0 {
                    v___x_4831_ = leanh::lean_box(0);
                    v___y_4826_ = v___x_4831_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tacSnap_x3f_4820_);
                    v___y_4826_ = v_tacSnap_x3f_4820_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4837_ = leanh::lean_box(0);
                v___x_4838_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_4794_, v___x_4837_);
                v___y_4830_ = v___x_4838_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___boxed(
    mut v_cond_4859_: *mut leanh::LeanObject,
    mut v_act_4860_: *mut leanh::LeanObject,
    mut v___y_4861_: *mut leanh::LeanObject,
    mut v___y_4862_: *mut leanh::LeanObject,
    mut v___y_4863_: *mut leanh::LeanObject,
    mut v___y_4864_: *mut leanh::LeanObject,
    mut v___y_4865_: *mut leanh::LeanObject,
    mut v___y_4866_: *mut leanh::LeanObject,
    mut v___y_4867_: *mut leanh::LeanObject,
    mut v___y_4868_: *mut leanh::LeanObject,
    mut v___y_4869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cond_boxed_4870_: u8 = 0;
    let mut v_res_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cond_boxed_4870_ = (leanh::lean_unbox(v_cond_4859_) as u8);
    v_res_4871_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v_cond_boxed_4870_, v_act_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_);
    leanh::lean_dec(v___y_4868_);
    leanh::lean_dec_ref(v___y_4867_);
    leanh::lean_dec(v___y_4866_);
    leanh::lean_dec_ref(v___y_4865_);
    leanh::lean_dec(v___y_4864_);
    leanh::lean_dec_ref(v___y_4863_);
    leanh::lean_dec(v___y_4862_);
    leanh::lean_dec_ref(v___y_4861_);
    return v_res_4871_;
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1(
    mut v_00_u03b1_4872_: *mut leanh::LeanObject,
    mut v_cond_4873_: u8,
    mut v_act_4874_: *mut leanh::LeanObject,
    mut v___y_4875_: *mut leanh::LeanObject,
    mut v___y_4876_: *mut leanh::LeanObject,
    mut v___y_4877_: *mut leanh::LeanObject,
    mut v___y_4878_: *mut leanh::LeanObject,
    mut v___y_4879_: *mut leanh::LeanObject,
    mut v___y_4880_: *mut leanh::LeanObject,
    mut v___y_4881_: *mut leanh::LeanObject,
    mut v___y_4882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4884_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v_cond_4873_, v_act_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
    return v___x_4884_;
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___boxed(
    mut v_00_u03b1_4885_: *mut leanh::LeanObject,
    mut v_cond_4886_: *mut leanh::LeanObject,
    mut v_act_4887_: *mut leanh::LeanObject,
    mut v___y_4888_: *mut leanh::LeanObject,
    mut v___y_4889_: *mut leanh::LeanObject,
    mut v___y_4890_: *mut leanh::LeanObject,
    mut v___y_4891_: *mut leanh::LeanObject,
    mut v___y_4892_: *mut leanh::LeanObject,
    mut v___y_4893_: *mut leanh::LeanObject,
    mut v___y_4894_: *mut leanh::LeanObject,
    mut v___y_4895_: *mut leanh::LeanObject,
    mut v___y_4896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cond_boxed_4897_: u8 = 0;
    let mut v_res_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cond_boxed_4897_ = (leanh::lean_unbox(v_cond_4886_) as u8);
    v_res_4898_ =
        l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1(
            v_00_u03b1_4885_,
            v_cond_boxed_4897_,
            v_act_4887_,
            v___y_4888_,
            v___y_4889_,
            v___y_4890_,
            v___y_4891_,
            v___y_4892_,
            v___y_4893_,
            v___y_4894_,
            v___y_4895_,
        );
    leanh::lean_dec(v___y_4895_);
    leanh::lean_dec_ref(v___y_4894_);
    leanh::lean_dec(v___y_4893_);
    leanh::lean_dec_ref(v___y_4892_);
    leanh::lean_dec(v___y_4891_);
    leanh::lean_dec_ref(v___y_4890_);
    leanh::lean_dec(v___y_4889_);
    leanh::lean_dec_ref(v___y_4888_);
    return v_res_4898_;
}
pub unsafe fn l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(
    mut v_k_4899_: *mut leanh::LeanObject,
    mut v_mayPostpone_4900_: u8,
    mut v___y_4901_: *mut leanh::LeanObject,
    mut v___y_4902_: *mut leanh::LeanObject,
    mut v___y_4903_: *mut leanh::LeanObject,
    mut v___y_4904_: *mut leanh::LeanObject,
    mut v___y_4905_: *mut leanh::LeanObject,
    mut v___y_4906_: *mut leanh::LeanObject,
    mut v___y_4907_: *mut leanh::LeanObject,
    mut v___y_4908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4910_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(
        v_k_4899_,
        v_mayPostpone_4900_,
        v___y_4903_,
        v___y_4904_,
        v___y_4905_,
        v___y_4906_,
        v___y_4907_,
        v___y_4908_,
    );
    return v___x_4910_;
}
pub unsafe fn l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed(
    mut v_k_4911_: *mut leanh::LeanObject,
    mut v_mayPostpone_4912_: *mut leanh::LeanObject,
    mut v___y_4913_: *mut leanh::LeanObject,
    mut v___y_4914_: *mut leanh::LeanObject,
    mut v___y_4915_: *mut leanh::LeanObject,
    mut v___y_4916_: *mut leanh::LeanObject,
    mut v___y_4917_: *mut leanh::LeanObject,
    mut v___y_4918_: *mut leanh::LeanObject,
    mut v___y_4919_: *mut leanh::LeanObject,
    mut v___y_4920_: *mut leanh::LeanObject,
    mut v___y_4921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mayPostpone_boxed_4922_: u8 = 0;
    let mut v_res_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_4922_ = (leanh::lean_unbox(v_mayPostpone_4912_) as u8);
    v_res_4923_ = l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(
        v_k_4911_,
        v_mayPostpone_boxed_4922_,
        v___y_4913_,
        v___y_4914_,
        v___y_4915_,
        v___y_4916_,
        v___y_4917_,
        v___y_4918_,
        v___y_4919_,
        v___y_4920_,
    );
    leanh::lean_dec(v___y_4920_);
    leanh::lean_dec_ref(v___y_4919_);
    leanh::lean_dec(v___y_4918_);
    leanh::lean_dec_ref(v___y_4917_);
    leanh::lean_dec(v___y_4916_);
    leanh::lean_dec_ref(v___y_4915_);
    leanh::lean_dec(v___y_4914_);
    leanh::lean_dec_ref(v___y_4913_);
    return v_res_4923_;
}
pub unsafe fn l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(
    mut v___f_4924_: *mut leanh::LeanObject,
    mut v_k_4925_: *mut leanh::LeanObject,
    mut v_mayPostpone_4926_: u8,
    mut v___y_4927_: *mut leanh::LeanObject,
    mut v___y_4928_: *mut leanh::LeanObject,
    mut v___y_4929_: *mut leanh::LeanObject,
    mut v___y_4930_: *mut leanh::LeanObject,
    mut v___y_4931_: *mut leanh::LeanObject,
    mut v___y_4932_: *mut leanh::LeanObject,
    mut v___y_4933_: *mut leanh::LeanObject,
    mut v___y_4934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_recover_4936_: u8 = 0;
    v_recover_4936_ = leanh::lean_ctor_get_uint8(
        v___y_4927_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    if v_recover_4936_ == 0 {
        let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4925_);
        v___x_4937_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(v___f_4924_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
        return v___x_4937_;
    } else {
        let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___f_4924_);
        v___x_4938_ =
            l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(
                v_k_4925_,
                v_mayPostpone_4926_,
                v___y_4929_,
                v___y_4930_,
                v___y_4931_,
                v___y_4932_,
                v___y_4933_,
                v___y_4934_,
            );
        return v___x_4938_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed(
    mut v___f_4939_: *mut leanh::LeanObject,
    mut v_k_4940_: *mut leanh::LeanObject,
    mut v_mayPostpone_4941_: *mut leanh::LeanObject,
    mut v___y_4942_: *mut leanh::LeanObject,
    mut v___y_4943_: *mut leanh::LeanObject,
    mut v___y_4944_: *mut leanh::LeanObject,
    mut v___y_4945_: *mut leanh::LeanObject,
    mut v___y_4946_: *mut leanh::LeanObject,
    mut v___y_4947_: *mut leanh::LeanObject,
    mut v___y_4948_: *mut leanh::LeanObject,
    mut v___y_4949_: *mut leanh::LeanObject,
    mut v___y_4950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mayPostpone_boxed_4951_: u8 = 0;
    let mut v_res_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_4951_ = (leanh::lean_unbox(v_mayPostpone_4941_) as u8);
    v_res_4952_ = l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(
        v___f_4939_,
        v_k_4940_,
        v_mayPostpone_boxed_4951_,
        v___y_4942_,
        v___y_4943_,
        v___y_4944_,
        v___y_4945_,
        v___y_4946_,
        v___y_4947_,
        v___y_4948_,
        v___y_4949_,
    );
    leanh::lean_dec(v___y_4949_);
    leanh::lean_dec_ref(v___y_4948_);
    leanh::lean_dec(v___y_4947_);
    leanh::lean_dec_ref(v___y_4946_);
    leanh::lean_dec(v___y_4945_);
    leanh::lean_dec_ref(v___y_4944_);
    leanh::lean_dec(v___y_4943_);
    leanh::lean_dec_ref(v___y_4942_);
    return v_res_4952_;
}
pub unsafe fn l_Lean_Elab_Tactic_runTermElab___redArg(
    mut v_k_4953_: *mut leanh::LeanObject,
    mut v_mayPostpone_4954_: u8,
    mut v_a_4955_: *mut leanh::LeanObject,
    mut v_a_4956_: *mut leanh::LeanObject,
    mut v_a_4957_: *mut leanh::LeanObject,
    mut v_a_4958_: *mut leanh::LeanObject,
    mut v_a_4959_: *mut leanh::LeanObject,
    mut v_a_4960_: *mut leanh::LeanObject,
    mut v_a_4961_: *mut leanh::LeanObject,
    mut v_a_4962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: u8 = 0;
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4964_ = leanh::lean_box((v_mayPostpone_4954_) as usize);
    leanh::lean_inc_ref(v_k_4953_);
    v___f_4965_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed as *mut core::ffi::c_void,
        11,
        2,
    );
    leanh::lean_closure_set(v___f_4965_, 0, v_k_4953_);
    leanh::lean_closure_set(v___f_4965_, 1, v___x_4964_);
    v___x_4966_ = leanh::lean_box((v_mayPostpone_4954_) as usize);
    v___f_4967_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed as *mut core::ffi::c_void,
        12,
        3,
    );
    leanh::lean_closure_set(v___f_4967_, 0, v___f_4965_);
    leanh::lean_closure_set(v___f_4967_, 1, v_k_4953_);
    leanh::lean_closure_set(v___f_4967_, 2, v___x_4966_);
    v___x_4968_ = 1;
    v___x_4969_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v___x_4968_, v___f_4967_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
    return v___x_4969_;
}
pub unsafe fn l_Lean_Elab_Tactic_runTermElab___redArg___boxed(
    mut v_k_4970_: *mut leanh::LeanObject,
    mut v_mayPostpone_4971_: *mut leanh::LeanObject,
    mut v_a_4972_: *mut leanh::LeanObject,
    mut v_a_4973_: *mut leanh::LeanObject,
    mut v_a_4974_: *mut leanh::LeanObject,
    mut v_a_4975_: *mut leanh::LeanObject,
    mut v_a_4976_: *mut leanh::LeanObject,
    mut v_a_4977_: *mut leanh::LeanObject,
    mut v_a_4978_: *mut leanh::LeanObject,
    mut v_a_4979_: *mut leanh::LeanObject,
    mut v_a_4980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mayPostpone_boxed_4981_: u8 = 0;
    let mut v_res_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_4981_ = (leanh::lean_unbox(v_mayPostpone_4971_) as u8);
    v_res_4982_ = l_Lean_Elab_Tactic_runTermElab___redArg(
        v_k_4970_,
        v_mayPostpone_boxed_4981_,
        v_a_4972_,
        v_a_4973_,
        v_a_4974_,
        v_a_4975_,
        v_a_4976_,
        v_a_4977_,
        v_a_4978_,
        v_a_4979_,
    );
    leanh::lean_dec(v_a_4979_);
    leanh::lean_dec_ref(v_a_4978_);
    leanh::lean_dec(v_a_4977_);
    leanh::lean_dec_ref(v_a_4976_);
    leanh::lean_dec(v_a_4975_);
    leanh::lean_dec_ref(v_a_4974_);
    leanh::lean_dec(v_a_4973_);
    leanh::lean_dec_ref(v_a_4972_);
    return v_res_4982_;
}
pub unsafe fn l_Lean_Elab_Tactic_runTermElab(
    mut v_00_u03b1_4983_: *mut leanh::LeanObject,
    mut v_k_4984_: *mut leanh::LeanObject,
    mut v_mayPostpone_4985_: u8,
    mut v_a_4986_: *mut leanh::LeanObject,
    mut v_a_4987_: *mut leanh::LeanObject,
    mut v_a_4988_: *mut leanh::LeanObject,
    mut v_a_4989_: *mut leanh::LeanObject,
    mut v_a_4990_: *mut leanh::LeanObject,
    mut v_a_4991_: *mut leanh::LeanObject,
    mut v_a_4992_: *mut leanh::LeanObject,
    mut v_a_4993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4995_ = l_Lean_Elab_Tactic_runTermElab___redArg(
        v_k_4984_,
        v_mayPostpone_4985_,
        v_a_4986_,
        v_a_4987_,
        v_a_4988_,
        v_a_4989_,
        v_a_4990_,
        v_a_4991_,
        v_a_4992_,
        v_a_4993_,
    );
    return v___x_4995_;
}
pub unsafe fn l_Lean_Elab_Tactic_runTermElab___boxed(
    mut v_00_u03b1_4996_: *mut leanh::LeanObject,
    mut v_k_4997_: *mut leanh::LeanObject,
    mut v_mayPostpone_4998_: *mut leanh::LeanObject,
    mut v_a_4999_: *mut leanh::LeanObject,
    mut v_a_5000_: *mut leanh::LeanObject,
    mut v_a_5001_: *mut leanh::LeanObject,
    mut v_a_5002_: *mut leanh::LeanObject,
    mut v_a_5003_: *mut leanh::LeanObject,
    mut v_a_5004_: *mut leanh::LeanObject,
    mut v_a_5005_: *mut leanh::LeanObject,
    mut v_a_5006_: *mut leanh::LeanObject,
    mut v_a_5007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mayPostpone_boxed_5008_: u8 = 0;
    let mut v_res_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_5008_ = (leanh::lean_unbox(v_mayPostpone_4998_) as u8);
    v_res_5009_ = l_Lean_Elab_Tactic_runTermElab(
        v_00_u03b1_4996_,
        v_k_4997_,
        v_mayPostpone_boxed_5008_,
        v_a_4999_,
        v_a_5000_,
        v_a_5001_,
        v_a_5002_,
        v_a_5003_,
        v_a_5004_,
        v_a_5005_,
        v_a_5006_,
    );
    leanh::lean_dec(v_a_5006_);
    leanh::lean_dec_ref(v_a_5005_);
    leanh::lean_dec(v_a_5004_);
    leanh::lean_dec_ref(v_a_5003_);
    leanh::lean_dec(v_a_5002_);
    leanh::lean_dec_ref(v_a_5001_);
    leanh::lean_dec(v_a_5000_);
    leanh::lean_dec_ref(v_a_4999_);
    return v_res_5009_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(
    mut v_e_5010_: *mut leanh::LeanObject,
    mut v___y_5011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5013_: u8 = 0;
    let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5027_: u8 = 0;
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5033_: u8 = 0;
    let mut v_unused_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5013_ = l_Lean_Expr_hasMVar(v_e_5010_);
                if v___x_5013_ == 0 {
                    v___x_5014_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5014_, 0, v_e_5010_);
                    return v___x_5014_;
                } else {
                    v___x_5015_ = lean_st_ref_get(v___y_5011_);
                    v_mctx_5016_ = leanh::lean_ctor_get(v___x_5015_, 0);
                    leanh::lean_inc_ref(v_mctx_5016_);
                    leanh::lean_dec(v___x_5015_);
                    v___x_5017_ = l_Lean_instantiateMVarsCore(v_mctx_5016_, v_e_5010_);
                    v_fst_5018_ = leanh::lean_ctor_get(v___x_5017_, 0);
                    leanh::lean_inc(v_fst_5018_);
                    v_snd_5019_ = leanh::lean_ctor_get(v___x_5017_, 1);
                    leanh::lean_inc(v_snd_5019_);
                    leanh::lean_dec_ref(v___x_5017_);
                    v___x_5020_ = lean_st_ref_take(v___y_5011_);
                    v_cache_5021_ = leanh::lean_ctor_get(v___x_5020_, 1);
                    v_zetaDeltaFVarIds_5022_ = leanh::lean_ctor_get(v___x_5020_, 2);
                    v_postponed_5023_ = leanh::lean_ctor_get(v___x_5020_, 3);
                    v_diag_5024_ = leanh::lean_ctor_get(v___x_5020_, 4);
                    v_isSharedCheck_5033_ = (!leanh::lean_is_exclusive(v___x_5020_)) as u8;
                    if v_isSharedCheck_5033_ == 0 {
                        v_unused_5034_ = leanh::lean_ctor_get(v___x_5020_, 0);
                        leanh::lean_dec(v_unused_5034_);
                        v___x_5026_ = v___x_5020_;
                        v_isShared_5027_ = v_isSharedCheck_5033_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_5024_);
                        leanh::lean_inc(v_postponed_5023_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_5022_);
                        leanh::lean_inc(v_cache_5021_);
                        leanh::lean_dec(v___x_5020_);
                        v___x_5026_ = leanh::lean_box(0);
                        v_isShared_5027_ = v_isSharedCheck_5033_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5027_ == 0 {
                    leanh::lean_ctor_set(v___x_5026_, 0, v_snd_5019_);
                    v___x_5029_ = v___x_5026_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5032_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_snd_5019_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5032_, 1, v_cache_5021_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5032_,
                        2,
                        v_zetaDeltaFVarIds_5022_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5032_, 3, v_postponed_5023_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5032_, 4, v_diag_5024_);
                    v___x_5029_ = v_reuseFailAlloc_5032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5030_ = lean_st_ref_set(v___y_5011_, v___x_5029_);
                v___x_5031_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5031_, 0, v_fst_5018_);
                return v___x_5031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg___boxed(
    mut v_e_5035_: *mut leanh::LeanObject,
    mut v___y_5036_: *mut leanh::LeanObject,
    mut v___y_5037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5038_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(
        v_e_5035_,
        v___y_5036_,
    );
    leanh::lean_dec(v___y_5036_);
    return v_res_5038_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0(
    mut v_e_5039_: *mut leanh::LeanObject,
    mut v___y_5040_: *mut leanh::LeanObject,
    mut v___y_5041_: *mut leanh::LeanObject,
    mut v___y_5042_: *mut leanh::LeanObject,
    mut v___y_5043_: *mut leanh::LeanObject,
    mut v___y_5044_: *mut leanh::LeanObject,
    mut v___y_5045_: *mut leanh::LeanObject,
    mut v___y_5046_: *mut leanh::LeanObject,
    mut v___y_5047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5049_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(
        v_e_5039_,
        v___y_5045_,
    );
    return v___x_5049_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___boxed(
    mut v_e_5050_: *mut leanh::LeanObject,
    mut v___y_5051_: *mut leanh::LeanObject,
    mut v___y_5052_: *mut leanh::LeanObject,
    mut v___y_5053_: *mut leanh::LeanObject,
    mut v___y_5054_: *mut leanh::LeanObject,
    mut v___y_5055_: *mut leanh::LeanObject,
    mut v___y_5056_: *mut leanh::LeanObject,
    mut v___y_5057_: *mut leanh::LeanObject,
    mut v___y_5058_: *mut leanh::LeanObject,
    mut v___y_5059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5060_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0(
        v_e_5050_,
        v___y_5051_,
        v___y_5052_,
        v___y_5053_,
        v___y_5054_,
        v___y_5055_,
        v___y_5056_,
        v___y_5057_,
        v___y_5058_,
    );
    leanh::lean_dec(v___y_5058_);
    leanh::lean_dec_ref(v___y_5057_);
    leanh::lean_dec(v___y_5056_);
    leanh::lean_dec_ref(v___y_5055_);
    leanh::lean_dec(v___y_5054_);
    leanh::lean_dec_ref(v___y_5053_);
    leanh::lean_dec(v___y_5052_);
    leanh::lean_dec_ref(v___y_5051_);
    return v_res_5060_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabTerm(
    mut v_stx_5061_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_5062_: *mut leanh::LeanObject,
    mut v_mayPostpone_5063_: u8,
    mut v_a_5064_: *mut leanh::LeanObject,
    mut v_a_5065_: *mut leanh::LeanObject,
    mut v_a_5066_: *mut leanh::LeanObject,
    mut v_a_5067_: *mut leanh::LeanObject,
    mut v_a_5068_: *mut leanh::LeanObject,
    mut v_a_5069_: *mut leanh::LeanObject,
    mut v_a_5070_: *mut leanh::LeanObject,
    mut v_a_5071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5073_: u8 = 0;
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5089_: u8 = 0;
    let mut v_cancelTk_x3f_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5091_: u8 = 0;
    let mut v_inheritedTraceOptions_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5073_ = 1;
    v___x_5074_ = leanh::lean_box((v___x_5073_) as usize);
    v___x_5075_ = leanh::lean_box((v___x_5073_) as usize);
    leanh::lean_inc(v_stx_5061_);
    v___x_5076_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Term_elabTerm___boxed as *mut core::ffi::c_void,
        11,
        4,
    );
    leanh::lean_closure_set(v___x_5076_, 0, v_stx_5061_);
    leanh::lean_closure_set(v___x_5076_, 1, v_expectedType_x3f_5062_);
    leanh::lean_closure_set(v___x_5076_, 2, v___x_5074_);
    leanh::lean_closure_set(v___x_5076_, 3, v___x_5075_);
    v_fileName_5077_ = leanh::lean_ctor_get(v_a_5070_, 0);
    v_fileMap_5078_ = leanh::lean_ctor_get(v_a_5070_, 1);
    v_options_5079_ = leanh::lean_ctor_get(v_a_5070_, 2);
    v_currRecDepth_5080_ = leanh::lean_ctor_get(v_a_5070_, 3);
    v_maxRecDepth_5081_ = leanh::lean_ctor_get(v_a_5070_, 4);
    v_ref_5082_ = leanh::lean_ctor_get(v_a_5070_, 5);
    v_currNamespace_5083_ = leanh::lean_ctor_get(v_a_5070_, 6);
    v_openDecls_5084_ = leanh::lean_ctor_get(v_a_5070_, 7);
    v_initHeartbeats_5085_ = leanh::lean_ctor_get(v_a_5070_, 8);
    v_maxHeartbeats_5086_ = leanh::lean_ctor_get(v_a_5070_, 9);
    v_quotContext_5087_ = leanh::lean_ctor_get(v_a_5070_, 10);
    v_currMacroScope_5088_ = leanh::lean_ctor_get(v_a_5070_, 11);
    v_diag_5089_ = leanh::lean_ctor_get_uint8(
        v_a_5070_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5090_ = leanh::lean_ctor_get(v_a_5070_, 12);
    v_suppressElabErrors_5091_ = leanh::lean_ctor_get_uint8(
        v_a_5070_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5092_ = leanh::lean_ctor_get(v_a_5070_, 13);
    v_ref_5093_ = l_Lean_replaceRef(v_stx_5061_, v_ref_5082_);
    leanh::lean_dec(v_stx_5061_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_5092_);
    leanh::lean_inc(v_cancelTk_x3f_5090_);
    leanh::lean_inc(v_currMacroScope_5088_);
    leanh::lean_inc(v_quotContext_5087_);
    leanh::lean_inc(v_maxHeartbeats_5086_);
    leanh::lean_inc(v_initHeartbeats_5085_);
    leanh::lean_inc(v_openDecls_5084_);
    leanh::lean_inc(v_currNamespace_5083_);
    leanh::lean_inc(v_maxRecDepth_5081_);
    leanh::lean_inc(v_currRecDepth_5080_);
    leanh::lean_inc_ref(v_options_5079_);
    leanh::lean_inc_ref(v_fileMap_5078_);
    leanh::lean_inc_ref(v_fileName_5077_);
    v___x_5094_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_5094_, 0, v_fileName_5077_);
    leanh::lean_ctor_set(v___x_5094_, 1, v_fileMap_5078_);
    leanh::lean_ctor_set(v___x_5094_, 2, v_options_5079_);
    leanh::lean_ctor_set(v___x_5094_, 3, v_currRecDepth_5080_);
    leanh::lean_ctor_set(v___x_5094_, 4, v_maxRecDepth_5081_);
    leanh::lean_ctor_set(v___x_5094_, 5, v_ref_5093_);
    leanh::lean_ctor_set(v___x_5094_, 6, v_currNamespace_5083_);
    leanh::lean_ctor_set(v___x_5094_, 7, v_openDecls_5084_);
    leanh::lean_ctor_set(v___x_5094_, 8, v_initHeartbeats_5085_);
    leanh::lean_ctor_set(v___x_5094_, 9, v_maxHeartbeats_5086_);
    leanh::lean_ctor_set(v___x_5094_, 10, v_quotContext_5087_);
    leanh::lean_ctor_set(v___x_5094_, 11, v_currMacroScope_5088_);
    leanh::lean_ctor_set(v___x_5094_, 12, v_cancelTk_x3f_5090_);
    leanh::lean_ctor_set(v___x_5094_, 13, v_inheritedTraceOptions_5092_);
    leanh::lean_ctor_set_uint8(
        v___x_5094_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_5089_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_5094_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5091_,
    );
    v___x_5095_ = l_Lean_Elab_Tactic_runTermElab___redArg(
        v___x_5076_,
        v_mayPostpone_5063_,
        v_a_5064_,
        v_a_5065_,
        v_a_5066_,
        v_a_5067_,
        v_a_5068_,
        v_a_5069_,
        v___x_5094_,
        v_a_5071_,
    );
    leanh::lean_dec_ref_known(v___x_5094_, 14);
    if leanh::lean_obj_tag(v___x_5095_) == 0 {
        let mut v_a_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_5096_ = leanh::lean_ctor_get(v___x_5095_, 0);
        leanh::lean_inc(v_a_5096_);
        leanh::lean_dec_ref_known(v___x_5095_, 1);
        v___x_5097_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(
            v_a_5096_, v_a_5069_,
        );
        return v___x_5097_;
    } else {
        return v___x_5095_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabTerm___boxed(
    mut v_stx_5098_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_5099_: *mut leanh::LeanObject,
    mut v_mayPostpone_5100_: *mut leanh::LeanObject,
    mut v_a_5101_: *mut leanh::LeanObject,
    mut v_a_5102_: *mut leanh::LeanObject,
    mut v_a_5103_: *mut leanh::LeanObject,
    mut v_a_5104_: *mut leanh::LeanObject,
    mut v_a_5105_: *mut leanh::LeanObject,
    mut v_a_5106_: *mut leanh::LeanObject,
    mut v_a_5107_: *mut leanh::LeanObject,
    mut v_a_5108_: *mut leanh::LeanObject,
    mut v_a_5109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mayPostpone_boxed_5110_: u8 = 0;
    let mut v_res_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_5110_ = (leanh::lean_unbox(v_mayPostpone_5100_) as u8);
    v_res_5111_ = l_Lean_Elab_Tactic_elabTerm(
        v_stx_5098_,
        v_expectedType_x3f_5099_,
        v_mayPostpone_boxed_5110_,
        v_a_5101_,
        v_a_5102_,
        v_a_5103_,
        v_a_5104_,
        v_a_5105_,
        v_a_5106_,
        v_a_5107_,
        v_a_5108_,
    );
    leanh::lean_dec(v_a_5108_);
    leanh::lean_dec_ref(v_a_5107_);
    leanh::lean_dec(v_a_5106_);
    leanh::lean_dec_ref(v_a_5105_);
    leanh::lean_dec(v_a_5104_);
    leanh::lean_dec_ref(v_a_5103_);
    leanh::lean_dec(v_a_5102_);
    leanh::lean_dec_ref(v_a_5101_);
    return v_res_5111_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabTermEnsuringType(
    mut v_stx_5112_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_5113_: *mut leanh::LeanObject,
    mut v_mayPostpone_5114_: u8,
    mut v_a_5115_: *mut leanh::LeanObject,
    mut v_a_5116_: *mut leanh::LeanObject,
    mut v_a_5117_: *mut leanh::LeanObject,
    mut v_a_5118_: *mut leanh::LeanObject,
    mut v_a_5119_: *mut leanh::LeanObject,
    mut v_a_5120_: *mut leanh::LeanObject,
    mut v_a_5121_: *mut leanh::LeanObject,
    mut v_a_5122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5131_: u8 = 0;
    let mut v_a_5133_: u8 = 0;
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5138_: u8 = 0;
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5142_: u8 = 0;
    let mut v_unused_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5147_: u8 = 0;
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5151_: u8 = 0;
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5156_: u8 = 0;
    let mut v_ctxApprox_5157_: u8 = 0;
    let mut v_quasiPatternApprox_5158_: u8 = 0;
    let mut v_constApprox_5159_: u8 = 0;
    let mut v_isDefEqStuckEx_5160_: u8 = 0;
    let mut v_unificationHints_5161_: u8 = 0;
    let mut v_proofIrrelevance_5162_: u8 = 0;
    let mut v_offsetCnstrs_5163_: u8 = 0;
    let mut v_transparency_5164_: u8 = 0;
    let mut v_etaStruct_5165_: u8 = 0;
    let mut v_univApprox_5166_: u8 = 0;
    let mut v_iota_5167_: u8 = 0;
    let mut v_beta_5168_: u8 = 0;
    let mut v_proj_5169_: u8 = 0;
    let mut v_zeta_5170_: u8 = 0;
    let mut v_zetaDelta_5171_: u8 = 0;
    let mut v_zetaUnused_5172_: u8 = 0;
    let mut v_zetaHave_5173_: u8 = 0;
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5176_: u8 = 0;
    let mut v_trackZetaDelta_5177_: u8 = 0;
    let mut v_zetaDeltaSet_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5184_: u8 = 0;
    let mut v_inTypeClassResolution_5185_: u8 = 0;
    let mut v_cacheInferType_5186_: u8 = 0;
    let mut v___x_5187_: u8 = 0;
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: u64 = 0;
    let mut v___x_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: u8 = 0;
    let mut v_a_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: u8 = 0;
    let mut v_a_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut v_reuseFailAlloc_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5207_: u8 = 0;
    let mut v_isSharedCheck_5208_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_expectedType_x3f_5113_);
                v___x_5124_ = l_Lean_Elab_Tactic_elabTerm(
                    v_stx_5112_,
                    v_expectedType_x3f_5113_,
                    v_mayPostpone_5114_,
                    v_a_5115_,
                    v_a_5116_,
                    v_a_5117_,
                    v_a_5118_,
                    v_a_5119_,
                    v_a_5120_,
                    v_a_5121_,
                    v_a_5122_,
                );
                if leanh::lean_obj_tag(v___x_5124_) == 0 {
                    if leanh::lean_obj_tag(v_expectedType_x3f_5113_) == 0 {
                        return v___x_5124_;
                    } else {
                        v_a_5125_ = leanh::lean_ctor_get(v___x_5124_, 0);
                        leanh::lean_inc_n(v_a_5125_, 2);
                        leanh::lean_dec_ref_known(v___x_5124_, 1);
                        v_val_5126_ = leanh::lean_ctor_get(v_expectedType_x3f_5113_, 0);
                        leanh::lean_inc(v_val_5126_);
                        leanh::lean_dec_ref_known(v_expectedType_x3f_5113_, 1);
                        leanh::lean_inc(v_a_5122_);
                        leanh::lean_inc_ref(v_a_5121_);
                        leanh::lean_inc(v_a_5120_);
                        leanh::lean_inc_ref(v_a_5119_);
                        v___x_5127_ =
                            lean_infer_type(v_a_5125_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_);
                        if leanh::lean_obj_tag(v___x_5127_) == 0 {
                            v_a_5128_ = leanh::lean_ctor_get(v___x_5127_, 0);
                            v_isSharedCheck_5208_ =
                                (!leanh::lean_is_exclusive(v___x_5127_)) as u8;
                            if v_isSharedCheck_5208_ == 0 {
                                v___x_5130_ = v___x_5127_;
                                v_isShared_5131_ = v_isSharedCheck_5208_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5128_);
                                leanh::lean_dec(v___x_5127_);
                                v___x_5130_ = leanh::lean_box(0);
                                v_isShared_5131_ = v_isSharedCheck_5208_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_val_5126_);
                            leanh::lean_dec(v_a_5125_);
                            return v___x_5127_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_expectedType_x3f_5113_);
                    return v___x_5124_;
                }
            }
            1 => {
                v___x_5155_ = l_Lean_Meta_Context_config(v_a_5119_);
                v_foApprox_5156_ = leanh::lean_ctor_get_uint8(v___x_5155_, 0 as u32);
                v_ctxApprox_5157_ = leanh::lean_ctor_get_uint8(v___x_5155_, 1 as u32);
                v_quasiPatternApprox_5158_ =
                    leanh::lean_ctor_get_uint8(v___x_5155_, 2 as u32);
                v_constApprox_5159_ = leanh::lean_ctor_get_uint8(v___x_5155_, 3 as u32);
                v_isDefEqStuckEx_5160_ = leanh::lean_ctor_get_uint8(v___x_5155_, 4 as u32);
                v_unificationHints_5161_ = leanh::lean_ctor_get_uint8(v___x_5155_, 5 as u32);
                v_proofIrrelevance_5162_ = leanh::lean_ctor_get_uint8(v___x_5155_, 6 as u32);
                v_offsetCnstrs_5163_ = leanh::lean_ctor_get_uint8(v___x_5155_, 8 as u32);
                v_transparency_5164_ = leanh::lean_ctor_get_uint8(v___x_5155_, 9 as u32);
                v_etaStruct_5165_ = leanh::lean_ctor_get_uint8(v___x_5155_, 10 as u32);
                v_univApprox_5166_ = leanh::lean_ctor_get_uint8(v___x_5155_, 11 as u32);
                v_iota_5167_ = leanh::lean_ctor_get_uint8(v___x_5155_, 12 as u32);
                v_beta_5168_ = leanh::lean_ctor_get_uint8(v___x_5155_, 13 as u32);
                v_proj_5169_ = leanh::lean_ctor_get_uint8(v___x_5155_, 14 as u32);
                v_zeta_5170_ = leanh::lean_ctor_get_uint8(v___x_5155_, 15 as u32);
                v_zetaDelta_5171_ = leanh::lean_ctor_get_uint8(v___x_5155_, 16 as u32);
                v_zetaUnused_5172_ = leanh::lean_ctor_get_uint8(v___x_5155_, 17 as u32);
                v_zetaHave_5173_ = leanh::lean_ctor_get_uint8(v___x_5155_, 18 as u32);
                v_isSharedCheck_5207_ = (!leanh::lean_is_exclusive(v___x_5155_)) as u8;
                if v_isSharedCheck_5207_ == 0 {
                    v___x_5175_ = v___x_5155_;
                    v_isShared_5176_ = v_isSharedCheck_5207_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_dec(v___x_5155_);
                    v___x_5175_ = leanh::lean_box(0);
                    v_isShared_5176_ = v_isSharedCheck_5207_;
                    state = 8;
                    continue;
                }
            }
            2 => {
                if v_a_5133_ == 0 {
                    leanh::lean_del_object(v___x_5130_);
                    v___x_5134_ = leanh::lean_box(0);
                    leanh::lean_inc(v_a_5125_);
                    v___x_5135_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(
                        v___x_5134_,
                        v_val_5126_,
                        v_a_5128_,
                        v_a_5125_,
                        v___x_5134_,
                        v_a_5119_,
                        v_a_5120_,
                        v_a_5121_,
                        v_a_5122_,
                    );
                    if leanh::lean_obj_tag(v___x_5135_) == 0 {
                        v_isSharedCheck_5142_ =
                            (!leanh::lean_is_exclusive(v___x_5135_)) as u8;
                        if v_isSharedCheck_5142_ == 0 {
                            v_unused_5143_ = leanh::lean_ctor_get(v___x_5135_, 0);
                            leanh::lean_dec(v_unused_5143_);
                            v___x_5137_ = v___x_5135_;
                            v_isShared_5138_ = v_isSharedCheck_5142_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5135_);
                            v___x_5137_ = leanh::lean_box(0);
                            v_isShared_5138_ = v_isSharedCheck_5142_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_5125_);
                        v_a_5144_ = leanh::lean_ctor_get(v___x_5135_, 0);
                        v_isSharedCheck_5151_ =
                            (!leanh::lean_is_exclusive(v___x_5135_)) as u8;
                        if v_isSharedCheck_5151_ == 0 {
                            v___x_5146_ = v___x_5135_;
                            v_isShared_5147_ = v_isSharedCheck_5151_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5144_);
                            leanh::lean_dec(v___x_5135_);
                            v___x_5146_ = leanh::lean_box(0);
                            v_isShared_5147_ = v_isSharedCheck_5151_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5128_);
                    leanh::lean_dec(v_val_5126_);
                    if v_isShared_5131_ == 0 {
                        leanh::lean_ctor_set(v___x_5130_, 0, v_a_5125_);
                        v___x_5153_ = v___x_5130_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5154_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5125_);
                        v___x_5153_ = v_reuseFailAlloc_5154_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5138_ == 0 {
                    leanh::lean_ctor_set(v___x_5137_, 0, v_a_5125_);
                    v___x_5140_ = v___x_5137_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5141_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5125_);
                    v___x_5140_ = v_reuseFailAlloc_5141_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5140_;
            }
            5 => {
                if v_isShared_5147_ == 0 {
                    v___x_5149_ = v___x_5146_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5150_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_a_5144_);
                    v___x_5149_ = v_reuseFailAlloc_5150_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5149_;
            }
            7 => {
                return v___x_5153_;
            }
            8 => {
                v_trackZetaDelta_5177_ = leanh::lean_ctor_get_uint8(
                    v_a_5119_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5178_ = leanh::lean_ctor_get(v_a_5119_, 1);
                v_lctx_5179_ = leanh::lean_ctor_get(v_a_5119_, 2);
                v_localInstances_5180_ = leanh::lean_ctor_get(v_a_5119_, 3);
                v_defEqCtx_x3f_5181_ = leanh::lean_ctor_get(v_a_5119_, 4);
                v_synthPendingDepth_5182_ = leanh::lean_ctor_get(v_a_5119_, 5);
                v_canUnfold_x3f_5183_ = leanh::lean_ctor_get(v_a_5119_, 6);
                v_univApprox_5184_ = leanh::lean_ctor_get_uint8(
                    v_a_5119_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5185_ = leanh::lean_ctor_get_uint8(
                    v_a_5119_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5186_ = leanh::lean_ctor_get_uint8(
                    v_a_5119_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_5187_ = 1;
                if v_isShared_5176_ == 0 {
                    v___x_5189_ = v___x_5175_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5206_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        0 as u32,
                        v_foApprox_5156_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        1 as u32,
                        v_ctxApprox_5157_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        2 as u32,
                        v_quasiPatternApprox_5158_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        3 as u32,
                        v_constApprox_5159_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        4 as u32,
                        v_isDefEqStuckEx_5160_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        5 as u32,
                        v_unificationHints_5161_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        6 as u32,
                        v_proofIrrelevance_5162_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        8 as u32,
                        v_offsetCnstrs_5163_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        9 as u32,
                        v_transparency_5164_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        10 as u32,
                        v_etaStruct_5165_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        11 as u32,
                        v_univApprox_5166_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        12 as u32,
                        v_iota_5167_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        13 as u32,
                        v_beta_5168_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        14 as u32,
                        v_proj_5169_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        15 as u32,
                        v_zeta_5170_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        16 as u32,
                        v_zetaDelta_5171_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        17 as u32,
                        v_zetaUnused_5172_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5206_,
                        18 as u32,
                        v_zetaHave_5173_,
                    );
                    v___x_5189_ = v_reuseFailAlloc_5206_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                leanh::lean_ctor_set_uint8(v___x_5189_, 7 as u32, v___x_5187_);
                v___x_5190_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5189_);
                v___x_5191_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_5191_, 0, v___x_5189_);
                leanh::lean_ctor_set_uint64(
                    v___x_5191_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_5190_,
                );
                leanh::lean_inc(v_canUnfold_x3f_5183_);
                leanh::lean_inc(v_synthPendingDepth_5182_);
                leanh::lean_inc(v_defEqCtx_x3f_5181_);
                leanh::lean_inc_ref(v_localInstances_5180_);
                leanh::lean_inc_ref(v_lctx_5179_);
                leanh::lean_inc(v_zetaDeltaSet_5178_);
                v___x_5192_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_5192_, 0, v___x_5191_);
                leanh::lean_ctor_set(v___x_5192_, 1, v_zetaDeltaSet_5178_);
                leanh::lean_ctor_set(v___x_5192_, 2, v_lctx_5179_);
                leanh::lean_ctor_set(v___x_5192_, 3, v_localInstances_5180_);
                leanh::lean_ctor_set(v___x_5192_, 4, v_defEqCtx_x3f_5181_);
                leanh::lean_ctor_set(v___x_5192_, 5, v_synthPendingDepth_5182_);
                leanh::lean_ctor_set(v___x_5192_, 6, v_canUnfold_x3f_5183_);
                leanh::lean_ctor_set_uint8(
                    v___x_5192_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5177_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5192_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5184_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5192_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5185_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5192_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5186_,
                );
                leanh::lean_inc(v_val_5126_);
                leanh::lean_inc(v_a_5128_);
                v___x_5193_ = l_Lean_Meta_isExprDefEq(
                    v_a_5128_,
                    v_val_5126_,
                    v___x_5192_,
                    v_a_5120_,
                    v_a_5121_,
                    v_a_5122_,
                );
                leanh::lean_dec_ref_known(v___x_5192_, 7);
                if leanh::lean_obj_tag(v___x_5193_) == 0 {
                    v_a_5194_ = leanh::lean_ctor_get(v___x_5193_, 0);
                    leanh::lean_inc(v_a_5194_);
                    leanh::lean_dec_ref_known(v___x_5193_, 1);
                    v___x_5195_ = (leanh::lean_unbox(v_a_5194_) as u8);
                    leanh::lean_dec(v_a_5194_);
                    v_a_5133_ = v___x_5195_;
                    state = 2;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___x_5193_) == 0 {
                        v_a_5196_ = leanh::lean_ctor_get(v___x_5193_, 0);
                        leanh::lean_inc(v_a_5196_);
                        leanh::lean_dec_ref_known(v___x_5193_, 1);
                        v___x_5197_ = (leanh::lean_unbox(v_a_5196_) as u8);
                        leanh::lean_dec(v_a_5196_);
                        v_a_5133_ = v___x_5197_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_5130_);
                        leanh::lean_dec(v_a_5128_);
                        leanh::lean_dec(v_val_5126_);
                        leanh::lean_dec(v_a_5125_);
                        v_a_5198_ = leanh::lean_ctor_get(v___x_5193_, 0);
                        v_isSharedCheck_5205_ =
                            (!leanh::lean_is_exclusive(v___x_5193_)) as u8;
                        if v_isSharedCheck_5205_ == 0 {
                            v___x_5200_ = v___x_5193_;
                            v_isShared_5201_ = v_isSharedCheck_5205_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5198_);
                            leanh::lean_dec(v___x_5193_);
                            v___x_5200_ = leanh::lean_box(0);
                            v_isShared_5201_ = v_isSharedCheck_5205_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            10 => {
                if v_isShared_5201_ == 0 {
                    v___x_5203_ = v___x_5200_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5204_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
                    v___x_5203_ = v_reuseFailAlloc_5204_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5203_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabTermEnsuringType___boxed(
    mut v_stx_5209_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_5210_: *mut leanh::LeanObject,
    mut v_mayPostpone_5211_: *mut leanh::LeanObject,
    mut v_a_5212_: *mut leanh::LeanObject,
    mut v_a_5213_: *mut leanh::LeanObject,
    mut v_a_5214_: *mut leanh::LeanObject,
    mut v_a_5215_: *mut leanh::LeanObject,
    mut v_a_5216_: *mut leanh::LeanObject,
    mut v_a_5217_: *mut leanh::LeanObject,
    mut v_a_5218_: *mut leanh::LeanObject,
    mut v_a_5219_: *mut leanh::LeanObject,
    mut v_a_5220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mayPostpone_boxed_5221_: u8 = 0;
    let mut v_res_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_5221_ = (leanh::lean_unbox(v_mayPostpone_5211_) as u8);
    v_res_5222_ = l_Lean_Elab_Tactic_elabTermEnsuringType(
        v_stx_5209_,
        v_expectedType_x3f_5210_,
        v_mayPostpone_boxed_5221_,
        v_a_5212_,
        v_a_5213_,
        v_a_5214_,
        v_a_5215_,
        v_a_5216_,
        v_a_5217_,
        v_a_5218_,
        v_a_5219_,
    );
    leanh::lean_dec(v_a_5219_);
    leanh::lean_dec_ref(v_a_5218_);
    leanh::lean_dec(v_a_5217_);
    leanh::lean_dec_ref(v_a_5216_);
    leanh::lean_dec(v_a_5215_);
    leanh::lean_dec_ref(v_a_5214_);
    leanh::lean_dec(v_a_5213_);
    leanh::lean_dec_ref(v_a_5212_);
    return v_res_5222_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5223_ = leanh::lean_box(0);
    v___x_5224_ = l_Lean_Elab_abortTacticExceptionId;
    v___x_5225_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5225_, 0, v___x_5224_);
    leanh::lean_ctor_set(v___x_5225_, 1, v___x_5223_);
    return v___x_5225_;
}
pub unsafe fn l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5227_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0);
    v___x_5228_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5228_, 0, v___x_5227_);
    return v___x_5228_;
}
pub unsafe fn l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___boxed(
    mut v___y_5229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5230_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
    return v_res_5230_;
}
pub unsafe fn l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(
    mut v_00_u03b1_5231_: *mut leanh::LeanObject,
    mut v___y_5232_: *mut leanh::LeanObject,
    mut v___y_5233_: *mut leanh::LeanObject,
    mut v___y_5234_: *mut leanh::LeanObject,
    mut v___y_5235_: *mut leanh::LeanObject,
    mut v___y_5236_: *mut leanh::LeanObject,
    mut v___y_5237_: *mut leanh::LeanObject,
    mut v___y_5238_: *mut leanh::LeanObject,
    mut v___y_5239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5241_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
    return v___x_5241_;
}
pub unsafe fn l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___boxed(
    mut v_00_u03b1_5242_: *mut leanh::LeanObject,
    mut v___y_5243_: *mut leanh::LeanObject,
    mut v___y_5244_: *mut leanh::LeanObject,
    mut v___y_5245_: *mut leanh::LeanObject,
    mut v___y_5246_: *mut leanh::LeanObject,
    mut v___y_5247_: *mut leanh::LeanObject,
    mut v___y_5248_: *mut leanh::LeanObject,
    mut v___y_5249_: *mut leanh::LeanObject,
    mut v___y_5250_: *mut leanh::LeanObject,
    mut v___y_5251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5252_ =
        l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(
            v_00_u03b1_5242_,
            v___y_5243_,
            v___y_5244_,
            v___y_5245_,
            v___y_5246_,
            v___y_5247_,
            v___y_5248_,
            v___y_5249_,
            v___y_5250_,
        );
    leanh::lean_dec(v___y_5250_);
    leanh::lean_dec_ref(v___y_5249_);
    leanh::lean_dec(v___y_5248_);
    leanh::lean_dec_ref(v___y_5247_);
    leanh::lean_dec(v___y_5246_);
    leanh::lean_dec_ref(v___y_5245_);
    leanh::lean_dec(v___y_5244_);
    leanh::lean_dec_ref(v___y_5243_);
    return v_res_5252_;
}
pub unsafe fn l_Lean_Elab_Tactic_logUnassignedAndAbort(
    mut v_mvarIds_5253_: *mut leanh::LeanObject,
    mut v_a_5254_: *mut leanh::LeanObject,
    mut v_a_5255_: *mut leanh::LeanObject,
    mut v_a_5256_: *mut leanh::LeanObject,
    mut v_a_5257_: *mut leanh::LeanObject,
    mut v_a_5258_: *mut leanh::LeanObject,
    mut v_a_5259_: *mut leanh::LeanObject,
    mut v_a_5260_: *mut leanh::LeanObject,
    mut v_a_5261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5268_: u8 = 0;
    let mut v___x_5269_: u8 = 0;
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut v_a_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5279_: u8 = 0;
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5263_ = leanh::lean_box(0);
                v___x_5264_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                    v_mvarIds_5253_,
                    v___x_5263_,
                    v_a_5256_,
                    v_a_5257_,
                    v_a_5258_,
                    v_a_5259_,
                    v_a_5260_,
                    v_a_5261_,
                );
                if leanh::lean_obj_tag(v___x_5264_) == 0 {
                    v_a_5265_ = leanh::lean_ctor_get(v___x_5264_, 0);
                    v_isSharedCheck_5275_ = (!leanh::lean_is_exclusive(v___x_5264_)) as u8;
                    if v_isSharedCheck_5275_ == 0 {
                        v___x_5267_ = v___x_5264_;
                        v_isShared_5268_ = v_isSharedCheck_5275_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5265_);
                        leanh::lean_dec(v___x_5264_);
                        v___x_5267_ = leanh::lean_box(0);
                        v_isShared_5268_ = v_isSharedCheck_5275_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5276_ = leanh::lean_ctor_get(v___x_5264_, 0);
                    v_isSharedCheck_5283_ = (!leanh::lean_is_exclusive(v___x_5264_)) as u8;
                    if v_isSharedCheck_5283_ == 0 {
                        v___x_5278_ = v___x_5264_;
                        v_isShared_5279_ = v_isSharedCheck_5283_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5276_);
                        leanh::lean_dec(v___x_5264_);
                        v___x_5278_ = leanh::lean_box(0);
                        v_isShared_5279_ = v_isSharedCheck_5283_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5269_ = (leanh::lean_unbox(v_a_5265_) as u8);
                leanh::lean_dec(v_a_5265_);
                if v___x_5269_ == 0 {
                    v___x_5270_ = leanh::lean_box(0);
                    if v_isShared_5268_ == 0 {
                        leanh::lean_ctor_set(v___x_5267_, 0, v___x_5270_);
                        v___x_5272_ = v___x_5267_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5273_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5273_, 0, v___x_5270_);
                        v___x_5272_ = v_reuseFailAlloc_5273_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5267_);
                    v___x_5274_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
                    return v___x_5274_;
                }
            }
            2 => {
                return v___x_5272_;
            }
            3 => {
                if v_isShared_5279_ == 0 {
                    v___x_5281_ = v___x_5278_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_a_5276_);
                    v___x_5281_ = v_reuseFailAlloc_5282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_logUnassignedAndAbort___boxed(
    mut v_mvarIds_5284_: *mut leanh::LeanObject,
    mut v_a_5285_: *mut leanh::LeanObject,
    mut v_a_5286_: *mut leanh::LeanObject,
    mut v_a_5287_: *mut leanh::LeanObject,
    mut v_a_5288_: *mut leanh::LeanObject,
    mut v_a_5289_: *mut leanh::LeanObject,
    mut v_a_5290_: *mut leanh::LeanObject,
    mut v_a_5291_: *mut leanh::LeanObject,
    mut v_a_5292_: *mut leanh::LeanObject,
    mut v_a_5293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5294_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(
        v_mvarIds_5284_,
        v_a_5285_,
        v_a_5286_,
        v_a_5287_,
        v_a_5288_,
        v_a_5289_,
        v_a_5290_,
        v_a_5291_,
        v_a_5292_,
    );
    leanh::lean_dec(v_a_5292_);
    leanh::lean_dec_ref(v_a_5291_);
    leanh::lean_dec(v_a_5290_);
    leanh::lean_dec_ref(v_a_5289_);
    leanh::lean_dec(v_a_5288_);
    leanh::lean_dec_ref(v_a_5287_);
    leanh::lean_dec(v_a_5286_);
    leanh::lean_dec_ref(v_a_5285_);
    leanh::lean_dec_ref(v_mvarIds_5284_);
    return v_res_5294_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(
    mut v___x_5295_: *mut leanh::LeanObject,
    mut v_mvarCounterSaved_5296_: *mut leanh::LeanObject,
    mut v_as_5297_: *mut leanh::LeanObject,
    mut v_i_5298_: usize,
    mut v_stop_5299_: usize,
    mut v_b_5300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: usize = 0;
    let mut v___x_5304_: usize = 0;
    let mut v___x_5306_: u8 = 0;
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: u8 = 0;
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5306_ = lean_usize_dec_eq(v_i_5298_, v_stop_5299_);
                if v___x_5306_ == 0 {
                    v___x_5307_ = lean_array_uget_borrowed(v_as_5297_, v_i_5298_);
                    leanh::lean_inc(v___x_5307_);
                    v___x_5308_ = l_Lean_MetavarContext_getDecl(v___x_5295_, v___x_5307_);
                    v_index_5309_ = leanh::lean_ctor_get(v___x_5308_, 6);
                    leanh::lean_inc(v_index_5309_);
                    leanh::lean_dec_ref(v___x_5308_);
                    v___x_5310_ = lean_nat_dec_le(v_mvarCounterSaved_5296_, v_index_5309_);
                    leanh::lean_dec(v_index_5309_);
                    if v___x_5310_ == 0 {
                        v___y_5302_ = v_b_5300_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_5307_);
                        v___x_5311_ = lean_array_push(v_b_5300_, v___x_5307_);
                        v___y_5302_ = v___x_5311_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5300_;
                }
            }
            1 => {
                v___x_5303_ = 1usize;
                v___x_5304_ = lean_usize_add(v_i_5298_, v___x_5303_);
                v_i_5298_ = v___x_5304_;
                v_b_5300_ = v___y_5302_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0___boxed(
    mut v___x_5312_: *mut leanh::LeanObject,
    mut v_mvarCounterSaved_5313_: *mut leanh::LeanObject,
    mut v_as_5314_: *mut leanh::LeanObject,
    mut v_i_5315_: *mut leanh::LeanObject,
    mut v_stop_5316_: *mut leanh::LeanObject,
    mut v_b_5317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5318_: usize = 0;
    let mut v_stop_boxed_5319_: usize = 0;
    let mut v_res_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5318_ = leanh::lean_unbox_usize(v_i_5315_);
    leanh::lean_dec(v_i_5315_);
    v_stop_boxed_5319_ = leanh::lean_unbox_usize(v_stop_5316_);
    leanh::lean_dec(v_stop_5316_);
    v_res_5320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v___x_5312_, v_mvarCounterSaved_5313_, v_as_5314_, v_i_boxed_5318_, v_stop_boxed_5319_, v_b_5317_);
    leanh::lean_dec_ref(v_as_5314_);
    leanh::lean_dec(v_mvarCounterSaved_5313_);
    leanh::lean_dec_ref(v___x_5312_);
    return v_res_5320_;
}
pub unsafe fn l_Lean_Elab_Tactic_filterOldMVars___redArg(
    mut v_mvarIds_5323_: *mut leanh::LeanObject,
    mut v_mvarCounterSaved_5324_: *mut leanh::LeanObject,
    mut v_a_5325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: u8 = 0;
    v___x_5327_ = lean_st_ref_get(v_a_5325_);
    v___x_5328_ = leanh::lean_unsigned_to_nat(0);
    v___x_5329_ = lean_array_get_size(v_mvarIds_5323_);
    v___x_5330_ = l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0;
    v___x_5331_ = lean_nat_dec_lt(v___x_5328_, v___x_5329_);
    if v___x_5331_ == 0 {
        let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_5327_);
        v___x_5332_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5332_, 0, v___x_5330_);
        return v___x_5332_;
    } else {
        let mut v_mctx_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5334_: u8 = 0;
        v_mctx_5333_ = leanh::lean_ctor_get(v___x_5327_, 0);
        leanh::lean_inc_ref(v_mctx_5333_);
        leanh::lean_dec(v___x_5327_);
        v___x_5334_ = lean_nat_dec_le(v___x_5329_, v___x_5329_);
        if v___x_5334_ == 0 {
            if v___x_5331_ == 0 {
                let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_mctx_5333_);
                v___x_5335_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5335_, 0, v___x_5330_);
                return v___x_5335_;
            } else {
                let mut v___x_5336_: usize = 0;
                let mut v___x_5337_: usize = 0;
                let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5336_ = 0usize;
                v___x_5337_ = lean_usize_of_nat(v___x_5329_);
                v___x_5338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v_mctx_5333_, v_mvarCounterSaved_5324_, v_mvarIds_5323_, v___x_5336_, v___x_5337_, v___x_5330_);
                leanh::lean_dec_ref(v_mctx_5333_);
                v___x_5339_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5339_, 0, v___x_5338_);
                return v___x_5339_;
            }
        } else {
            let mut v___x_5340_: usize = 0;
            let mut v___x_5341_: usize = 0;
            let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5340_ = 0usize;
            v___x_5341_ = lean_usize_of_nat(v___x_5329_);
            v___x_5342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v_mctx_5333_, v_mvarCounterSaved_5324_, v_mvarIds_5323_, v___x_5340_, v___x_5341_, v___x_5330_);
            leanh::lean_dec_ref(v_mctx_5333_);
            v___x_5343_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5343_, 0, v___x_5342_);
            return v___x_5343_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_filterOldMVars___redArg___boxed(
    mut v_mvarIds_5344_: *mut leanh::LeanObject,
    mut v_mvarCounterSaved_5345_: *mut leanh::LeanObject,
    mut v_a_5346_: *mut leanh::LeanObject,
    mut v_a_5347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5348_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(
        v_mvarIds_5344_,
        v_mvarCounterSaved_5345_,
        v_a_5346_,
    );
    leanh::lean_dec(v_a_5346_);
    leanh::lean_dec(v_mvarCounterSaved_5345_);
    leanh::lean_dec_ref(v_mvarIds_5344_);
    return v_res_5348_;
}
pub unsafe fn l_Lean_Elab_Tactic_filterOldMVars(
    mut v_mvarIds_5349_: *mut leanh::LeanObject,
    mut v_mvarCounterSaved_5350_: *mut leanh::LeanObject,
    mut v_a_5351_: *mut leanh::LeanObject,
    mut v_a_5352_: *mut leanh::LeanObject,
    mut v_a_5353_: *mut leanh::LeanObject,
    mut v_a_5354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5356_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(
        v_mvarIds_5349_,
        v_mvarCounterSaved_5350_,
        v_a_5352_,
    );
    return v___x_5356_;
}
pub unsafe fn l_Lean_Elab_Tactic_filterOldMVars___boxed(
    mut v_mvarIds_5357_: *mut leanh::LeanObject,
    mut v_mvarCounterSaved_5358_: *mut leanh::LeanObject,
    mut v_a_5359_: *mut leanh::LeanObject,
    mut v_a_5360_: *mut leanh::LeanObject,
    mut v_a_5361_: *mut leanh::LeanObject,
    mut v_a_5362_: *mut leanh::LeanObject,
    mut v_a_5363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5364_ = l_Lean_Elab_Tactic_filterOldMVars(
        v_mvarIds_5357_,
        v_mvarCounterSaved_5358_,
        v_a_5359_,
        v_a_5360_,
        v_a_5361_,
        v_a_5362_,
    );
    leanh::lean_dec(v_a_5362_);
    leanh::lean_dec_ref(v_a_5361_);
    leanh::lean_dec(v_a_5360_);
    leanh::lean_dec_ref(v_a_5359_);
    leanh::lean_dec(v_mvarCounterSaved_5358_);
    leanh::lean_dec_ref(v_mvarIds_5357_);
    return v_res_5364_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(
    mut v_x_5365_: *mut leanh::LeanObject,
    mut v___y_5366_: *mut leanh::LeanObject,
    mut v___y_5367_: *mut leanh::LeanObject,
    mut v___y_5368_: *mut leanh::LeanObject,
    mut v___y_5369_: *mut leanh::LeanObject,
    mut v___y_5370_: *mut leanh::LeanObject,
    mut v___y_5371_: *mut leanh::LeanObject,
    mut v___y_5372_: *mut leanh::LeanObject,
    mut v___y_5373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_5369_);
    leanh::lean_inc_ref(v___y_5368_);
    leanh::lean_inc(v___y_5367_);
    leanh::lean_inc_ref(v___y_5366_);
    v___x_5375_ = leanh::lean_apply_9(
        v_x_5365_,
        v___y_5366_,
        v___y_5367_,
        v___y_5368_,
        v___y_5369_,
        v___y_5370_,
        v___y_5371_,
        v___y_5372_,
        v___y_5373_,
        leanh::lean_box(0),
    );
    return v___x_5375_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed(
    mut v_x_5376_: *mut leanh::LeanObject,
    mut v___y_5377_: *mut leanh::LeanObject,
    mut v___y_5378_: *mut leanh::LeanObject,
    mut v___y_5379_: *mut leanh::LeanObject,
    mut v___y_5380_: *mut leanh::LeanObject,
    mut v___y_5381_: *mut leanh::LeanObject,
    mut v___y_5382_: *mut leanh::LeanObject,
    mut v___y_5383_: *mut leanh::LeanObject,
    mut v___y_5384_: *mut leanh::LeanObject,
    mut v___y_5385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5386_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(v_x_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_);
    leanh::lean_dec(v___y_5380_);
    leanh::lean_dec_ref(v___y_5379_);
    leanh::lean_dec(v___y_5378_);
    leanh::lean_dec_ref(v___y_5377_);
    return v_res_5386_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(
    mut v_mvarId_5387_: *mut leanh::LeanObject,
    mut v_x_5388_: *mut leanh::LeanObject,
    mut v___y_5389_: *mut leanh::LeanObject,
    mut v___y_5390_: *mut leanh::LeanObject,
    mut v___y_5391_: *mut leanh::LeanObject,
    mut v___y_5392_: *mut leanh::LeanObject,
    mut v___y_5393_: *mut leanh::LeanObject,
    mut v___y_5394_: *mut leanh::LeanObject,
    mut v___y_5395_: *mut leanh::LeanObject,
    mut v___y_5396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5403_: u8 = 0;
    let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_5392_);
                leanh::lean_inc_ref(v___y_5391_);
                leanh::lean_inc(v___y_5390_);
                leanh::lean_inc_ref(v___y_5389_);
                v___f_5398_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                leanh::lean_closure_set(v___f_5398_, 0, v_x_5388_);
                leanh::lean_closure_set(v___f_5398_, 1, v___y_5389_);
                leanh::lean_closure_set(v___f_5398_, 2, v___y_5390_);
                leanh::lean_closure_set(v___f_5398_, 3, v___y_5391_);
                leanh::lean_closure_set(v___f_5398_, 4, v___y_5392_);
                v___x_5399_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_5387_,
                    v___f_5398_,
                    v___y_5393_,
                    v___y_5394_,
                    v___y_5395_,
                    v___y_5396_,
                );
                if leanh::lean_obj_tag(v___x_5399_) == 0 {
                    return v___x_5399_;
                } else {
                    v_a_5400_ = leanh::lean_ctor_get(v___x_5399_, 0);
                    v_isSharedCheck_5407_ = (!leanh::lean_is_exclusive(v___x_5399_)) as u8;
                    if v_isSharedCheck_5407_ == 0 {
                        v___x_5402_ = v___x_5399_;
                        v_isShared_5403_ = v_isSharedCheck_5407_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5400_);
                        leanh::lean_dec(v___x_5399_);
                        v___x_5402_ = leanh::lean_box(0);
                        v_isShared_5403_ = v_isSharedCheck_5407_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5403_ == 0 {
                    v___x_5405_ = v___x_5402_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5406_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_a_5400_);
                    v___x_5405_ = v_reuseFailAlloc_5406_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___boxed(
    mut v_mvarId_5408_: *mut leanh::LeanObject,
    mut v_x_5409_: *mut leanh::LeanObject,
    mut v___y_5410_: *mut leanh::LeanObject,
    mut v___y_5411_: *mut leanh::LeanObject,
    mut v___y_5412_: *mut leanh::LeanObject,
    mut v___y_5413_: *mut leanh::LeanObject,
    mut v___y_5414_: *mut leanh::LeanObject,
    mut v___y_5415_: *mut leanh::LeanObject,
    mut v___y_5416_: *mut leanh::LeanObject,
    mut v___y_5417_: *mut leanh::LeanObject,
    mut v___y_5418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5419_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(
            v_mvarId_5408_,
            v_x_5409_,
            v___y_5410_,
            v___y_5411_,
            v___y_5412_,
            v___y_5413_,
            v___y_5414_,
            v___y_5415_,
            v___y_5416_,
            v___y_5417_,
        );
    leanh::lean_dec(v___y_5417_);
    leanh::lean_dec_ref(v___y_5416_);
    leanh::lean_dec(v___y_5415_);
    leanh::lean_dec_ref(v___y_5414_);
    leanh::lean_dec(v___y_5413_);
    leanh::lean_dec_ref(v___y_5412_);
    leanh::lean_dec(v___y_5411_);
    leanh::lean_dec_ref(v___y_5410_);
    return v_res_5419_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(
    mut v_00_u03b1_5420_: *mut leanh::LeanObject,
    mut v_mvarId_5421_: *mut leanh::LeanObject,
    mut v_x_5422_: *mut leanh::LeanObject,
    mut v___y_5423_: *mut leanh::LeanObject,
    mut v___y_5424_: *mut leanh::LeanObject,
    mut v___y_5425_: *mut leanh::LeanObject,
    mut v___y_5426_: *mut leanh::LeanObject,
    mut v___y_5427_: *mut leanh::LeanObject,
    mut v___y_5428_: *mut leanh::LeanObject,
    mut v___y_5429_: *mut leanh::LeanObject,
    mut v___y_5430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5432_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(
            v_mvarId_5421_,
            v_x_5422_,
            v___y_5423_,
            v___y_5424_,
            v___y_5425_,
            v___y_5426_,
            v___y_5427_,
            v___y_5428_,
            v___y_5429_,
            v___y_5430_,
        );
    return v___x_5432_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___boxed(
    mut v_00_u03b1_5433_: *mut leanh::LeanObject,
    mut v_mvarId_5434_: *mut leanh::LeanObject,
    mut v_x_5435_: *mut leanh::LeanObject,
    mut v___y_5436_: *mut leanh::LeanObject,
    mut v___y_5437_: *mut leanh::LeanObject,
    mut v___y_5438_: *mut leanh::LeanObject,
    mut v___y_5439_: *mut leanh::LeanObject,
    mut v___y_5440_: *mut leanh::LeanObject,
    mut v___y_5441_: *mut leanh::LeanObject,
    mut v___y_5442_: *mut leanh::LeanObject,
    mut v___y_5443_: *mut leanh::LeanObject,
    mut v___y_5444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5445_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(
        v_00_u03b1_5433_,
        v_mvarId_5434_,
        v_x_5435_,
        v___y_5436_,
        v___y_5437_,
        v___y_5438_,
        v___y_5439_,
        v___y_5440_,
        v___y_5441_,
        v___y_5442_,
        v___y_5443_,
    );
    leanh::lean_dec(v___y_5443_);
    leanh::lean_dec_ref(v___y_5442_);
    leanh::lean_dec(v___y_5441_);
    leanh::lean_dec_ref(v___y_5440_);
    leanh::lean_dec(v___y_5439_);
    leanh::lean_dec_ref(v___y_5438_);
    leanh::lean_dec(v___y_5437_);
    leanh::lean_dec_ref(v___y_5436_);
    return v_res_5445_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5447_ = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0;
    v___x_5448_ = l_Lean_stringToMessageData(v___x_5447_);
    return v___x_5448_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5450_ = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2;
    v___x_5451_ = l_Lean_stringToMessageData(v___x_5450_);
    return v___x_5451_;
}
pub unsafe fn l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(
    mut v_a_5452_: *mut leanh::LeanObject,
    mut v_x_5453_: *mut leanh::LeanObject,
    mut v_tacName_5454_: *mut leanh::LeanObject,
    mut v_checkNewUnassigned_5455_: u8,
    mut v_mvarCounter_5456_: *mut leanh::LeanObject,
    mut v___y_5457_: *mut leanh::LeanObject,
    mut v___y_5458_: *mut leanh::LeanObject,
    mut v___y_5459_: *mut leanh::LeanObject,
    mut v___y_5460_: *mut leanh::LeanObject,
    mut v___y_5461_: *mut leanh::LeanObject,
    mut v___y_5462_: *mut leanh::LeanObject,
    mut v___y_5463_: *mut leanh::LeanObject,
    mut v___y_5464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5481_: u8 = 0;
    let mut v___x_5482_: u8 = 0;
    let mut v___x_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5494_: u8 = 0;
    let mut v_a_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5498_: u8 = 0;
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5502_: u8 = 0;
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5511_: u8 = 0;
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5515_: u8 = 0;
    let mut v_a_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5519_: u8 = 0;
    let mut v___x_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5523_: u8 = 0;
    let mut v_a_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5527_: u8 = 0;
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5531_: u8 = 0;
    let mut v_a_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5535_: u8 = 0;
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_5452_);
                v___x_5466_ = l_Lean_MVarId_getType(
                    v_a_5452_,
                    v___y_5461_,
                    v___y_5462_,
                    v___y_5463_,
                    v___y_5464_,
                );
                if leanh::lean_obj_tag(v___x_5466_) == 0 {
                    v_a_5467_ = leanh::lean_ctor_get(v___x_5466_, 0);
                    leanh::lean_inc(v_a_5467_);
                    leanh::lean_dec_ref_known(v___x_5466_, 1);
                    leanh::lean_inc(v_a_5452_);
                    v___x_5468_ = l_Lean_MVarId_getTag(
                        v_a_5452_,
                        v___y_5461_,
                        v___y_5462_,
                        v___y_5463_,
                        v___y_5464_,
                    );
                    if leanh::lean_obj_tag(v___x_5468_) == 0 {
                        v_a_5469_ = leanh::lean_ctor_get(v___x_5468_, 0);
                        leanh::lean_inc(v_a_5469_);
                        leanh::lean_dec_ref_known(v___x_5468_, 1);
                        leanh::lean_inc(v___y_5464_);
                        leanh::lean_inc_ref(v___y_5463_);
                        leanh::lean_inc(v___y_5462_);
                        leanh::lean_inc_ref(v___y_5461_);
                        leanh::lean_inc(v___y_5460_);
                        leanh::lean_inc_ref(v___y_5459_);
                        leanh::lean_inc(v___y_5458_);
                        leanh::lean_inc_ref(v___y_5457_);
                        v___x_5470_ = leanh::lean_apply_11(
                            v_x_5453_,
                            v_a_5467_,
                            v_a_5469_,
                            v___y_5457_,
                            v___y_5458_,
                            v___y_5459_,
                            v___y_5460_,
                            v___y_5461_,
                            v___y_5462_,
                            v___y_5463_,
                            v___y_5464_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_5470_) == 0 {
                            v_a_5471_ = leanh::lean_ctor_get(v___x_5470_, 0);
                            leanh::lean_inc(v_a_5471_);
                            leanh::lean_dec_ref_known(v___x_5470_, 1);
                            if v_checkNewUnassigned_5455_ == 0 {
                                leanh::lean_dec(v___y_5460_);
                                leanh::lean_dec_ref(v___y_5459_);
                                leanh::lean_dec(v___y_5458_);
                                leanh::lean_dec_ref(v___y_5457_);
                                v___y_5473_ = v___y_5461_;
                                v___y_5474_ = v___y_5462_;
                                v___y_5475_ = v___y_5463_;
                                v___y_5476_ = v___y_5464_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5471_);
                                v___x_5503_ = l_Lean_Meta_getMVars(
                                    v_a_5471_,
                                    v___y_5461_,
                                    v___y_5462_,
                                    v___y_5463_,
                                    v___y_5464_,
                                );
                                if leanh::lean_obj_tag(v___x_5503_) == 0 {
                                    v_a_5504_ = leanh::lean_ctor_get(v___x_5503_, 0);
                                    leanh::lean_inc(v_a_5504_);
                                    leanh::lean_dec_ref_known(v___x_5503_, 1);
                                    v___x_5505_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(
                                        v_a_5504_,
                                        v_mvarCounter_5456_,
                                        v___y_5462_,
                                    );
                                    leanh::lean_dec(v_a_5504_);
                                    v_a_5506_ = leanh::lean_ctor_get(v___x_5505_, 0);
                                    leanh::lean_inc(v_a_5506_);
                                    leanh::lean_dec_ref(v___x_5505_);
                                    v___x_5507_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(
                                        v_a_5506_,
                                        v___y_5457_,
                                        v___y_5458_,
                                        v___y_5459_,
                                        v___y_5460_,
                                        v___y_5461_,
                                        v___y_5462_,
                                        v___y_5463_,
                                        v___y_5464_,
                                    );
                                    leanh::lean_dec(v___y_5460_);
                                    leanh::lean_dec_ref(v___y_5459_);
                                    leanh::lean_dec(v___y_5458_);
                                    leanh::lean_dec_ref(v___y_5457_);
                                    leanh::lean_dec(v_a_5506_);
                                    if leanh::lean_obj_tag(v___x_5507_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_5507_, 1);
                                        v___y_5473_ = v___y_5461_;
                                        v___y_5474_ = v___y_5462_;
                                        v___y_5475_ = v___y_5463_;
                                        v___y_5476_ = v___y_5464_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_5471_);
                                        leanh::lean_dec(v___y_5464_);
                                        leanh::lean_dec_ref(v___y_5463_);
                                        leanh::lean_dec(v___y_5462_);
                                        leanh::lean_dec_ref(v___y_5461_);
                                        leanh::lean_dec(v_tacName_5454_);
                                        leanh::lean_dec(v_a_5452_);
                                        return v___x_5507_;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_5471_);
                                    leanh::lean_dec(v___y_5464_);
                                    leanh::lean_dec_ref(v___y_5463_);
                                    leanh::lean_dec(v___y_5462_);
                                    leanh::lean_dec_ref(v___y_5461_);
                                    leanh::lean_dec(v___y_5460_);
                                    leanh::lean_dec_ref(v___y_5459_);
                                    leanh::lean_dec(v___y_5458_);
                                    leanh::lean_dec_ref(v___y_5457_);
                                    leanh::lean_dec(v_tacName_5454_);
                                    leanh::lean_dec(v_a_5452_);
                                    v_a_5508_ = leanh::lean_ctor_get(v___x_5503_, 0);
                                    v_isSharedCheck_5515_ =
                                        (!leanh::lean_is_exclusive(v___x_5503_)) as u8;
                                    if v_isSharedCheck_5515_ == 0 {
                                        v___x_5510_ = v___x_5503_;
                                        v_isShared_5511_ = v_isSharedCheck_5515_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5508_);
                                        leanh::lean_dec(v___x_5503_);
                                        v___x_5510_ = leanh::lean_box(0);
                                        v_isShared_5511_ = v_isSharedCheck_5515_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v___y_5464_);
                            leanh::lean_dec_ref(v___y_5463_);
                            leanh::lean_dec(v___y_5462_);
                            leanh::lean_dec_ref(v___y_5461_);
                            leanh::lean_dec(v___y_5460_);
                            leanh::lean_dec_ref(v___y_5459_);
                            leanh::lean_dec(v___y_5458_);
                            leanh::lean_dec_ref(v___y_5457_);
                            leanh::lean_dec(v_tacName_5454_);
                            leanh::lean_dec(v_a_5452_);
                            v_a_5516_ = leanh::lean_ctor_get(v___x_5470_, 0);
                            v_isSharedCheck_5523_ =
                                (!leanh::lean_is_exclusive(v___x_5470_)) as u8;
                            if v_isSharedCheck_5523_ == 0 {
                                v___x_5518_ = v___x_5470_;
                                v_isShared_5519_ = v_isSharedCheck_5523_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5516_);
                                leanh::lean_dec(v___x_5470_);
                                v___x_5518_ = leanh::lean_box(0);
                                v_isShared_5519_ = v_isSharedCheck_5523_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_5467_);
                        leanh::lean_dec(v___y_5464_);
                        leanh::lean_dec_ref(v___y_5463_);
                        leanh::lean_dec(v___y_5462_);
                        leanh::lean_dec_ref(v___y_5461_);
                        leanh::lean_dec(v___y_5460_);
                        leanh::lean_dec_ref(v___y_5459_);
                        leanh::lean_dec(v___y_5458_);
                        leanh::lean_dec_ref(v___y_5457_);
                        leanh::lean_dec(v_tacName_5454_);
                        leanh::lean_dec_ref(v_x_5453_);
                        leanh::lean_dec(v_a_5452_);
                        v_a_5524_ = leanh::lean_ctor_get(v___x_5468_, 0);
                        v_isSharedCheck_5531_ =
                            (!leanh::lean_is_exclusive(v___x_5468_)) as u8;
                        if v_isSharedCheck_5531_ == 0 {
                            v___x_5526_ = v___x_5468_;
                            v_isShared_5527_ = v_isSharedCheck_5531_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5524_);
                            leanh::lean_dec(v___x_5468_);
                            v___x_5526_ = leanh::lean_box(0);
                            v_isShared_5527_ = v_isSharedCheck_5531_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_5464_);
                    leanh::lean_dec_ref(v___y_5463_);
                    leanh::lean_dec(v___y_5462_);
                    leanh::lean_dec_ref(v___y_5461_);
                    leanh::lean_dec(v___y_5460_);
                    leanh::lean_dec_ref(v___y_5459_);
                    leanh::lean_dec(v___y_5458_);
                    leanh::lean_dec_ref(v___y_5457_);
                    leanh::lean_dec(v_tacName_5454_);
                    leanh::lean_dec_ref(v_x_5453_);
                    leanh::lean_dec(v_a_5452_);
                    v_a_5532_ = leanh::lean_ctor_get(v___x_5466_, 0);
                    v_isSharedCheck_5539_ = (!leanh::lean_is_exclusive(v___x_5466_)) as u8;
                    if v_isSharedCheck_5539_ == 0 {
                        v___x_5534_ = v___x_5466_;
                        v_isShared_5535_ = v_isSharedCheck_5539_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5532_);
                        leanh::lean_dec(v___x_5466_);
                        v___x_5534_ = leanh::lean_box(0);
                        v_isShared_5535_ = v_isSharedCheck_5539_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_5476_);
                leanh::lean_inc_ref(v___y_5475_);
                leanh::lean_inc(v___y_5474_);
                leanh::lean_inc_ref(v___y_5473_);
                leanh::lean_inc(v_a_5471_);
                leanh::lean_inc(v_a_5452_);
                v___x_5477_ = lean_checked_assign(
                    v_a_5452_,
                    v_a_5471_,
                    v___y_5473_,
                    v___y_5474_,
                    v___y_5475_,
                    v___y_5476_,
                );
                if leanh::lean_obj_tag(v___x_5477_) == 0 {
                    v_a_5478_ = leanh::lean_ctor_get(v___x_5477_, 0);
                    v_isSharedCheck_5494_ = (!leanh::lean_is_exclusive(v___x_5477_)) as u8;
                    if v_isSharedCheck_5494_ == 0 {
                        v___x_5480_ = v___x_5477_;
                        v_isShared_5481_ = v_isSharedCheck_5494_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5478_);
                        leanh::lean_dec(v___x_5477_);
                        v___x_5480_ = leanh::lean_box(0);
                        v_isShared_5481_ = v_isSharedCheck_5494_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_5476_);
                    leanh::lean_dec_ref(v___y_5475_);
                    leanh::lean_dec(v___y_5474_);
                    leanh::lean_dec_ref(v___y_5473_);
                    leanh::lean_dec(v_a_5471_);
                    leanh::lean_dec(v_tacName_5454_);
                    leanh::lean_dec(v_a_5452_);
                    v_a_5495_ = leanh::lean_ctor_get(v___x_5477_, 0);
                    v_isSharedCheck_5502_ = (!leanh::lean_is_exclusive(v___x_5477_)) as u8;
                    if v_isSharedCheck_5502_ == 0 {
                        v___x_5497_ = v___x_5477_;
                        v_isShared_5498_ = v_isSharedCheck_5502_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5495_);
                        leanh::lean_dec(v___x_5477_);
                        v___x_5497_ = leanh::lean_box(0);
                        v_isShared_5498_ = v_isSharedCheck_5502_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5482_ = (leanh::lean_unbox(v_a_5478_) as u8);
                leanh::lean_dec(v_a_5478_);
                if v___x_5482_ == 0 {
                    leanh::lean_del_object(v___x_5480_);
                    v___x_5483_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1,
                    );
                    v___x_5484_ = l_Lean_indentExpr(v_a_5471_);
                    v___x_5485_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5485_, 0, v___x_5483_);
                    leanh::lean_ctor_set(v___x_5485_, 1, v___x_5484_);
                    v___x_5486_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3,
                    );
                    v___x_5487_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5487_, 0, v___x_5485_);
                    leanh::lean_ctor_set(v___x_5487_, 1, v___x_5486_);
                    v___x_5488_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5488_, 0, v___x_5487_);
                    v___x_5489_ = l_Lean_Meta_throwTacticEx___redArg(
                        v_tacName_5454_,
                        v_a_5452_,
                        v___x_5488_,
                        v___y_5473_,
                        v___y_5474_,
                        v___y_5475_,
                        v___y_5476_,
                    );
                    leanh::lean_dec(v___y_5476_);
                    leanh::lean_dec_ref(v___y_5475_);
                    leanh::lean_dec(v___y_5474_);
                    leanh::lean_dec_ref(v___y_5473_);
                    return v___x_5489_;
                } else {
                    leanh::lean_dec(v___y_5476_);
                    leanh::lean_dec_ref(v___y_5475_);
                    leanh::lean_dec(v___y_5474_);
                    leanh::lean_dec_ref(v___y_5473_);
                    leanh::lean_dec(v_a_5471_);
                    leanh::lean_dec(v_tacName_5454_);
                    leanh::lean_dec(v_a_5452_);
                    v___x_5490_ = leanh::lean_box(0);
                    if v_isShared_5481_ == 0 {
                        leanh::lean_ctor_set(v___x_5480_, 0, v___x_5490_);
                        v___x_5492_ = v___x_5480_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5493_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5490_);
                        v___x_5492_ = v_reuseFailAlloc_5493_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5492_;
            }
            4 => {
                if v_isShared_5498_ == 0 {
                    v___x_5500_ = v___x_5497_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5501_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5495_);
                    v___x_5500_ = v_reuseFailAlloc_5501_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5500_;
            }
            6 => {
                if v_isShared_5511_ == 0 {
                    v___x_5513_ = v___x_5510_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5514_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_a_5508_);
                    v___x_5513_ = v_reuseFailAlloc_5514_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5513_;
            }
            8 => {
                if v_isShared_5519_ == 0 {
                    v___x_5521_ = v___x_5518_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5522_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_a_5516_);
                    v___x_5521_ = v_reuseFailAlloc_5522_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5521_;
            }
            10 => {
                if v_isShared_5527_ == 0 {
                    v___x_5529_ = v___x_5526_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5530_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5524_);
                    v___x_5529_ = v_reuseFailAlloc_5530_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5529_;
            }
            12 => {
                if v_isShared_5535_ == 0 {
                    v___x_5537_ = v___x_5534_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5538_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
                    v___x_5537_ = v_reuseFailAlloc_5538_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5537_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed(
    mut v_a_5540_: *mut leanh::LeanObject,
    mut v_x_5541_: *mut leanh::LeanObject,
    mut v_tacName_5542_: *mut leanh::LeanObject,
    mut v_checkNewUnassigned_5543_: *mut leanh::LeanObject,
    mut v_mvarCounter_5544_: *mut leanh::LeanObject,
    mut v___y_5545_: *mut leanh::LeanObject,
    mut v___y_5546_: *mut leanh::LeanObject,
    mut v___y_5547_: *mut leanh::LeanObject,
    mut v___y_5548_: *mut leanh::LeanObject,
    mut v___y_5549_: *mut leanh::LeanObject,
    mut v___y_5550_: *mut leanh::LeanObject,
    mut v___y_5551_: *mut leanh::LeanObject,
    mut v___y_5552_: *mut leanh::LeanObject,
    mut v___y_5553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkNewUnassigned_boxed_5554_: u8 = 0;
    let mut v_res_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkNewUnassigned_boxed_5554_ = (leanh::lean_unbox(v_checkNewUnassigned_5543_) as u8);
    v_res_5555_ = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(
        v_a_5540_,
        v_x_5541_,
        v_tacName_5542_,
        v_checkNewUnassigned_boxed_5554_,
        v_mvarCounter_5544_,
        v___y_5545_,
        v___y_5546_,
        v___y_5547_,
        v___y_5548_,
        v___y_5549_,
        v___y_5550_,
        v___y_5551_,
        v___y_5552_,
    );
    leanh::lean_dec(v_mvarCounter_5544_);
    return v_res_5555_;
}
pub unsafe fn l_Lean_Elab_Tactic_closeMainGoalUsing(
    mut v_tacName_5556_: *mut leanh::LeanObject,
    mut v_x_5557_: *mut leanh::LeanObject,
    mut v_checkNewUnassigned_5558_: u8,
    mut v_a_5559_: *mut leanh::LeanObject,
    mut v_a_5560_: *mut leanh::LeanObject,
    mut v_a_5561_: *mut leanh::LeanObject,
    mut v_a_5562_: *mut leanh::LeanObject,
    mut v_a_5563_: *mut leanh::LeanObject,
    mut v_a_5564_: *mut leanh::LeanObject,
    mut v_a_5565_: *mut leanh::LeanObject,
    mut v_a_5566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5578_: u8 = 0;
    let mut v___x_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5582_: u8 = 0;
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5586_: u8 = 0;
    let mut v_unused_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: u8 = 0;
    let mut v___x_5589_: u8 = 0;
    let mut v_a_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5593_: u8 = 0;
    let mut v___x_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5568_ = lean_st_ref_get(v_a_5564_);
                v___x_5569_ = l_Lean_Elab_Tactic_popMainGoal___redArg(
                    v_a_5560_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_,
                );
                if leanh::lean_obj_tag(v___x_5569_) == 0 {
                    v_mctx_5570_ = leanh::lean_ctor_get(v___x_5568_, 0);
                    leanh::lean_inc_ref(v_mctx_5570_);
                    leanh::lean_dec(v___x_5568_);
                    v_a_5571_ = leanh::lean_ctor_get(v___x_5569_, 0);
                    leanh::lean_inc_n(v_a_5571_, 3);
                    leanh::lean_dec_ref_known(v___x_5569_, 1);
                    v_mvarCounter_5572_ = leanh::lean_ctor_get(v_mctx_5570_, 3);
                    leanh::lean_inc(v_mvarCounter_5572_);
                    leanh::lean_dec_ref(v_mctx_5570_);
                    v___x_5573_ = leanh::lean_box((v_checkNewUnassigned_5558_) as usize);
                    v___f_5574_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed
                            as *mut core::ffi::c_void,
                        14,
                        5,
                    );
                    leanh::lean_closure_set(v___f_5574_, 0, v_a_5571_);
                    leanh::lean_closure_set(v___f_5574_, 1, v_x_5557_);
                    leanh::lean_closure_set(v___f_5574_, 2, v_tacName_5556_);
                    leanh::lean_closure_set(v___f_5574_, 3, v___x_5573_);
                    leanh::lean_closure_set(v___f_5574_, 4, v_mvarCounter_5572_);
                    v___x_5575_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_a_5571_, v___f_5574_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_);
                    if leanh::lean_obj_tag(v___x_5575_) == 0 {
                        leanh::lean_dec(v_a_5571_);
                        return v___x_5575_;
                    } else {
                        v_a_5576_ = leanh::lean_ctor_get(v___x_5575_, 0);
                        leanh::lean_inc(v_a_5576_);
                        v___x_5588_ = l_Lean_Exception_isInterrupt(v_a_5576_);
                        if v___x_5588_ == 0 {
                            leanh::lean_inc(v_a_5576_);
                            v___x_5589_ = l_Lean_Exception_isRuntime(v_a_5576_);
                            v___y_5578_ = v___x_5589_;
                            state = 1;
                            continue;
                        } else {
                            v___y_5578_ = v___x_5588_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_5568_);
                    leanh::lean_dec_ref(v_x_5557_);
                    leanh::lean_dec(v_tacName_5556_);
                    v_a_5590_ = leanh::lean_ctor_get(v___x_5569_, 0);
                    v_isSharedCheck_5597_ = (!leanh::lean_is_exclusive(v___x_5569_)) as u8;
                    if v_isSharedCheck_5597_ == 0 {
                        v___x_5592_ = v___x_5569_;
                        v_isShared_5593_ = v_isSharedCheck_5597_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5590_);
                        leanh::lean_dec(v___x_5569_);
                        v___x_5592_ = leanh::lean_box(0);
                        v_isShared_5593_ = v_isSharedCheck_5597_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5578_ == 0 {
                    leanh::lean_dec_ref_known(v___x_5575_, 1);
                    v___x_5579_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_5571_, v_a_5560_);
                    if leanh::lean_obj_tag(v___x_5579_) == 0 {
                        v_isSharedCheck_5586_ =
                            (!leanh::lean_is_exclusive(v___x_5579_)) as u8;
                        if v_isSharedCheck_5586_ == 0 {
                            v_unused_5587_ = leanh::lean_ctor_get(v___x_5579_, 0);
                            leanh::lean_dec(v_unused_5587_);
                            v___x_5581_ = v___x_5579_;
                            v_isShared_5582_ = v_isSharedCheck_5586_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5579_);
                            v___x_5581_ = leanh::lean_box(0);
                            v_isShared_5582_ = v_isSharedCheck_5586_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_5576_);
                        return v___x_5579_;
                    }
                } else {
                    leanh::lean_dec(v_a_5576_);
                    leanh::lean_dec(v_a_5571_);
                    return v___x_5575_;
                }
            }
            2 => {
                if v_isShared_5582_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5581_, 1);
                    leanh::lean_ctor_set(v___x_5581_, 0, v_a_5576_);
                    v___x_5584_ = v___x_5581_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5576_);
                    v___x_5584_ = v_reuseFailAlloc_5585_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5584_;
            }
            4 => {
                if v_isShared_5593_ == 0 {
                    v___x_5595_ = v___x_5592_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5596_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_a_5590_);
                    v___x_5595_ = v_reuseFailAlloc_5596_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_closeMainGoalUsing___boxed(
    mut v_tacName_5598_: *mut leanh::LeanObject,
    mut v_x_5599_: *mut leanh::LeanObject,
    mut v_checkNewUnassigned_5600_: *mut leanh::LeanObject,
    mut v_a_5601_: *mut leanh::LeanObject,
    mut v_a_5602_: *mut leanh::LeanObject,
    mut v_a_5603_: *mut leanh::LeanObject,
    mut v_a_5604_: *mut leanh::LeanObject,
    mut v_a_5605_: *mut leanh::LeanObject,
    mut v_a_5606_: *mut leanh::LeanObject,
    mut v_a_5607_: *mut leanh::LeanObject,
    mut v_a_5608_: *mut leanh::LeanObject,
    mut v_a_5609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkNewUnassigned_boxed_5610_: u8 = 0;
    let mut v_res_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkNewUnassigned_boxed_5610_ = (leanh::lean_unbox(v_checkNewUnassigned_5600_) as u8);
    v_res_5611_ = l_Lean_Elab_Tactic_closeMainGoalUsing(
        v_tacName_5598_,
        v_x_5599_,
        v_checkNewUnassigned_boxed_5610_,
        v_a_5601_,
        v_a_5602_,
        v_a_5603_,
        v_a_5604_,
        v_a_5605_,
        v_a_5606_,
        v_a_5607_,
        v_a_5608_,
    );
    leanh::lean_dec(v_a_5608_);
    leanh::lean_dec_ref(v_a_5607_);
    leanh::lean_dec(v_a_5606_);
    leanh::lean_dec_ref(v_a_5605_);
    leanh::lean_dec(v_a_5604_);
    leanh::lean_dec_ref(v_a_5603_);
    leanh::lean_dec(v_a_5602_);
    leanh::lean_dec_ref(v_a_5601_);
    return v_res_5611_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5612_ = leanh::lean_box(0);
    v___x_5613_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_5614_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5614_, 0, v___x_5613_);
    leanh::lean_ctor_set(v___x_5614_, 1, v___x_5612_);
    return v___x_5614_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5616_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0);
    v___x_5617_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5617_, 0, v___x_5616_);
    return v___x_5617_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___boxed(
    mut v___y_5618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5619_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
    return v_res_5619_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(
    mut v_00_u03b1_5620_: *mut leanh::LeanObject,
    mut v___y_5621_: *mut leanh::LeanObject,
    mut v___y_5622_: *mut leanh::LeanObject,
    mut v___y_5623_: *mut leanh::LeanObject,
    mut v___y_5624_: *mut leanh::LeanObject,
    mut v___y_5625_: *mut leanh::LeanObject,
    mut v___y_5626_: *mut leanh::LeanObject,
    mut v___y_5627_: *mut leanh::LeanObject,
    mut v___y_5628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5630_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
    return v___x_5630_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___boxed(
    mut v_00_u03b1_5631_: *mut leanh::LeanObject,
    mut v___y_5632_: *mut leanh::LeanObject,
    mut v___y_5633_: *mut leanh::LeanObject,
    mut v___y_5634_: *mut leanh::LeanObject,
    mut v___y_5635_: *mut leanh::LeanObject,
    mut v___y_5636_: *mut leanh::LeanObject,
    mut v___y_5637_: *mut leanh::LeanObject,
    mut v___y_5638_: *mut leanh::LeanObject,
    mut v___y_5639_: *mut leanh::LeanObject,
    mut v___y_5640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5641_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(
        v_00_u03b1_5631_,
        v___y_5632_,
        v___y_5633_,
        v___y_5634_,
        v___y_5635_,
        v___y_5636_,
        v___y_5637_,
        v___y_5638_,
        v___y_5639_,
    );
    leanh::lean_dec(v___y_5639_);
    leanh::lean_dec_ref(v___y_5638_);
    leanh::lean_dec(v___y_5637_);
    leanh::lean_dec_ref(v___y_5636_);
    leanh::lean_dec(v___y_5635_);
    leanh::lean_dec_ref(v___y_5634_);
    leanh::lean_dec(v___y_5633_);
    leanh::lean_dec_ref(v___y_5632_);
    return v_res_5641_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExact___lam__0(
    mut v___x_5642_: *mut leanh::LeanObject,
    mut v_type_5643_: *mut leanh::LeanObject,
    mut v_x_5644_: *mut leanh::LeanObject,
    mut v___y_5645_: *mut leanh::LeanObject,
    mut v___y_5646_: *mut leanh::LeanObject,
    mut v___y_5647_: *mut leanh::LeanObject,
    mut v___y_5648_: *mut leanh::LeanObject,
    mut v___y_5649_: *mut leanh::LeanObject,
    mut v___y_5650_: *mut leanh::LeanObject,
    mut v___y_5651_: *mut leanh::LeanObject,
    mut v___y_5652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: u8 = 0;
    let mut v___x_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5654_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5654_, 0, v_type_5643_);
    v___x_5655_ = 0;
    v___x_5656_ = l_Lean_Elab_Tactic_elabTermEnsuringType(
        v___x_5642_,
        v___x_5654_,
        v___x_5655_,
        v___y_5645_,
        v___y_5646_,
        v___y_5647_,
        v___y_5648_,
        v___y_5649_,
        v___y_5650_,
        v___y_5651_,
        v___y_5652_,
    );
    return v___x_5656_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExact___lam__0___boxed(
    mut v___x_5657_: *mut leanh::LeanObject,
    mut v_type_5658_: *mut leanh::LeanObject,
    mut v_x_5659_: *mut leanh::LeanObject,
    mut v___y_5660_: *mut leanh::LeanObject,
    mut v___y_5661_: *mut leanh::LeanObject,
    mut v___y_5662_: *mut leanh::LeanObject,
    mut v___y_5663_: *mut leanh::LeanObject,
    mut v___y_5664_: *mut leanh::LeanObject,
    mut v___y_5665_: *mut leanh::LeanObject,
    mut v___y_5666_: *mut leanh::LeanObject,
    mut v___y_5667_: *mut leanh::LeanObject,
    mut v___y_5668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5669_ = l_Lean_Elab_Tactic_evalExact___lam__0(
        v___x_5657_,
        v_type_5658_,
        v_x_5659_,
        v___y_5660_,
        v___y_5661_,
        v___y_5662_,
        v___y_5663_,
        v___y_5664_,
        v___y_5665_,
        v___y_5666_,
        v___y_5667_,
    );
    leanh::lean_dec(v___y_5667_);
    leanh::lean_dec_ref(v___y_5666_);
    leanh::lean_dec(v___y_5665_);
    leanh::lean_dec_ref(v___y_5664_);
    leanh::lean_dec(v___y_5663_);
    leanh::lean_dec_ref(v___y_5662_);
    leanh::lean_dec(v___y_5661_);
    leanh::lean_dec_ref(v___y_5660_);
    leanh::lean_dec(v_x_5659_);
    return v_res_5669_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalExact(
    mut v_stx_5681_: *mut leanh::LeanObject,
    mut v_a_5682_: *mut leanh::LeanObject,
    mut v_a_5683_: *mut leanh::LeanObject,
    mut v_a_5684_: *mut leanh::LeanObject,
    mut v_a_5685_: *mut leanh::LeanObject,
    mut v_a_5686_: *mut leanh::LeanObject,
    mut v_a_5687_: *mut leanh::LeanObject,
    mut v_a_5688_: *mut leanh::LeanObject,
    mut v_a_5689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: u8 = 0;
    v___x_5691_ = l_Lean_Elab_Tactic_evalExact___closed__4;
    leanh::lean_inc(v_stx_5681_);
    v___x_5692_ = l_Lean_Syntax_isOfKind(v_stx_5681_, v___x_5691_);
    if v___x_5692_ == 0 {
        let mut v___x_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_5681_);
        v___x_5693_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg(
            );
        return v___x_5693_;
    } else {
        let mut v___x_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5694_ = leanh::lean_unsigned_to_nat(1);
        v___x_5695_ = l_Lean_Syntax_getArg(v_stx_5681_, v___x_5694_);
        leanh::lean_dec(v_stx_5681_);
        v___f_5696_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_evalExact___lam__0___boxed as *mut core::ffi::c_void,
            12,
            1,
        );
        leanh::lean_closure_set(v___f_5696_, 0, v___x_5695_);
        v___x_5697_ = l_Lean_Elab_Tactic_evalExact___closed__5;
        v___x_5698_ = l_Lean_Elab_Tactic_closeMainGoalUsing(
            v___x_5697_,
            v___f_5696_,
            v___x_5692_,
            v_a_5682_,
            v_a_5683_,
            v_a_5684_,
            v_a_5685_,
            v_a_5686_,
            v_a_5687_,
            v_a_5688_,
            v_a_5689_,
        );
        return v___x_5698_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalExact___boxed(
    mut v_stx_5699_: *mut leanh::LeanObject,
    mut v_a_5700_: *mut leanh::LeanObject,
    mut v_a_5701_: *mut leanh::LeanObject,
    mut v_a_5702_: *mut leanh::LeanObject,
    mut v_a_5703_: *mut leanh::LeanObject,
    mut v_a_5704_: *mut leanh::LeanObject,
    mut v_a_5705_: *mut leanh::LeanObject,
    mut v_a_5706_: *mut leanh::LeanObject,
    mut v_a_5707_: *mut leanh::LeanObject,
    mut v_a_5708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5709_ = l_Lean_Elab_Tactic_evalExact(
        v_stx_5699_,
        v_a_5700_,
        v_a_5701_,
        v_a_5702_,
        v_a_5703_,
        v_a_5704_,
        v_a_5705_,
        v_a_5706_,
        v_a_5707_,
    );
    leanh::lean_dec(v_a_5707_);
    leanh::lean_dec_ref(v_a_5706_);
    leanh::lean_dec(v_a_5705_);
    leanh::lean_dec_ref(v_a_5704_);
    leanh::lean_dec(v_a_5703_);
    leanh::lean_dec_ref(v_a_5702_);
    leanh::lean_dec(v_a_5701_);
    leanh::lean_dec_ref(v_a_5700_);
    return v_res_5709_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1()
-> *mut leanh::LeanObject {
    let mut v___x_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5717_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_5718_ = l_Lean_Elab_Tactic_evalExact___closed__4;
    v___x_5719_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
    v___x_5720_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalExact___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5721_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5717_,
        v___x_5718_,
        v___x_5719_,
        v___x_5720_,
    );
    return v___x_5721_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___boxed(
    mut v_a_5722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5723_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1();
    return v_res_5723_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5750_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
    v___x_5751_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6;
    v___x_5752_ = l_Lean_addBuiltinDeclarationRanges(v___x_5750_, v___x_5751_);
    return v___x_5752_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___boxed(
    mut v_a_5753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5754_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3();
    return v_res_5754_;
}
pub unsafe fn l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(
    mut v_mctx_5755_: *mut leanh::LeanObject,
    mut v_mvarId_u2081_5756_: *mut leanh::LeanObject,
    mut v_mvarId_u2082_5757_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_decl_u2081_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_u2082_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: u8 = 0;
    leanh::lean_inc(v_mvarId_u2081_5756_);
    v_decl_u2081_5758_ = l_Lean_MetavarContext_getDecl(v_mctx_5755_, v_mvarId_u2081_5756_);
    v_index_5759_ = leanh::lean_ctor_get(v_decl_u2081_5758_, 6);
    leanh::lean_inc(v_index_5759_);
    leanh::lean_dec_ref(v_decl_u2081_5758_);
    leanh::lean_inc(v_mvarId_u2082_5757_);
    v_decl_u2082_5760_ = l_Lean_MetavarContext_getDecl(v_mctx_5755_, v_mvarId_u2082_5757_);
    v_index_5761_ = leanh::lean_ctor_get(v_decl_u2082_5760_, 6);
    leanh::lean_inc(v_index_5761_);
    leanh::lean_dec_ref(v_decl_u2082_5760_);
    v___x_5762_ = lean_nat_dec_eq(v_index_5759_, v_index_5761_);
    if v___x_5762_ == 0 {
        let mut v___x_5763_: u8 = 0;
        leanh::lean_dec(v_mvarId_u2082_5757_);
        leanh::lean_dec(v_mvarId_u2081_5756_);
        v___x_5763_ = lean_nat_dec_lt(v_index_5759_, v_index_5761_);
        leanh::lean_dec(v_index_5761_);
        leanh::lean_dec(v_index_5759_);
        return v___x_5763_;
    } else {
        let mut v___x_5764_: u8 = 0;
        leanh::lean_dec(v_index_5761_);
        leanh::lean_dec(v_index_5759_);
        v___x_5764_ = l_Lean_Name_quickLt(v_mvarId_u2081_5756_, v_mvarId_u2082_5757_);
        leanh::lean_dec(v_mvarId_u2082_5757_);
        leanh::lean_dec(v_mvarId_u2081_5756_);
        return v___x_5764_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed(
    mut v_mctx_5765_: *mut leanh::LeanObject,
    mut v_mvarId_u2081_5766_: *mut leanh::LeanObject,
    mut v_mvarId_u2082_5767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5768_: u8 = 0;
    let mut v_r_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5768_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(
        v_mctx_5765_,
        v_mvarId_u2081_5766_,
        v_mvarId_u2082_5767_,
    );
    leanh::lean_dec_ref(v_mctx_5765_);
    v_r_5769_ = leanh::lean_box((v_res_5768_) as usize);
    return v_r_5769_;
}
pub unsafe fn l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1(
    mut v_mvarIds_5770_: *mut leanh::LeanObject,
    mut v_toPure_5771_: *mut leanh::LeanObject,
    mut v_mctx_5772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: u8 = 0;
    let mut v___f_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: u8 = 0;
    let mut v___x_5787_: u8 = 0;
    let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5773_ = lean_array_get_size(v_mvarIds_5770_);
                v___x_5774_ = leanh::lean_unsigned_to_nat(0);
                v___x_5775_ = lean_nat_dec_eq(v___x_5773_, v___x_5774_);
                if v___x_5775_ == 0 {
                    v___f_5776_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    leanh::lean_closure_set(v___f_5776_, 0, v_mctx_5772_);
                    v___x_5782_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5783_ = lean_nat_sub(v___x_5773_, v___x_5782_);
                    v___x_5787_ = lean_nat_dec_le(v___x_5774_, v___x_5783_);
                    if v___x_5787_ == 0 {
                        leanh::lean_inc(v___x_5783_);
                        v___y_5785_ = v___x_5783_;
                        state = 2;
                        continue;
                    } else {
                        v___y_5785_ = v___x_5774_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_mctx_5772_);
                    v___x_5788_ = leanh::lean_apply_2(
                        v_toPure_5771_,
                        leanh::lean_box(0),
                        v_mvarIds_5770_,
                    );
                    return v___x_5788_;
                }
            }
            1 => {
                v___x_5780_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    leanh::lean_box(0),
                    v___f_5776_,
                    v___x_5773_,
                    v_mvarIds_5770_,
                    v___y_5778_,
                    v___y_5779_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                leanh::lean_dec(v___y_5779_);
                v___x_5781_ = leanh::lean_apply_2(
                    v_toPure_5771_,
                    leanh::lean_box(0),
                    v___x_5780_,
                );
                return v___x_5781_;
            }
            2 => {
                v___x_5786_ = lean_nat_dec_le(v___y_5785_, v___x_5783_);
                if v___x_5786_ == 0 {
                    leanh::lean_dec(v___x_5783_);
                    leanh::lean_inc(v___y_5785_);
                    v___y_5778_ = v___y_5785_;
                    v___y_5779_ = v___y_5785_;
                    state = 1;
                    continue;
                } else {
                    v___y_5778_ = v___y_5785_;
                    v___y_5779_ = v___x_5783_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(
    mut v_inst_5789_: *mut leanh::LeanObject,
    mut v_inst_5790_: *mut leanh::LeanObject,
    mut v_mvarIds_5791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getMCtx_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5792_ = leanh::lean_ctor_get(v_inst_5790_, 0);
    leanh::lean_inc_ref(v_toApplicative_5792_);
    v_toBind_5793_ = leanh::lean_ctor_get(v_inst_5790_, 1);
    leanh::lean_inc(v_toBind_5793_);
    leanh::lean_dec_ref(v_inst_5790_);
    v_getMCtx_5794_ = leanh::lean_ctor_get(v_inst_5789_, 0);
    leanh::lean_inc(v_getMCtx_5794_);
    leanh::lean_dec_ref(v_inst_5789_);
    v_toPure_5795_ = leanh::lean_ctor_get(v_toApplicative_5792_, 1);
    leanh::lean_inc(v_toPure_5795_);
    leanh::lean_dec_ref(v_toApplicative_5792_);
    v___f_5796_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5796_, 0, v_mvarIds_5791_);
    leanh::lean_closure_set(v___f_5796_, 1, v_toPure_5795_);
    v___x_5797_ = leanh::lean_apply_4(
        v_toBind_5793_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getMCtx_5794_,
        v___f_5796_,
    );
    return v___x_5797_;
}
pub unsafe fn l_Lean_Elab_Tactic_sortMVarIdArrayByIndex(
    mut v_m_5798_: *mut leanh::LeanObject,
    mut v_inst_5799_: *mut leanh::LeanObject,
    mut v_inst_5800_: *mut leanh::LeanObject,
    mut v_mvarIds_5801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5802_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(
        v_inst_5799_,
        v_inst_5800_,
        v_mvarIds_5801_,
    );
    return v___x_5802_;
}
pub unsafe fn l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg(
    mut v_inst_5803_: *mut leanh::LeanObject,
    mut v_inst_5804_: *mut leanh::LeanObject,
    mut v_mvarIds_5805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5806_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(
        v_inst_5803_,
        v_inst_5804_,
        v_mvarIds_5805_,
    );
    return v___x_5806_;
}
pub unsafe fn l_Lean_Elab_Tactic_sortMVarIdsByIndex(
    mut v_m_5807_: *mut leanh::LeanObject,
    mut v_inst_5808_: *mut leanh::LeanObject,
    mut v_inst_5809_: *mut leanh::LeanObject,
    mut v_mvarIds_5810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5811_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(
        v_inst_5808_,
        v_inst_5809_,
        v_mvarIds_5810_,
    );
    return v___x_5811_;
}
pub unsafe fn l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(
    mut v___y_5812_: *mut leanh::LeanObject,
    mut v___y_5813_: *mut leanh::LeanObject,
    mut v___y_5814_: *mut leanh::LeanObject,
    mut v___y_5815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5817_ = lean_st_ref_get(v___y_5813_);
    v_mctx_5818_ = leanh::lean_ctor_get(v___x_5817_, 0);
    leanh::lean_inc_ref(v_mctx_5818_);
    leanh::lean_dec(v___x_5817_);
    v___x_5819_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5819_, 0, v_mctx_5818_);
    return v___x_5819_;
}
pub unsafe fn l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0___boxed(
    mut v___y_5820_: *mut leanh::LeanObject,
    mut v___y_5821_: *mut leanh::LeanObject,
    mut v___y_5822_: *mut leanh::LeanObject,
    mut v___y_5823_: *mut leanh::LeanObject,
    mut v___y_5824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5825_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(
        v___y_5820_,
        v___y_5821_,
        v___y_5822_,
        v___y_5823_,
    );
    leanh::lean_dec(v___y_5823_);
    leanh::lean_dec_ref(v___y_5822_);
    leanh::lean_dec(v___y_5821_);
    leanh::lean_dec_ref(v___y_5820_);
    return v_res_5825_;
}
pub unsafe fn l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1(
    mut v_val_5826_: *mut leanh::LeanObject,
    mut v_toPure_5827_: *mut leanh::LeanObject,
    mut v_newMVarIds_5828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5829_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5829_, 0, v_val_5826_);
    leanh::lean_ctor_set(v___x_5829_, 1, v_newMVarIds_5828_);
    v___x_5830_ =
        leanh::lean_apply_2(v_toPure_5827_, leanh::lean_box(0), v___x_5829_);
    return v___x_5830_;
}
pub unsafe fn l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2(
    mut v___x_5831_: *mut leanh::LeanObject,
    mut v___x_5832_: *mut leanh::LeanObject,
    mut v_inst_5833_: *mut leanh::LeanObject,
    mut v_toBind_5834_: *mut leanh::LeanObject,
    mut v___f_5835_: *mut leanh::LeanObject,
    mut v_newMVarIds_5836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5837_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(
        v___x_5831_,
        v___x_5832_,
        v_newMVarIds_5836_,
    );
    v___x_5838_ = leanh::lean_apply_2(v_inst_5833_, leanh::lean_box(0), v___x_5837_);
    v___x_5839_ = leanh::lean_apply_4(
        v_toBind_5834_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5838_,
        v___f_5835_,
    );
    return v___x_5839_;
}
pub unsafe fn l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3(
    mut v_mvarCounter_5840_: *mut leanh::LeanObject,
    mut v_inst_5841_: *mut leanh::LeanObject,
    mut v_toBind_5842_: *mut leanh::LeanObject,
    mut v___f_5843_: *mut leanh::LeanObject,
    mut v_newMVarIds_5844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5845_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_filterOldMVars___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5845_, 0, v_newMVarIds_5844_);
    leanh::lean_closure_set(v___x_5845_, 1, v_mvarCounter_5840_);
    v___x_5846_ = leanh::lean_apply_2(v_inst_5841_, leanh::lean_box(0), v___x_5845_);
    v___x_5847_ = leanh::lean_apply_4(
        v_toBind_5842_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5846_,
        v___f_5843_,
    );
    return v___x_5847_;
}
pub unsafe fn l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4(
    mut v_toPure_5848_: *mut leanh::LeanObject,
    mut v___x_5849_: *mut leanh::LeanObject,
    mut v___x_5850_: *mut leanh::LeanObject,
    mut v_inst_5851_: *mut leanh::LeanObject,
    mut v_toBind_5852_: *mut leanh::LeanObject,
    mut v_mvarCounter_5853_: *mut leanh::LeanObject,
    mut v_val_5854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_val_5854_);
    v___f_5855_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5855_, 0, v_val_5854_);
    leanh::lean_closure_set(v___f_5855_, 1, v_toPure_5848_);
    leanh::lean_inc_n(v_toBind_5852_, 2);
    leanh::lean_inc_n(v_inst_5851_, 2);
    v___f_5856_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_5856_, 0, v___x_5849_);
    leanh::lean_closure_set(v___f_5856_, 1, v___x_5850_);
    leanh::lean_closure_set(v___f_5856_, 2, v_inst_5851_);
    leanh::lean_closure_set(v___f_5856_, 3, v_toBind_5852_);
    leanh::lean_closure_set(v___f_5856_, 4, v___f_5855_);
    v___f_5857_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_5857_, 0, v_mvarCounter_5853_);
    leanh::lean_closure_set(v___f_5857_, 1, v_inst_5851_);
    leanh::lean_closure_set(v___f_5857_, 2, v_toBind_5852_);
    leanh::lean_closure_set(v___f_5857_, 3, v___f_5856_);
    v___x_5858_ = leanh::lean_alloc_closure(
        l_Lean_Meta_getMVarsNoDelayed___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_5858_, 0, v_val_5854_);
    v___x_5859_ = leanh::lean_apply_2(v_inst_5851_, leanh::lean_box(0), v___x_5858_);
    v___x_5860_ = leanh::lean_apply_4(
        v_toBind_5852_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5859_,
        v___f_5857_,
    );
    return v___x_5860_;
}
pub unsafe fn l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5(
    mut v_toPure_5861_: *mut leanh::LeanObject,
    mut v___x_5862_: *mut leanh::LeanObject,
    mut v___x_5863_: *mut leanh::LeanObject,
    mut v_inst_5864_: *mut leanh::LeanObject,
    mut v_toBind_5865_: *mut leanh::LeanObject,
    mut v_k_5866_: *mut leanh::LeanObject,
    mut v_____do__lift_5867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mvarCounter_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mvarCounter_5868_ = leanh::lean_ctor_get(v_____do__lift_5867_, 3);
    leanh::lean_inc(v_mvarCounter_5868_);
    leanh::lean_dec_ref(v_____do__lift_5867_);
    leanh::lean_inc(v_toBind_5865_);
    v___f_5869_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_5869_, 0, v_toPure_5861_);
    leanh::lean_closure_set(v___f_5869_, 1, v___x_5862_);
    leanh::lean_closure_set(v___f_5869_, 2, v___x_5863_);
    leanh::lean_closure_set(v___f_5869_, 3, v_inst_5864_);
    leanh::lean_closure_set(v___f_5869_, 4, v_toBind_5865_);
    leanh::lean_closure_set(v___f_5869_, 5, v_mvarCounter_5868_);
    v___x_5870_ = leanh::lean_apply_4(
        v_toBind_5865_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_k_5866_,
        v___f_5869_,
    );
    return v___x_5870_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5871_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_5871_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5872_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0_once),
        _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0,
    );
    v___x_5873_ = l_StateRefT_x27_instMonad___redArg(v___x_5872_);
    return v___x_5873_;
}
pub unsafe fn l_Lean_Elab_Tactic_collectFreshMVars___redArg(
    mut v_inst_5879_: *mut leanh::LeanObject,
    mut v_inst_5880_: *mut leanh::LeanObject,
    mut v_k_5881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5903_: u8 = 0;
    let mut v_toFunctor_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5910_: u8 = 0;
    let mut v___f_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5932_: u8 = 0;
    let mut v_unused_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5934_: u8 = 0;
    let mut v_unused_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5882_ = l_Lean_Meta_instMonadMCtxMetaM;
                v___x_5883_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1,
                );
                v_toApplicative_5884_ = leanh::lean_ctor_get(v___x_5883_, 0);
                v_toFunctor_5885_ = leanh::lean_ctor_get(v_toApplicative_5884_, 0);
                v_toSeq_5886_ = leanh::lean_ctor_get(v_toApplicative_5884_, 2);
                v_toSeqLeft_5887_ = leanh::lean_ctor_get(v_toApplicative_5884_, 3);
                v_toSeqRight_5888_ = leanh::lean_ctor_get(v_toApplicative_5884_, 4);
                v___f_5889_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2;
                v___f_5890_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_5885_, 2);
                v___f_5891_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5891_, 0, v_toFunctor_5885_);
                v___f_5892_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5892_, 0, v_toFunctor_5885_);
                v___x_5893_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5893_, 0, v___f_5891_);
                leanh::lean_ctor_set(v___x_5893_, 1, v___f_5892_);
                leanh::lean_inc(v_toSeqRight_5888_);
                v___f_5894_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5894_, 0, v_toSeqRight_5888_);
                leanh::lean_inc(v_toSeqLeft_5887_);
                v___f_5895_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5895_, 0, v_toSeqLeft_5887_);
                leanh::lean_inc(v_toSeq_5886_);
                v___f_5896_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5896_, 0, v_toSeq_5886_);
                v___x_5897_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5897_, 0, v___x_5893_);
                leanh::lean_ctor_set(v___x_5897_, 1, v___f_5889_);
                leanh::lean_ctor_set(v___x_5897_, 2, v___f_5896_);
                leanh::lean_ctor_set(v___x_5897_, 3, v___f_5895_);
                leanh::lean_ctor_set(v___x_5897_, 4, v___f_5894_);
                v___x_5898_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5898_, 0, v___x_5897_);
                leanh::lean_ctor_set(v___x_5898_, 1, v___f_5890_);
                v___x_5899_ = l_StateRefT_x27_instMonad___redArg(v___x_5898_);
                v_toApplicative_5900_ = leanh::lean_ctor_get(v___x_5899_, 0);
                v_isSharedCheck_5934_ = (!leanh::lean_is_exclusive(v___x_5899_)) as u8;
                if v_isSharedCheck_5934_ == 0 {
                    v_unused_5935_ = leanh::lean_ctor_get(v___x_5899_, 1);
                    leanh::lean_dec(v_unused_5935_);
                    v___x_5902_ = v___x_5899_;
                    v_isShared_5903_ = v_isSharedCheck_5934_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_5900_);
                    leanh::lean_dec(v___x_5899_);
                    v___x_5902_ = leanh::lean_box(0);
                    v_isShared_5903_ = v_isSharedCheck_5934_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5904_ = leanh::lean_ctor_get(v_toApplicative_5900_, 0);
                v_toSeq_5905_ = leanh::lean_ctor_get(v_toApplicative_5900_, 2);
                v_toSeqLeft_5906_ = leanh::lean_ctor_get(v_toApplicative_5900_, 3);
                v_toSeqRight_5907_ = leanh::lean_ctor_get(v_toApplicative_5900_, 4);
                v_isSharedCheck_5932_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_5900_)) as u8;
                if v_isSharedCheck_5932_ == 0 {
                    v_unused_5933_ = leanh::lean_ctor_get(v_toApplicative_5900_, 1);
                    leanh::lean_dec(v_unused_5933_);
                    v___x_5909_ = v_toApplicative_5900_;
                    v_isShared_5910_ = v_isSharedCheck_5932_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_5907_);
                    leanh::lean_inc(v_toSeqLeft_5906_);
                    leanh::lean_inc(v_toSeq_5905_);
                    leanh::lean_inc(v_toFunctor_5904_);
                    leanh::lean_dec(v_toApplicative_5900_);
                    v___x_5909_ = leanh::lean_box(0);
                    v_isShared_5910_ = v_isSharedCheck_5932_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5911_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4;
                v___f_5912_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_5904_);
                v___f_5913_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5913_, 0, v_toFunctor_5904_);
                v___f_5914_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5914_, 0, v_toFunctor_5904_);
                v___x_5915_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5915_, 0, v___f_5913_);
                leanh::lean_ctor_set(v___x_5915_, 1, v___f_5914_);
                v___f_5916_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5916_, 0, v_toSeqRight_5907_);
                v___f_5917_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5917_, 0, v_toSeqLeft_5906_);
                v___f_5918_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5918_, 0, v_toSeq_5905_);
                if v_isShared_5910_ == 0 {
                    leanh::lean_ctor_set(v___x_5909_, 4, v___f_5916_);
                    leanh::lean_ctor_set(v___x_5909_, 3, v___f_5917_);
                    leanh::lean_ctor_set(v___x_5909_, 2, v___f_5918_);
                    leanh::lean_ctor_set(v___x_5909_, 1, v___f_5911_);
                    leanh::lean_ctor_set(v___x_5909_, 0, v___x_5915_);
                    v___x_5920_ = v___x_5909_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5931_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5931_, 0, v___x_5915_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5931_, 1, v___f_5911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5931_, 2, v___f_5918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5931_, 3, v___f_5917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5931_, 4, v___f_5916_);
                    v___x_5920_ = v_reuseFailAlloc_5931_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5903_ == 0 {
                    leanh::lean_ctor_set(v___x_5902_, 1, v___f_5912_);
                    leanh::lean_ctor_set(v___x_5902_, 0, v___x_5920_);
                    v___x_5922_ = v___x_5902_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5930_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5930_, 0, v___x_5920_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5930_, 1, v___f_5912_);
                    v___x_5922_ = v_reuseFailAlloc_5930_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_toApplicative_5923_ = leanh::lean_ctor_get(v_inst_5879_, 0);
                leanh::lean_inc_ref(v_toApplicative_5923_);
                v_toBind_5924_ = leanh::lean_ctor_get(v_inst_5879_, 1);
                leanh::lean_inc_n(v_toBind_5924_, 2);
                leanh::lean_dec_ref(v_inst_5879_);
                v_toPure_5925_ = leanh::lean_ctor_get(v_toApplicative_5923_, 1);
                leanh::lean_inc(v_toPure_5925_);
                leanh::lean_dec_ref(v_toApplicative_5923_);
                v___f_5926_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6;
                leanh::lean_inc(v_inst_5880_);
                v___x_5927_ = leanh::lean_apply_2(
                    v_inst_5880_,
                    leanh::lean_box(0),
                    v___f_5926_,
                );
                v___f_5928_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                leanh::lean_closure_set(v___f_5928_, 0, v_toPure_5925_);
                leanh::lean_closure_set(v___f_5928_, 1, v___x_5882_);
                leanh::lean_closure_set(v___f_5928_, 2, v___x_5922_);
                leanh::lean_closure_set(v___f_5928_, 3, v_inst_5880_);
                leanh::lean_closure_set(v___f_5928_, 4, v_toBind_5924_);
                leanh::lean_closure_set(v___f_5928_, 5, v_k_5881_);
                v___x_5929_ = leanh::lean_apply_4(
                    v_toBind_5924_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_5927_,
                    v___f_5928_,
                );
                return v___x_5929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_collectFreshMVars(
    mut v_m_5936_: *mut leanh::LeanObject,
    mut v_inst_5937_: *mut leanh::LeanObject,
    mut v_inst_5938_: *mut leanh::LeanObject,
    mut v_k_5939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5940_ =
        l_Lean_Elab_Tactic_collectFreshMVars___redArg(v_inst_5937_, v_inst_5938_, v_k_5939_);
    return v___x_5940_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(
    mut v_as_5941_: *mut leanh::LeanObject,
    mut v_i_5942_: usize,
    mut v_stop_5943_: usize,
    mut v_b_5944_: *mut leanh::LeanObject,
    mut v___y_5945_: *mut leanh::LeanObject,
    mut v___y_5946_: *mut leanh::LeanObject,
    mut v___y_5947_: *mut leanh::LeanObject,
    mut v___y_5948_: *mut leanh::LeanObject,
    mut v___y_5949_: *mut leanh::LeanObject,
    mut v___y_5950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: usize = 0;
    let mut v___x_5955_: usize = 0;
    let mut v___x_5957_: u8 = 0;
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: u8 = 0;
    let mut v_a_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: u8 = 0;
    let mut v_a_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5969_: u8 = 0;
    let mut v___x_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5973_: u8 = 0;
    let mut v___x_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5957_ = lean_usize_dec_eq(v_i_5942_, v_stop_5943_);
                if v___x_5957_ == 0 {
                    v___x_5958_ = lean_array_uget_borrowed(v_as_5941_, v_i_5942_);
                    leanh::lean_inc(v___x_5958_);
                    v___x_5961_ = l_Lean_Elab_Term_isLetRecAuxMVar(
                        v___x_5958_,
                        v___y_5945_,
                        v___y_5946_,
                        v___y_5947_,
                        v___y_5948_,
                        v___y_5949_,
                        v___y_5950_,
                    );
                    if leanh::lean_obj_tag(v___x_5961_) == 0 {
                        v_a_5962_ = leanh::lean_ctor_get(v___x_5961_, 0);
                        leanh::lean_inc(v_a_5962_);
                        leanh::lean_dec_ref_known(v___x_5961_, 1);
                        v___x_5963_ = (leanh::lean_unbox(v_a_5962_) as u8);
                        leanh::lean_dec(v_a_5962_);
                        if v___x_5963_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_5953_ = v_b_5944_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_5961_) == 0 {
                            v_a_5964_ = leanh::lean_ctor_get(v___x_5961_, 0);
                            leanh::lean_inc(v_a_5964_);
                            leanh::lean_dec_ref_known(v___x_5961_, 1);
                            v___x_5965_ = (leanh::lean_unbox(v_a_5964_) as u8);
                            leanh::lean_dec(v_a_5964_);
                            if v___x_5965_ == 0 {
                                v_a_5953_ = v_b_5944_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_5944_);
                            v_a_5966_ = leanh::lean_ctor_get(v___x_5961_, 0);
                            v_isSharedCheck_5973_ =
                                (!leanh::lean_is_exclusive(v___x_5961_)) as u8;
                            if v_isSharedCheck_5973_ == 0 {
                                v___x_5968_ = v___x_5961_;
                                v_isShared_5969_ = v_isSharedCheck_5973_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5966_);
                                leanh::lean_dec(v___x_5961_);
                                v___x_5968_ = leanh::lean_box(0);
                                v_isShared_5969_ = v_isSharedCheck_5973_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_5974_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5974_, 0, v_b_5944_);
                    return v___x_5974_;
                }
            }
            1 => {
                v___x_5954_ = 1usize;
                v___x_5955_ = lean_usize_add(v_i_5942_, v___x_5954_);
                v_i_5942_ = v___x_5955_;
                v_b_5944_ = v_a_5953_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc(v___x_5958_);
                v___x_5960_ = lean_array_push(v_b_5944_, v___x_5958_);
                v_a_5953_ = v___x_5960_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_5969_ == 0 {
                    v___x_5971_ = v___x_5968_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5972_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_a_5966_);
                    v___x_5971_ = v_reuseFailAlloc_5972_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg___boxed(
    mut v_as_5975_: *mut leanh::LeanObject,
    mut v_i_5976_: *mut leanh::LeanObject,
    mut v_stop_5977_: *mut leanh::LeanObject,
    mut v_b_5978_: *mut leanh::LeanObject,
    mut v___y_5979_: *mut leanh::LeanObject,
    mut v___y_5980_: *mut leanh::LeanObject,
    mut v___y_5981_: *mut leanh::LeanObject,
    mut v___y_5982_: *mut leanh::LeanObject,
    mut v___y_5983_: *mut leanh::LeanObject,
    mut v___y_5984_: *mut leanh::LeanObject,
    mut v___y_5985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5986_: usize = 0;
    let mut v_stop_boxed_5987_: usize = 0;
    let mut v_res_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5986_ = leanh::lean_unbox_usize(v_i_5976_);
    leanh::lean_dec(v_i_5976_);
    v_stop_boxed_5987_ = leanh::lean_unbox_usize(v_stop_5977_);
    leanh::lean_dec(v_stop_5977_);
    v_res_5988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_as_5975_, v_i_boxed_5986_, v_stop_boxed_5987_, v_b_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_);
    leanh::lean_dec(v___y_5984_);
    leanh::lean_dec_ref(v___y_5983_);
    leanh::lean_dec(v___y_5982_);
    leanh::lean_dec_ref(v___y_5981_);
    leanh::lean_dec(v___y_5980_);
    leanh::lean_dec_ref(v___y_5979_);
    leanh::lean_dec_ref(v_as_5975_);
    return v_res_5988_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(
    mut v_as_5989_: *mut leanh::LeanObject,
    mut v_i_5990_: usize,
    mut v_stop_5991_: usize,
    mut v_b_5992_: *mut leanh::LeanObject,
    mut v___y_5993_: *mut leanh::LeanObject,
    mut v___y_5994_: *mut leanh::LeanObject,
    mut v___y_5995_: *mut leanh::LeanObject,
    mut v___y_5996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5998_: u8 = 0;
    let mut v___x_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: usize = 0;
    let mut v___x_6005_: usize = 0;
    let mut v___x_6007_: u8 = 0;
    let mut v___x_6008_: u8 = 0;
    let mut v___x_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6013_: u8 = 0;
    let mut v___x_6015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6017_: u8 = 0;
    let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5998_ = lean_usize_dec_eq(v_i_5990_, v_stop_5991_);
                if v___x_5998_ == 0 {
                    v___x_5999_ = lean_array_uget_borrowed(v_as_5989_, v_i_5990_);
                    leanh::lean_inc(v___x_5999_);
                    v___x_6000_ = l_Lean_MVarId_getKind(
                        v___x_5999_,
                        v___y_5993_,
                        v___y_5994_,
                        v___y_5995_,
                        v___y_5996_,
                    );
                    if leanh::lean_obj_tag(v___x_6000_) == 0 {
                        v_a_6001_ = leanh::lean_ctor_get(v___x_6000_, 0);
                        leanh::lean_inc(v_a_6001_);
                        leanh::lean_dec_ref_known(v___x_6000_, 1);
                        v___x_6007_ = (leanh::lean_unbox(v_a_6001_) as u8);
                        leanh::lean_dec(v_a_6001_);
                        v___x_6008_ = l_Lean_MetavarKind_isNatural(v___x_6007_);
                        if v___x_6008_ == 0 {
                            v_a_6003_ = v_b_5992_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v___x_5999_);
                            v___x_6009_ = lean_array_push(v_b_5992_, v___x_5999_);
                            v_a_6003_ = v___x_6009_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_5992_);
                        v_a_6010_ = leanh::lean_ctor_get(v___x_6000_, 0);
                        v_isSharedCheck_6017_ =
                            (!leanh::lean_is_exclusive(v___x_6000_)) as u8;
                        if v_isSharedCheck_6017_ == 0 {
                            v___x_6012_ = v___x_6000_;
                            v_isShared_6013_ = v_isSharedCheck_6017_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6010_);
                            leanh::lean_dec(v___x_6000_);
                            v___x_6012_ = leanh::lean_box(0);
                            v_isShared_6013_ = v_isSharedCheck_6017_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_6018_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6018_, 0, v_b_5992_);
                    return v___x_6018_;
                }
            }
            1 => {
                v___x_6004_ = 1usize;
                v___x_6005_ = lean_usize_add(v_i_5990_, v___x_6004_);
                v_i_5990_ = v___x_6005_;
                v_b_5992_ = v_a_6003_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_6013_ == 0 {
                    v___x_6015_ = v___x_6012_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6016_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_a_6010_);
                    v___x_6015_ = v_reuseFailAlloc_6016_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg___boxed(
    mut v_as_6019_: *mut leanh::LeanObject,
    mut v_i_6020_: *mut leanh::LeanObject,
    mut v_stop_6021_: *mut leanh::LeanObject,
    mut v_b_6022_: *mut leanh::LeanObject,
    mut v___y_6023_: *mut leanh::LeanObject,
    mut v___y_6024_: *mut leanh::LeanObject,
    mut v___y_6025_: *mut leanh::LeanObject,
    mut v___y_6026_: *mut leanh::LeanObject,
    mut v___y_6027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6028_: usize = 0;
    let mut v_stop_boxed_6029_: usize = 0;
    let mut v_res_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6028_ = leanh::lean_unbox_usize(v_i_6020_);
    leanh::lean_dec(v_i_6020_);
    v_stop_boxed_6029_ = leanh::lean_unbox_usize(v_stop_6021_);
    leanh::lean_dec(v_stop_6021_);
    v_res_6030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_as_6019_, v_i_boxed_6028_, v_stop_boxed_6029_, v_b_6022_, v___y_6023_, v___y_6024_, v___y_6025_, v___y_6026_);
    leanh::lean_dec(v___y_6026_);
    leanh::lean_dec_ref(v___y_6025_);
    leanh::lean_dec(v___y_6024_);
    leanh::lean_dec_ref(v___y_6023_);
    leanh::lean_dec_ref(v_as_6019_);
    return v_res_6030_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(
    mut v___x_6031_: *mut leanh::LeanObject,
    mut v_mvarId_u2081_6032_: *mut leanh::LeanObject,
    mut v_mvarId_u2082_6033_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_decl_u2081_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_u2082_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: u8 = 0;
    leanh::lean_inc(v_mvarId_u2081_6032_);
    v_decl_u2081_6034_ = l_Lean_MetavarContext_getDecl(v___x_6031_, v_mvarId_u2081_6032_);
    v_index_6035_ = leanh::lean_ctor_get(v_decl_u2081_6034_, 6);
    leanh::lean_inc(v_index_6035_);
    leanh::lean_dec_ref(v_decl_u2081_6034_);
    leanh::lean_inc(v_mvarId_u2082_6033_);
    v_decl_u2082_6036_ = l_Lean_MetavarContext_getDecl(v___x_6031_, v_mvarId_u2082_6033_);
    v_index_6037_ = leanh::lean_ctor_get(v_decl_u2082_6036_, 6);
    leanh::lean_inc(v_index_6037_);
    leanh::lean_dec_ref(v_decl_u2082_6036_);
    v___x_6038_ = lean_nat_dec_eq(v_index_6035_, v_index_6037_);
    if v___x_6038_ == 0 {
        let mut v___x_6039_: u8 = 0;
        leanh::lean_dec(v_mvarId_u2082_6033_);
        leanh::lean_dec(v_mvarId_u2081_6032_);
        v___x_6039_ = lean_nat_dec_lt(v_index_6035_, v_index_6037_);
        leanh::lean_dec(v_index_6037_);
        leanh::lean_dec(v_index_6035_);
        return v___x_6039_;
    } else {
        let mut v___x_6040_: u8 = 0;
        leanh::lean_dec(v_index_6037_);
        leanh::lean_dec(v_index_6035_);
        v___x_6040_ = l_Lean_Name_quickLt(v_mvarId_u2081_6032_, v_mvarId_u2082_6033_);
        leanh::lean_dec(v_mvarId_u2082_6033_);
        leanh::lean_dec(v_mvarId_u2081_6032_);
        return v___x_6040_;
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0___boxed(
    mut v___x_6041_: *mut leanh::LeanObject,
    mut v_mvarId_u2081_6042_: *mut leanh::LeanObject,
    mut v_mvarId_u2082_6043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6044_: u8 = 0;
    let mut v_r_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6044_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_6041_, v_mvarId_u2081_6042_, v_mvarId_u2082_6043_);
    leanh::lean_dec_ref(v___x_6041_);
    v_r_6045_ = leanh::lean_box((v_res_6044_) as usize);
    return v_r_6045_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v___x_6046_: *mut leanh::LeanObject,
    mut v_hi_6047_: *mut leanh::LeanObject,
    mut v_pivot_6048_: *mut leanh::LeanObject,
    mut v_as_6049_: *mut leanh::LeanObject,
    mut v_i_6050_: *mut leanh::LeanObject,
    mut v_k_6051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6053_: u8 = 0;
    let mut v___x_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: u8 = 0;
    let mut v___x_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_u2081_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_u2082_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: u8 = 0;
    let mut v___x_6071_: u8 = 0;
    let mut v___x_6072_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6062_ = lean_nat_dec_lt(v_k_6051_, v_hi_6047_);
                if v___x_6062_ == 0 {
                    leanh::lean_dec(v_k_6051_);
                    leanh::lean_dec(v_pivot_6048_);
                    v___x_6063_ = lean_array_fswap(v_as_6049_, v_i_6050_, v_hi_6047_);
                    v___x_6064_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6064_, 0, v_i_6050_);
                    leanh::lean_ctor_set(v___x_6064_, 1, v___x_6063_);
                    return v___x_6064_;
                } else {
                    v___x_6065_ = lean_array_fget_borrowed(v_as_6049_, v_k_6051_);
                    leanh::lean_inc(v___x_6065_);
                    v_decl_u2081_6066_ = l_Lean_MetavarContext_getDecl(v___x_6046_, v___x_6065_);
                    v_index_6067_ = leanh::lean_ctor_get(v_decl_u2081_6066_, 6);
                    leanh::lean_inc(v_index_6067_);
                    leanh::lean_dec_ref(v_decl_u2081_6066_);
                    leanh::lean_inc(v_pivot_6048_);
                    v_decl_u2082_6068_ = l_Lean_MetavarContext_getDecl(v___x_6046_, v_pivot_6048_);
                    v_index_6069_ = leanh::lean_ctor_get(v_decl_u2082_6068_, 6);
                    leanh::lean_inc(v_index_6069_);
                    leanh::lean_dec_ref(v_decl_u2082_6068_);
                    v___x_6070_ = lean_nat_dec_eq(v_index_6067_, v_index_6069_);
                    if v___x_6070_ == 0 {
                        v___x_6071_ = lean_nat_dec_lt(v_index_6067_, v_index_6069_);
                        leanh::lean_dec(v_index_6069_);
                        leanh::lean_dec(v_index_6067_);
                        v___y_6053_ = v___x_6071_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_index_6069_);
                        leanh::lean_dec(v_index_6067_);
                        v___x_6072_ = l_Lean_Name_quickLt(v___x_6065_, v_pivot_6048_);
                        v___y_6053_ = v___x_6072_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6053_ == 0 {
                    v___x_6054_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6055_ = lean_nat_add(v_k_6051_, v___x_6054_);
                    leanh::lean_dec(v_k_6051_);
                    v_k_6051_ = v___x_6055_;
                    state = 0;
                    continue;
                } else {
                    v___x_6057_ = lean_array_fswap(v_as_6049_, v_i_6050_, v_k_6051_);
                    v___x_6058_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6059_ = lean_nat_add(v_i_6050_, v___x_6058_);
                    leanh::lean_dec(v_i_6050_);
                    v___x_6060_ = lean_nat_add(v_k_6051_, v___x_6058_);
                    leanh::lean_dec(v_k_6051_);
                    v_as_6049_ = v___x_6057_;
                    v_i_6050_ = v___x_6059_;
                    v_k_6051_ = v___x_6060_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v___x_6073_: *mut leanh::LeanObject,
    mut v_hi_6074_: *mut leanh::LeanObject,
    mut v_pivot_6075_: *mut leanh::LeanObject,
    mut v_as_6076_: *mut leanh::LeanObject,
    mut v_i_6077_: *mut leanh::LeanObject,
    mut v_k_6078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6079_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_6073_, v_hi_6074_, v_pivot_6075_, v_as_6076_, v_i_6077_, v_k_6078_);
    leanh::lean_dec(v_hi_6074_);
    leanh::lean_dec_ref(v___x_6073_);
    return v_res_6079_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(
    mut v___x_6080_: *mut leanh::LeanObject,
    mut v_n_6081_: *mut leanh::LeanObject,
    mut v_as_6082_: *mut leanh::LeanObject,
    mut v_lo_6083_: *mut leanh::LeanObject,
    mut v_hi_6084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: u8 = 0;
    let mut v___x_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: u8 = 0;
    let mut v___x_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: u8 = 0;
    let mut v___x_6105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: u8 = 0;
    let mut v___x_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: u8 = 0;
    let mut v___x_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6096_ = lean_nat_dec_lt(v_lo_6083_, v_hi_6084_);
                if v___x_6096_ == 0 {
                    leanh::lean_dec(v_lo_6083_);
                    return v_as_6082_;
                } else {
                    v___x_6097_ = lean_nat_add(v_lo_6083_, v_hi_6084_);
                    v___x_6098_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_6099_ = lean_nat_shiftr(v___x_6097_, v___x_6098_);
                    leanh::lean_dec(v___x_6097_);
                    v___x_6112_ = lean_array_fget_borrowed(v_as_6082_, v_mid_6099_);
                    v___x_6113_ = lean_array_fget_borrowed(v_as_6082_, v_lo_6083_);
                    leanh::lean_inc(v___x_6113_);
                    leanh::lean_inc(v___x_6112_);
                    v___x_6114_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_6080_, v___x_6112_, v___x_6113_);
                    if v___x_6114_ == 0 {
                        v___y_6107_ = v_as_6082_;
                        state = 3;
                        continue;
                    } else {
                        v___x_6115_ = lean_array_fswap(v_as_6082_, v_lo_6083_, v_mid_6099_);
                        v___y_6107_ = v___x_6115_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_6087_ = lean_array_fget(v___y_6086_, v_hi_6084_);
                leanh::lean_inc_n(v_lo_6083_, 2);
                v___x_6088_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_6080_, v_hi_6084_, v_pivot_6087_, v___y_6086_, v_lo_6083_, v_lo_6083_);
                v_fst_6089_ = leanh::lean_ctor_get(v___x_6088_, 0);
                leanh::lean_inc(v_fst_6089_);
                v_snd_6090_ = leanh::lean_ctor_get(v___x_6088_, 1);
                leanh::lean_inc(v_snd_6090_);
                leanh::lean_dec_ref(v___x_6088_);
                v___x_6091_ = lean_nat_dec_le(v_hi_6084_, v_fst_6089_);
                if v___x_6091_ == 0 {
                    v___x_6092_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_6080_, v_n_6081_, v_snd_6090_, v_lo_6083_, v_fst_6089_);
                    v___x_6093_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6094_ = lean_nat_add(v_fst_6089_, v___x_6093_);
                    leanh::lean_dec(v_fst_6089_);
                    v_as_6082_ = v___x_6092_;
                    v_lo_6083_ = v___x_6094_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_6089_);
                    leanh::lean_dec(v_lo_6083_);
                    return v_snd_6090_;
                }
            }
            2 => {
                v___x_6102_ = lean_array_fget_borrowed(v___y_6101_, v_mid_6099_);
                v___x_6103_ = lean_array_fget_borrowed(v___y_6101_, v_hi_6084_);
                leanh::lean_inc(v___x_6103_);
                leanh::lean_inc(v___x_6102_);
                v___x_6104_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_6080_, v___x_6102_, v___x_6103_);
                if v___x_6104_ == 0 {
                    leanh::lean_dec(v_mid_6099_);
                    v___y_6086_ = v___y_6101_;
                    state = 1;
                    continue;
                } else {
                    v___x_6105_ = lean_array_fswap(v___y_6101_, v_mid_6099_, v_hi_6084_);
                    leanh::lean_dec(v_mid_6099_);
                    v___y_6086_ = v___x_6105_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_6108_ = lean_array_fget_borrowed(v___y_6107_, v_hi_6084_);
                v___x_6109_ = lean_array_fget_borrowed(v___y_6107_, v_lo_6083_);
                leanh::lean_inc(v___x_6109_);
                leanh::lean_inc(v___x_6108_);
                v___x_6110_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_6080_, v___x_6108_, v___x_6109_);
                if v___x_6110_ == 0 {
                    v___y_6101_ = v___y_6107_;
                    state = 2;
                    continue;
                } else {
                    v___x_6111_ = lean_array_fswap(v___y_6107_, v_lo_6083_, v_hi_6084_);
                    v___y_6101_ = v___x_6111_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___boxed(
    mut v___x_6116_: *mut leanh::LeanObject,
    mut v_n_6117_: *mut leanh::LeanObject,
    mut v_as_6118_: *mut leanh::LeanObject,
    mut v_lo_6119_: *mut leanh::LeanObject,
    mut v_hi_6120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6121_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_6116_, v_n_6117_, v_as_6118_, v_lo_6119_, v_hi_6120_);
    leanh::lean_dec(v_hi_6120_);
    leanh::lean_dec(v_n_6117_);
    leanh::lean_dec_ref(v___x_6116_);
    return v_res_6121_;
}
pub unsafe fn l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(
    mut v_mvarIds_6122_: *mut leanh::LeanObject,
    mut v___y_6123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: u8 = 0;
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: u8 = 0;
    let mut v___x_6140_: u8 = 0;
    let mut v___x_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6125_ = lean_st_ref_get(v___y_6123_);
                v_mctx_6126_ = leanh::lean_ctor_get(v___x_6125_, 0);
                leanh::lean_inc_ref(v_mctx_6126_);
                leanh::lean_dec(v___x_6125_);
                v___x_6127_ = lean_array_get_size(v_mvarIds_6122_);
                v___x_6133_ = leanh::lean_unsigned_to_nat(0);
                v___x_6134_ = lean_nat_dec_eq(v___x_6127_, v___x_6133_);
                if v___x_6134_ == 0 {
                    v___x_6135_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6136_ = lean_nat_sub(v___x_6127_, v___x_6135_);
                    v___x_6140_ = lean_nat_dec_le(v___x_6133_, v___x_6136_);
                    if v___x_6140_ == 0 {
                        leanh::lean_inc(v___x_6136_);
                        v___y_6138_ = v___x_6136_;
                        state = 2;
                        continue;
                    } else {
                        v___y_6138_ = v___x_6133_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_mctx_6126_);
                    v___x_6141_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6141_, 0, v_mvarIds_6122_);
                    return v___x_6141_;
                }
            }
            1 => {
                v___x_6131_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v_mctx_6126_, v___x_6127_, v_mvarIds_6122_, v___y_6129_, v___y_6130_);
                leanh::lean_dec(v___y_6130_);
                leanh::lean_dec_ref(v_mctx_6126_);
                v___x_6132_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6132_, 0, v___x_6131_);
                return v___x_6132_;
            }
            2 => {
                v___x_6139_ = lean_nat_dec_le(v___y_6138_, v___x_6136_);
                if v___x_6139_ == 0 {
                    leanh::lean_dec(v___x_6136_);
                    leanh::lean_inc(v___y_6138_);
                    v___y_6129_ = v___y_6138_;
                    v___y_6130_ = v___y_6138_;
                    state = 1;
                    continue;
                } else {
                    v___y_6129_ = v___y_6138_;
                    v___y_6130_ = v___x_6136_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg___boxed(
    mut v_mvarIds_6142_: *mut leanh::LeanObject,
    mut v___y_6143_: *mut leanh::LeanObject,
    mut v___y_6144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6145_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_mvarIds_6142_, v___y_6143_);
    leanh::lean_dec(v___y_6143_);
    return v_res_6145_;
}
pub unsafe fn l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(
    mut v_k_6146_: *mut leanh::LeanObject,
    mut v___y_6147_: *mut leanh::LeanObject,
    mut v___y_6148_: *mut leanh::LeanObject,
    mut v___y_6149_: *mut leanh::LeanObject,
    mut v___y_6150_: *mut leanh::LeanObject,
    mut v___y_6151_: *mut leanh::LeanObject,
    mut v___y_6152_: *mut leanh::LeanObject,
    mut v___y_6153_: *mut leanh::LeanObject,
    mut v___y_6154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6169_: u8 = 0;
    let mut v___x_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6174_: u8 = 0;
    let mut v_a_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6178_: u8 = 0;
    let mut v___x_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6182_: u8 = 0;
    let mut v_a_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6186_: u8 = 0;
    let mut v___x_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6156_ = lean_st_ref_get(v___y_6152_);
                v_mctx_6157_ = leanh::lean_ctor_get(v___x_6156_, 0);
                leanh::lean_inc_ref(v_mctx_6157_);
                leanh::lean_dec(v___x_6156_);
                v_mvarCounter_6158_ = leanh::lean_ctor_get(v_mctx_6157_, 3);
                leanh::lean_inc(v_mvarCounter_6158_);
                leanh::lean_dec_ref(v_mctx_6157_);
                leanh::lean_inc(v___y_6154_);
                leanh::lean_inc_ref(v___y_6153_);
                leanh::lean_inc(v___y_6152_);
                leanh::lean_inc_ref(v___y_6151_);
                leanh::lean_inc(v___y_6150_);
                leanh::lean_inc_ref(v___y_6149_);
                leanh::lean_inc(v___y_6148_);
                leanh::lean_inc_ref(v___y_6147_);
                v___x_6159_ = leanh::lean_apply_9(
                    v_k_6146_,
                    v___y_6147_,
                    v___y_6148_,
                    v___y_6149_,
                    v___y_6150_,
                    v___y_6151_,
                    v___y_6152_,
                    v___y_6153_,
                    v___y_6154_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_6159_) == 0 {
                    v_a_6160_ = leanh::lean_ctor_get(v___x_6159_, 0);
                    leanh::lean_inc_n(v_a_6160_, 2);
                    leanh::lean_dec_ref_known(v___x_6159_, 1);
                    v___x_6161_ = l_Lean_Meta_getMVarsNoDelayed(
                        v_a_6160_,
                        v___y_6151_,
                        v___y_6152_,
                        v___y_6153_,
                        v___y_6154_,
                    );
                    if leanh::lean_obj_tag(v___x_6161_) == 0 {
                        v_a_6162_ = leanh::lean_ctor_get(v___x_6161_, 0);
                        leanh::lean_inc(v_a_6162_);
                        leanh::lean_dec_ref_known(v___x_6161_, 1);
                        v___x_6163_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(
                            v_a_6162_,
                            v_mvarCounter_6158_,
                            v___y_6152_,
                        );
                        leanh::lean_dec(v_mvarCounter_6158_);
                        leanh::lean_dec(v_a_6162_);
                        v_a_6164_ = leanh::lean_ctor_get(v___x_6163_, 0);
                        leanh::lean_inc(v_a_6164_);
                        leanh::lean_dec_ref(v___x_6163_);
                        v___x_6165_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_a_6164_, v___y_6152_);
                        v_a_6166_ = leanh::lean_ctor_get(v___x_6165_, 0);
                        v_isSharedCheck_6174_ =
                            (!leanh::lean_is_exclusive(v___x_6165_)) as u8;
                        if v_isSharedCheck_6174_ == 0 {
                            v___x_6168_ = v___x_6165_;
                            v_isShared_6169_ = v_isSharedCheck_6174_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6166_);
                            leanh::lean_dec(v___x_6165_);
                            v___x_6168_ = leanh::lean_box(0);
                            v_isShared_6169_ = v_isSharedCheck_6174_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_6160_);
                        leanh::lean_dec(v_mvarCounter_6158_);
                        v_a_6175_ = leanh::lean_ctor_get(v___x_6161_, 0);
                        v_isSharedCheck_6182_ =
                            (!leanh::lean_is_exclusive(v___x_6161_)) as u8;
                        if v_isSharedCheck_6182_ == 0 {
                            v___x_6177_ = v___x_6161_;
                            v_isShared_6178_ = v_isSharedCheck_6182_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6175_);
                            leanh::lean_dec(v___x_6161_);
                            v___x_6177_ = leanh::lean_box(0);
                            v_isShared_6178_ = v_isSharedCheck_6182_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarCounter_6158_);
                    v_a_6183_ = leanh::lean_ctor_get(v___x_6159_, 0);
                    v_isSharedCheck_6190_ = (!leanh::lean_is_exclusive(v___x_6159_)) as u8;
                    if v_isSharedCheck_6190_ == 0 {
                        v___x_6185_ = v___x_6159_;
                        v_isShared_6186_ = v_isSharedCheck_6190_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6183_);
                        leanh::lean_dec(v___x_6159_);
                        v___x_6185_ = leanh::lean_box(0);
                        v_isShared_6186_ = v_isSharedCheck_6190_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6170_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6170_, 0, v_a_6160_);
                leanh::lean_ctor_set(v___x_6170_, 1, v_a_6166_);
                if v_isShared_6169_ == 0 {
                    leanh::lean_ctor_set(v___x_6168_, 0, v___x_6170_);
                    v___x_6172_ = v___x_6168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6173_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6173_, 0, v___x_6170_);
                    v___x_6172_ = v_reuseFailAlloc_6173_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6172_;
            }
            3 => {
                if v_isShared_6178_ == 0 {
                    v___x_6180_ = v___x_6177_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6181_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6181_, 0, v_a_6175_);
                    v___x_6180_ = v_reuseFailAlloc_6181_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6180_;
            }
            5 => {
                if v_isShared_6186_ == 0 {
                    v___x_6188_ = v___x_6185_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6189_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 0, v_a_6183_);
                    v___x_6188_ = v_reuseFailAlloc_6189_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0___boxed(
    mut v_k_6191_: *mut leanh::LeanObject,
    mut v___y_6192_: *mut leanh::LeanObject,
    mut v___y_6193_: *mut leanh::LeanObject,
    mut v___y_6194_: *mut leanh::LeanObject,
    mut v___y_6195_: *mut leanh::LeanObject,
    mut v___y_6196_: *mut leanh::LeanObject,
    mut v___y_6197_: *mut leanh::LeanObject,
    mut v___y_6198_: *mut leanh::LeanObject,
    mut v___y_6199_: *mut leanh::LeanObject,
    mut v___y_6200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6201_ = l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(v_k_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_);
    leanh::lean_dec(v___y_6199_);
    leanh::lean_dec_ref(v___y_6198_);
    leanh::lean_dec(v___y_6197_);
    leanh::lean_dec_ref(v___y_6196_);
    leanh::lean_dec(v___y_6195_);
    leanh::lean_dec_ref(v___y_6194_);
    leanh::lean_dec(v___y_6193_);
    leanh::lean_dec_ref(v___y_6192_);
    return v_res_6201_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(
    mut v_k_6202_: *mut leanh::LeanObject,
    mut v_parentTag_6203_: *mut leanh::LeanObject,
    mut v_tagSuffix_6204_: *mut leanh::LeanObject,
    mut v_allowNaturalHoles_6205_: u8,
    mut v_a_6206_: *mut leanh::LeanObject,
    mut v_a_6207_: *mut leanh::LeanObject,
    mut v_a_6208_: *mut leanh::LeanObject,
    mut v_a_6209_: *mut leanh::LeanObject,
    mut v_a_6210_: *mut leanh::LeanObject,
    mut v_a_6211_: *mut leanh::LeanObject,
    mut v_a_6212_: *mut leanh::LeanObject,
    mut v_a_6213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6221_: u8 = 0;
    let mut v___y_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6236_: u8 = 0;
    let mut v___x_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6243_: u8 = 0;
    let mut v_unused_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6248_: u8 = 0;
    let mut v___x_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6252_: u8 = 0;
    let mut v___y_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6260_: u8 = 0;
    let mut v___x_6262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6264_: u8 = 0;
    let mut v___y_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6272_: u8 = 0;
    let mut v___x_6274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6276_: u8 = 0;
    let mut v___x_6277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: u8 = 0;
    let mut v___x_6283_: u8 = 0;
    let mut v___x_6284_: usize = 0;
    let mut v___x_6285_: usize = 0;
    let mut v___x_6286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: usize = 0;
    let mut v___x_6288_: usize = 0;
    let mut v___x_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6296_: u8 = 0;
    let mut v___x_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6300_: u8 = 0;
    let mut v___x_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: u8 = 0;
    let mut v___x_6304_: u8 = 0;
    let mut v___x_6305_: usize = 0;
    let mut v___x_6306_: usize = 0;
    let mut v___x_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: usize = 0;
    let mut v___x_6309_: usize = 0;
    let mut v___x_6310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6311_: u8 = 0;
    let mut v_a_6312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6315_: u8 = 0;
    let mut v___x_6317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6215_ = l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(v_k_6202_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_, v_a_6211_, v_a_6212_, v_a_6213_);
                if leanh::lean_obj_tag(v___x_6215_) == 0 {
                    v_a_6216_ = leanh::lean_ctor_get(v___x_6215_, 0);
                    leanh::lean_inc(v_a_6216_);
                    leanh::lean_dec_ref_known(v___x_6215_, 1);
                    v_fst_6217_ = leanh::lean_ctor_get(v_a_6216_, 0);
                    v_snd_6218_ = leanh::lean_ctor_get(v_a_6216_, 1);
                    v_isSharedCheck_6311_ = (!leanh::lean_is_exclusive(v_a_6216_)) as u8;
                    if v_isSharedCheck_6311_ == 0 {
                        v___x_6220_ = v_a_6216_;
                        v_isShared_6221_ = v_isSharedCheck_6311_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6218_);
                        leanh::lean_inc(v_fst_6217_);
                        leanh::lean_dec(v_a_6216_);
                        v___x_6220_ = leanh::lean_box(0);
                        v_isShared_6221_ = v_isSharedCheck_6311_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_tagSuffix_6204_);
                    leanh::lean_dec(v_parentTag_6203_);
                    v_a_6312_ = leanh::lean_ctor_get(v___x_6215_, 0);
                    v_isSharedCheck_6319_ = (!leanh::lean_is_exclusive(v___x_6215_)) as u8;
                    if v_isSharedCheck_6319_ == 0 {
                        v___x_6314_ = v___x_6215_;
                        v_isShared_6315_ = v_isSharedCheck_6319_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6312_);
                        leanh::lean_dec(v___x_6215_);
                        v___x_6314_ = leanh::lean_box(0);
                        v_isShared_6315_ = v_isSharedCheck_6319_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6277_ = leanh::lean_unsigned_to_nat(0);
                v___x_6301_ = lean_array_get_size(v_snd_6218_);
                v___x_6302_ = l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0;
                v___x_6303_ = lean_nat_dec_lt(v___x_6277_, v___x_6301_);
                if v___x_6303_ == 0 {
                    leanh::lean_dec(v_snd_6218_);
                    v_a_6279_ = v___x_6302_;
                    state = 14;
                    continue;
                } else {
                    v___x_6304_ = lean_nat_dec_le(v___x_6301_, v___x_6301_);
                    if v___x_6304_ == 0 {
                        if v___x_6303_ == 0 {
                            leanh::lean_dec(v_snd_6218_);
                            v_a_6279_ = v___x_6302_;
                            state = 14;
                            continue;
                        } else {
                            v___x_6305_ = 0usize;
                            v___x_6306_ = lean_usize_of_nat(v___x_6301_);
                            v___x_6307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_snd_6218_, v___x_6305_, v___x_6306_, v___x_6302_, v_a_6208_, v_a_6209_, v_a_6210_, v_a_6211_, v_a_6212_, v_a_6213_);
                            leanh::lean_dec(v_snd_6218_);
                            v___y_6291_ = v___x_6307_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_6308_ = 0usize;
                        v___x_6309_ = lean_usize_of_nat(v___x_6301_);
                        v___x_6310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_snd_6218_, v___x_6308_, v___x_6309_, v___x_6302_, v_a_6208_, v_a_6209_, v_a_6210_, v_a_6211_, v_a_6212_, v_a_6213_);
                        leanh::lean_dec(v_snd_6218_);
                        v___y_6291_ = v___x_6310_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6232_ = lean_array_to_list(v___y_6223_);
                v___x_6233_ = l_Lean_Elab_Tactic_tagUntaggedGoals(
                    v_parentTag_6203_,
                    v_tagSuffix_6204_,
                    v___x_6232_,
                    v___y_6224_,
                    v___y_6225_,
                    v___y_6226_,
                    v___y_6227_,
                    v___y_6228_,
                    v___y_6229_,
                    v___y_6230_,
                    v___y_6231_,
                );
                if leanh::lean_obj_tag(v___x_6233_) == 0 {
                    v_isSharedCheck_6243_ = (!leanh::lean_is_exclusive(v___x_6233_)) as u8;
                    if v_isSharedCheck_6243_ == 0 {
                        v_unused_6244_ = leanh::lean_ctor_get(v___x_6233_, 0);
                        leanh::lean_dec(v_unused_6244_);
                        v___x_6235_ = v___x_6233_;
                        v_isShared_6236_ = v_isSharedCheck_6243_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6233_);
                        v___x_6235_ = leanh::lean_box(0);
                        v_isShared_6236_ = v_isSharedCheck_6243_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_6232_);
                    leanh::lean_del_object(v___x_6220_);
                    leanh::lean_dec(v_fst_6217_);
                    v_a_6245_ = leanh::lean_ctor_get(v___x_6233_, 0);
                    v_isSharedCheck_6252_ = (!leanh::lean_is_exclusive(v___x_6233_)) as u8;
                    if v_isSharedCheck_6252_ == 0 {
                        v___x_6247_ = v___x_6233_;
                        v_isShared_6248_ = v_isSharedCheck_6252_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6245_);
                        leanh::lean_dec(v___x_6233_);
                        v___x_6247_ = leanh::lean_box(0);
                        v_isShared_6248_ = v_isSharedCheck_6252_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6221_ == 0 {
                    leanh::lean_ctor_set(v___x_6220_, 1, v___x_6232_);
                    v___x_6238_ = v___x_6220_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6242_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6242_, 0, v_fst_6217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6242_, 1, v___x_6232_);
                    v___x_6238_ = v_reuseFailAlloc_6242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6236_ == 0 {
                    leanh::lean_ctor_set(v___x_6235_, 0, v___x_6238_);
                    v___x_6240_ = v___x_6235_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6241_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6241_, 0, v___x_6238_);
                    v___x_6240_ = v_reuseFailAlloc_6241_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6240_;
            }
            6 => {
                if v_isShared_6248_ == 0 {
                    v___x_6250_ = v___x_6247_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6251_, 0, v_a_6245_);
                    v___x_6250_ = v_reuseFailAlloc_6251_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6250_;
            }
            8 => {
                v___x_6256_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(
                    v_a_6255_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_, v_a_6211_,
                    v_a_6212_, v_a_6213_,
                );
                leanh::lean_dec_ref(v_a_6255_);
                if leanh::lean_obj_tag(v___x_6256_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6256_, 1);
                    v___y_6223_ = v___y_6254_;
                    v___y_6224_ = v_a_6206_;
                    v___y_6225_ = v_a_6207_;
                    v___y_6226_ = v_a_6208_;
                    v___y_6227_ = v_a_6209_;
                    v___y_6228_ = v_a_6210_;
                    v___y_6229_ = v_a_6211_;
                    v___y_6230_ = v_a_6212_;
                    v___y_6231_ = v_a_6213_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_6254_);
                    leanh::lean_del_object(v___x_6220_);
                    leanh::lean_dec(v_fst_6217_);
                    leanh::lean_dec(v_tagSuffix_6204_);
                    leanh::lean_dec(v_parentTag_6203_);
                    v_a_6257_ = leanh::lean_ctor_get(v___x_6256_, 0);
                    v_isSharedCheck_6264_ = (!leanh::lean_is_exclusive(v___x_6256_)) as u8;
                    if v_isSharedCheck_6264_ == 0 {
                        v___x_6259_ = v___x_6256_;
                        v_isShared_6260_ = v_isSharedCheck_6264_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6257_);
                        leanh::lean_dec(v___x_6256_);
                        v___x_6259_ = leanh::lean_box(0);
                        v_isShared_6260_ = v_isSharedCheck_6264_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_6260_ == 0 {
                    v___x_6262_ = v___x_6259_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6263_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6263_, 0, v_a_6257_);
                    v___x_6262_ = v_reuseFailAlloc_6263_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6262_;
            }
            11 => {
                if leanh::lean_obj_tag(v___y_6267_) == 0 {
                    v_a_6268_ = leanh::lean_ctor_get(v___y_6267_, 0);
                    leanh::lean_inc(v_a_6268_);
                    leanh::lean_dec_ref_known(v___y_6267_, 1);
                    v___y_6254_ = v___y_6266_;
                    v_a_6255_ = v_a_6268_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_6266_);
                    leanh::lean_del_object(v___x_6220_);
                    leanh::lean_dec(v_fst_6217_);
                    leanh::lean_dec(v_tagSuffix_6204_);
                    leanh::lean_dec(v_parentTag_6203_);
                    v_a_6269_ = leanh::lean_ctor_get(v___y_6267_, 0);
                    v_isSharedCheck_6276_ = (!leanh::lean_is_exclusive(v___y_6267_)) as u8;
                    if v_isSharedCheck_6276_ == 0 {
                        v___x_6271_ = v___y_6267_;
                        v_isShared_6272_ = v_isSharedCheck_6276_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6269_);
                        leanh::lean_dec(v___y_6267_);
                        v___x_6271_ = leanh::lean_box(0);
                        v_isShared_6272_ = v_isSharedCheck_6276_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_6272_ == 0 {
                    v___x_6274_ = v___x_6271_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6275_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 0, v_a_6269_);
                    v___x_6274_ = v_reuseFailAlloc_6275_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6274_;
            }
            14 => {
                if v_allowNaturalHoles_6205_ == 0 {
                    v___x_6280_ = lean_array_get_size(v_a_6279_);
                    v___x_6281_ = l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0;
                    v___x_6282_ = lean_nat_dec_lt(v___x_6277_, v___x_6280_);
                    if v___x_6282_ == 0 {
                        v___y_6254_ = v_a_6279_;
                        v_a_6255_ = v___x_6281_;
                        state = 8;
                        continue;
                    } else {
                        v___x_6283_ = lean_nat_dec_le(v___x_6280_, v___x_6280_);
                        if v___x_6283_ == 0 {
                            if v___x_6282_ == 0 {
                                v___y_6254_ = v_a_6279_;
                                v_a_6255_ = v___x_6281_;
                                state = 8;
                                continue;
                            } else {
                                v___x_6284_ = 0usize;
                                v___x_6285_ = lean_usize_of_nat(v___x_6280_);
                                v___x_6286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_a_6279_, v___x_6284_, v___x_6285_, v___x_6281_, v_a_6210_, v_a_6211_, v_a_6212_, v_a_6213_);
                                v___y_6266_ = v_a_6279_;
                                v___y_6267_ = v___x_6286_;
                                state = 11;
                                continue;
                            }
                        } else {
                            v___x_6287_ = 0usize;
                            v___x_6288_ = lean_usize_of_nat(v___x_6280_);
                            v___x_6289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_a_6279_, v___x_6287_, v___x_6288_, v___x_6281_, v_a_6210_, v_a_6211_, v_a_6212_, v_a_6213_);
                            v___y_6266_ = v_a_6279_;
                            v___y_6267_ = v___x_6289_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    v___y_6223_ = v_a_6279_;
                    v___y_6224_ = v_a_6206_;
                    v___y_6225_ = v_a_6207_;
                    v___y_6226_ = v_a_6208_;
                    v___y_6227_ = v_a_6209_;
                    v___y_6228_ = v_a_6210_;
                    v___y_6229_ = v_a_6211_;
                    v___y_6230_ = v_a_6212_;
                    v___y_6231_ = v_a_6213_;
                    state = 2;
                    continue;
                }
            }
            15 => {
                if leanh::lean_obj_tag(v___y_6291_) == 0 {
                    v_a_6292_ = leanh::lean_ctor_get(v___y_6291_, 0);
                    leanh::lean_inc(v_a_6292_);
                    leanh::lean_dec_ref_known(v___y_6291_, 1);
                    v_a_6279_ = v_a_6292_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_6220_);
                    leanh::lean_dec(v_fst_6217_);
                    leanh::lean_dec(v_tagSuffix_6204_);
                    leanh::lean_dec(v_parentTag_6203_);
                    v_a_6293_ = leanh::lean_ctor_get(v___y_6291_, 0);
                    v_isSharedCheck_6300_ = (!leanh::lean_is_exclusive(v___y_6291_)) as u8;
                    if v_isSharedCheck_6300_ == 0 {
                        v___x_6295_ = v___y_6291_;
                        v_isShared_6296_ = v_isSharedCheck_6300_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6293_);
                        leanh::lean_dec(v___y_6291_);
                        v___x_6295_ = leanh::lean_box(0);
                        v_isShared_6296_ = v_isSharedCheck_6300_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_6296_ == 0 {
                    v___x_6298_ = v___x_6295_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6299_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6299_, 0, v_a_6293_);
                    v___x_6298_ = v_reuseFailAlloc_6299_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6298_;
            }
            18 => {
                if v_isShared_6315_ == 0 {
                    v___x_6317_ = v___x_6314_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6318_, 0, v_a_6312_);
                    v___x_6317_ = v_reuseFailAlloc_6318_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___boxed(
    mut v_k_6320_: *mut leanh::LeanObject,
    mut v_parentTag_6321_: *mut leanh::LeanObject,
    mut v_tagSuffix_6322_: *mut leanh::LeanObject,
    mut v_allowNaturalHoles_6323_: *mut leanh::LeanObject,
    mut v_a_6324_: *mut leanh::LeanObject,
    mut v_a_6325_: *mut leanh::LeanObject,
    mut v_a_6326_: *mut leanh::LeanObject,
    mut v_a_6327_: *mut leanh::LeanObject,
    mut v_a_6328_: *mut leanh::LeanObject,
    mut v_a_6329_: *mut leanh::LeanObject,
    mut v_a_6330_: *mut leanh::LeanObject,
    mut v_a_6331_: *mut leanh::LeanObject,
    mut v_a_6332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowNaturalHoles_boxed_6333_: u8 = 0;
    let mut v_res_6334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowNaturalHoles_boxed_6333_ = (leanh::lean_unbox(v_allowNaturalHoles_6323_) as u8);
    v_res_6334_ =
        l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(
            v_k_6320_,
            v_parentTag_6321_,
            v_tagSuffix_6322_,
            v_allowNaturalHoles_boxed_6333_,
            v_a_6324_,
            v_a_6325_,
            v_a_6326_,
            v_a_6327_,
            v_a_6328_,
            v_a_6329_,
            v_a_6330_,
            v_a_6331_,
        );
    leanh::lean_dec(v_a_6331_);
    leanh::lean_dec_ref(v_a_6330_);
    leanh::lean_dec(v_a_6329_);
    leanh::lean_dec_ref(v_a_6328_);
    leanh::lean_dec(v_a_6327_);
    leanh::lean_dec_ref(v_a_6326_);
    leanh::lean_dec(v_a_6325_);
    leanh::lean_dec_ref(v_a_6324_);
    return v_res_6334_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(
    mut v_as_6335_: *mut leanh::LeanObject,
    mut v_i_6336_: usize,
    mut v_stop_6337_: usize,
    mut v_b_6338_: *mut leanh::LeanObject,
    mut v___y_6339_: *mut leanh::LeanObject,
    mut v___y_6340_: *mut leanh::LeanObject,
    mut v___y_6341_: *mut leanh::LeanObject,
    mut v___y_6342_: *mut leanh::LeanObject,
    mut v___y_6343_: *mut leanh::LeanObject,
    mut v___y_6344_: *mut leanh::LeanObject,
    mut v___y_6345_: *mut leanh::LeanObject,
    mut v___y_6346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_as_6335_, v_i_6336_, v_stop_6337_, v_b_6338_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_);
    return v___x_6348_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___boxed(
    mut v_as_6349_: *mut leanh::LeanObject,
    mut v_i_6350_: *mut leanh::LeanObject,
    mut v_stop_6351_: *mut leanh::LeanObject,
    mut v_b_6352_: *mut leanh::LeanObject,
    mut v___y_6353_: *mut leanh::LeanObject,
    mut v___y_6354_: *mut leanh::LeanObject,
    mut v___y_6355_: *mut leanh::LeanObject,
    mut v___y_6356_: *mut leanh::LeanObject,
    mut v___y_6357_: *mut leanh::LeanObject,
    mut v___y_6358_: *mut leanh::LeanObject,
    mut v___y_6359_: *mut leanh::LeanObject,
    mut v___y_6360_: *mut leanh::LeanObject,
    mut v___y_6361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6362_: usize = 0;
    let mut v_stop_boxed_6363_: usize = 0;
    let mut v_res_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6362_ = leanh::lean_unbox_usize(v_i_6350_);
    leanh::lean_dec(v_i_6350_);
    v_stop_boxed_6363_ = leanh::lean_unbox_usize(v_stop_6351_);
    leanh::lean_dec(v_stop_6351_);
    v_res_6364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(v_as_6349_, v_i_boxed_6362_, v_stop_boxed_6363_, v_b_6352_, v___y_6353_, v___y_6354_, v___y_6355_, v___y_6356_, v___y_6357_, v___y_6358_, v___y_6359_, v___y_6360_);
    leanh::lean_dec(v___y_6360_);
    leanh::lean_dec_ref(v___y_6359_);
    leanh::lean_dec(v___y_6358_);
    leanh::lean_dec_ref(v___y_6357_);
    leanh::lean_dec(v___y_6356_);
    leanh::lean_dec_ref(v___y_6355_);
    leanh::lean_dec(v___y_6354_);
    leanh::lean_dec_ref(v___y_6353_);
    leanh::lean_dec_ref(v_as_6349_);
    return v_res_6364_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(
    mut v_as_6365_: *mut leanh::LeanObject,
    mut v_i_6366_: usize,
    mut v_stop_6367_: usize,
    mut v_b_6368_: *mut leanh::LeanObject,
    mut v___y_6369_: *mut leanh::LeanObject,
    mut v___y_6370_: *mut leanh::LeanObject,
    mut v___y_6371_: *mut leanh::LeanObject,
    mut v___y_6372_: *mut leanh::LeanObject,
    mut v___y_6373_: *mut leanh::LeanObject,
    mut v___y_6374_: *mut leanh::LeanObject,
    mut v___y_6375_: *mut leanh::LeanObject,
    mut v___y_6376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_as_6365_, v_i_6366_, v_stop_6367_, v_b_6368_, v___y_6371_, v___y_6372_, v___y_6373_, v___y_6374_, v___y_6375_, v___y_6376_);
    return v___x_6378_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___boxed(
    mut v_as_6379_: *mut leanh::LeanObject,
    mut v_i_6380_: *mut leanh::LeanObject,
    mut v_stop_6381_: *mut leanh::LeanObject,
    mut v_b_6382_: *mut leanh::LeanObject,
    mut v___y_6383_: *mut leanh::LeanObject,
    mut v___y_6384_: *mut leanh::LeanObject,
    mut v___y_6385_: *mut leanh::LeanObject,
    mut v___y_6386_: *mut leanh::LeanObject,
    mut v___y_6387_: *mut leanh::LeanObject,
    mut v___y_6388_: *mut leanh::LeanObject,
    mut v___y_6389_: *mut leanh::LeanObject,
    mut v___y_6390_: *mut leanh::LeanObject,
    mut v___y_6391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6392_: usize = 0;
    let mut v_stop_boxed_6393_: usize = 0;
    let mut v_res_6394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6392_ = leanh::lean_unbox_usize(v_i_6380_);
    leanh::lean_dec(v_i_6380_);
    v_stop_boxed_6393_ = leanh::lean_unbox_usize(v_stop_6381_);
    leanh::lean_dec(v_stop_6381_);
    v_res_6394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(v_as_6379_, v_i_boxed_6392_, v_stop_boxed_6393_, v_b_6382_, v___y_6383_, v___y_6384_, v___y_6385_, v___y_6386_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_);
    leanh::lean_dec(v___y_6390_);
    leanh::lean_dec_ref(v___y_6389_);
    leanh::lean_dec(v___y_6388_);
    leanh::lean_dec_ref(v___y_6387_);
    leanh::lean_dec(v___y_6386_);
    leanh::lean_dec_ref(v___y_6385_);
    leanh::lean_dec(v___y_6384_);
    leanh::lean_dec_ref(v___y_6383_);
    leanh::lean_dec_ref(v_as_6379_);
    return v_res_6394_;
}
pub unsafe fn l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(
    mut v_mvarIds_6395_: *mut leanh::LeanObject,
    mut v___y_6396_: *mut leanh::LeanObject,
    mut v___y_6397_: *mut leanh::LeanObject,
    mut v___y_6398_: *mut leanh::LeanObject,
    mut v___y_6399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6401_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_mvarIds_6395_, v___y_6397_);
    return v___x_6401_;
}
pub unsafe fn l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___boxed(
    mut v_mvarIds_6402_: *mut leanh::LeanObject,
    mut v___y_6403_: *mut leanh::LeanObject,
    mut v___y_6404_: *mut leanh::LeanObject,
    mut v___y_6405_: *mut leanh::LeanObject,
    mut v___y_6406_: *mut leanh::LeanObject,
    mut v___y_6407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6408_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(v_mvarIds_6402_, v___y_6403_, v___y_6404_, v___y_6405_, v___y_6406_);
    leanh::lean_dec(v___y_6406_);
    leanh::lean_dec_ref(v___y_6405_);
    leanh::lean_dec(v___y_6404_);
    leanh::lean_dec_ref(v___y_6403_);
    return v_res_6408_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(
    mut v___x_6409_: *mut leanh::LeanObject,
    mut v_n_6410_: *mut leanh::LeanObject,
    mut v_as_6411_: *mut leanh::LeanObject,
    mut v_lo_6412_: *mut leanh::LeanObject,
    mut v_hi_6413_: *mut leanh::LeanObject,
    mut v_w_6414_: *mut leanh::LeanObject,
    mut v_hlo_6415_: *mut leanh::LeanObject,
    mut v_hhi_6416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6417_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_6409_, v_n_6410_, v_as_6411_, v_lo_6412_, v_hi_6413_);
    return v___x_6417_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___boxed(
    mut v___x_6418_: *mut leanh::LeanObject,
    mut v_n_6419_: *mut leanh::LeanObject,
    mut v_as_6420_: *mut leanh::LeanObject,
    mut v_lo_6421_: *mut leanh::LeanObject,
    mut v_hi_6422_: *mut leanh::LeanObject,
    mut v_w_6423_: *mut leanh::LeanObject,
    mut v_hlo_6424_: *mut leanh::LeanObject,
    mut v_hhi_6425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6426_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(v___x_6418_, v_n_6419_, v_as_6420_, v_lo_6421_, v_hi_6422_, v_w_6423_, v_hlo_6424_, v_hhi_6425_);
    leanh::lean_dec(v_hi_6422_);
    leanh::lean_dec(v_n_6419_);
    leanh::lean_dec_ref(v___x_6418_);
    return v_res_6426_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(
    mut v___x_6427_: *mut leanh::LeanObject,
    mut v_n_6428_: *mut leanh::LeanObject,
    mut v_lo_6429_: *mut leanh::LeanObject,
    mut v_hi_6430_: *mut leanh::LeanObject,
    mut v_hhi_6431_: *mut leanh::LeanObject,
    mut v_pivot_6432_: *mut leanh::LeanObject,
    mut v_as_6433_: *mut leanh::LeanObject,
    mut v_i_6434_: *mut leanh::LeanObject,
    mut v_k_6435_: *mut leanh::LeanObject,
    mut v_ilo_6436_: *mut leanh::LeanObject,
    mut v_ik_6437_: *mut leanh::LeanObject,
    mut v_w_6438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6439_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_6427_, v_hi_6430_, v_pivot_6432_, v_as_6433_, v_i_6434_, v_k_6435_);
    return v___x_6439_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v___x_6440_: *mut leanh::LeanObject,
    mut v_n_6441_: *mut leanh::LeanObject,
    mut v_lo_6442_: *mut leanh::LeanObject,
    mut v_hi_6443_: *mut leanh::LeanObject,
    mut v_hhi_6444_: *mut leanh::LeanObject,
    mut v_pivot_6445_: *mut leanh::LeanObject,
    mut v_as_6446_: *mut leanh::LeanObject,
    mut v_i_6447_: *mut leanh::LeanObject,
    mut v_k_6448_: *mut leanh::LeanObject,
    mut v_ilo_6449_: *mut leanh::LeanObject,
    mut v_ik_6450_: *mut leanh::LeanObject,
    mut v_w_6451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6452_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(v___x_6440_, v_n_6441_, v_lo_6442_, v_hi_6443_, v_hhi_6444_, v_pivot_6445_, v_as_6446_, v_i_6447_, v_k_6448_, v_ilo_6449_, v_ik_6450_, v_w_6451_);
    leanh::lean_dec(v_hi_6443_);
    leanh::lean_dec(v_lo_6442_);
    leanh::lean_dec(v_n_6441_);
    leanh::lean_dec_ref(v___x_6440_);
    return v_res_6452_;
}
pub unsafe fn l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(
    mut v_k_6453_: *mut leanh::LeanObject,
    mut v_parentTag_6454_: *mut leanh::LeanObject,
    mut v_tagSuffix_6455_: *mut leanh::LeanObject,
    mut v_allowNaturalHoles_6456_: u8,
    mut v_a_6457_: *mut leanh::LeanObject,
    mut v_a_6458_: *mut leanh::LeanObject,
    mut v_a_6459_: *mut leanh::LeanObject,
    mut v_a_6460_: *mut leanh::LeanObject,
    mut v_a_6461_: *mut leanh::LeanObject,
    mut v_a_6462_: *mut leanh::LeanObject,
    mut v_a_6463_: *mut leanh::LeanObject,
    mut v_a_6464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_x3f_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_6468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mayPostpone_6469_: u8 = 0;
    let mut v_errToSorry_6470_: u8 = 0;
    let mut v_autoBoundImplicitContext_6471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicitForbidden_6472_: *mut leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_sectionVars_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sectionFVars_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_implicitLambda_6475_: u8 = 0;
    let mut v_heedElabAsElim_6476_: u8 = 0;
    let mut v_isNoncomputableSection_6477_: u8 = 0;
    let mut v_isMetaSection_6478_: u8 = 0;
    let mut v_ignoreTCFailures_6479_: u8 = 0;
    let mut v_inPattern_6480_: u8 = 0;
    let mut v_tacSnap_x3f_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveRecAppSyntax_6482_: u8 = 0;
    let mut v_holesAsSyntheticOpaque_6483_: u8 = 0;
    let mut v_checkDeprecated_6484_: u8 = 0;
    let mut v_fixedTermElabs_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6487_: u8 = 0;
    let mut v___x_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_6489_: u8 = 0;
    let mut v_ctxApprox_6490_: u8 = 0;
    let mut v_quasiPatternApprox_6491_: u8 = 0;
    let mut v_constApprox_6492_: u8 = 0;
    let mut v_isDefEqStuckEx_6493_: u8 = 0;
    let mut v_unificationHints_6494_: u8 = 0;
    let mut v_proofIrrelevance_6495_: u8 = 0;
    let mut v_offsetCnstrs_6496_: u8 = 0;
    let mut v_transparency_6497_: u8 = 0;
    let mut v_etaStruct_6498_: u8 = 0;
    let mut v_univApprox_6499_: u8 = 0;
    let mut v_iota_6500_: u8 = 0;
    let mut v_beta_6501_: u8 = 0;
    let mut v_proj_6502_: u8 = 0;
    let mut v_zeta_6503_: u8 = 0;
    let mut v_zetaDelta_6504_: u8 = 0;
    let mut v_zetaUnused_6505_: u8 = 0;
    let mut v_zetaHave_6506_: u8 = 0;
    let mut v___x_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6509_: u8 = 0;
    let mut v_trackZetaDelta_6510_: u8 = 0;
    let mut v_zetaDeltaSet_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_6513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_6517_: u8 = 0;
    let mut v_inTypeClassResolution_6518_: u8 = 0;
    let mut v_cacheInferType_6519_: u8 = 0;
    let mut v___x_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: u64 = 0;
    let mut v___x_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6530_: u8 = 0;
    let mut v___x_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6534_: u8 = 0;
    let mut v_reuseFailAlloc_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6536_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_allowNaturalHoles_6456_ == 0 {
                    v___x_6466_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_6453_, v_parentTag_6454_, v_tagSuffix_6455_, v_allowNaturalHoles_6456_, v_a_6457_, v_a_6458_, v_a_6459_, v_a_6460_, v_a_6461_, v_a_6462_, v_a_6463_, v_a_6464_);
                    return v___x_6466_;
                } else {
                    v_declName_x3f_6467_ = leanh::lean_ctor_get(v_a_6459_, 0);
                    v_macroStack_6468_ = leanh::lean_ctor_get(v_a_6459_, 1);
                    v_mayPostpone_6469_ = leanh::lean_ctor_get_uint8(
                        v_a_6459_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    v_errToSorry_6470_ = leanh::lean_ctor_get_uint8(
                        v_a_6459_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 1) as u32,
                    );
                    v_autoBoundImplicitContext_6471_ = leanh::lean_ctor_get(v_a_6459_, 2);
                    v_autoBoundImplicitForbidden_6472_ = leanh::lean_ctor_get(v_a_6459_, 3);
                    v_sectionVars_6473_ = leanh::lean_ctor_get(v_a_6459_, 4);
                    v_sectionFVars_6474_ = leanh::lean_ctor_get(v_a_6459_, 5);
                    v_implicitLambda_6475_ = leanh::lean_ctor_get_uint8(
                        v_a_6459_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                    );
                    v_heedElabAsElim_6476_ = leanh::lean_ctor_get_uint8(
                        v_a_6459_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 3) as u32,
                    );
                    v_isNoncomputableSection_6477_ = leanh::lean_ctor_get_uint8(
                        v_a_6459_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 4) as u32,
                    );
                    v_isMetaSection_6478_ = leanh::lean_ctor_get_uint8(
                        v_a_6459_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 5) as u32,
                    );
                    v_ignoreTCFailures_6479_ = leanh::lean_ctor_get_uint8(
                        v_a_6459_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 6) as u32,
                    );
                    v_inPattern_6480_ = leanh::lean_ctor_get_uint8(
                        v_a_6459_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 7) as u32,
                    );
                    v_tacSnap_x3f_6481_ = leanh::lean_ctor_get(v_a_6459_, 6);
                    v_saveRecAppSyntax_6482_ = leanh::lean_ctor_get_uint8(
                        v_a_6459_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 8) as u32,
                    );
                    v_holesAsSyntheticOpaque_6483_ = leanh::lean_ctor_get_uint8(
                        v_a_6459_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 9) as u32,
                    );
                    v_checkDeprecated_6484_ = leanh::lean_ctor_get_uint8(
                        v_a_6459_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 10) as u32,
                    );
                    v_fixedTermElabs_6485_ = leanh::lean_ctor_get(v_a_6459_, 7);
                    if v_holesAsSyntheticOpaque_6483_ == 0 {
                        v___y_6487_ = v_allowNaturalHoles_6456_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6487_ = v_holesAsSyntheticOpaque_6483_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6488_ = l_Lean_Meta_Context_config(v_a_6461_);
                v_foApprox_6489_ = leanh::lean_ctor_get_uint8(v___x_6488_, 0 as u32);
                v_ctxApprox_6490_ = leanh::lean_ctor_get_uint8(v___x_6488_, 1 as u32);
                v_quasiPatternApprox_6491_ =
                    leanh::lean_ctor_get_uint8(v___x_6488_, 2 as u32);
                v_constApprox_6492_ = leanh::lean_ctor_get_uint8(v___x_6488_, 3 as u32);
                v_isDefEqStuckEx_6493_ = leanh::lean_ctor_get_uint8(v___x_6488_, 4 as u32);
                v_unificationHints_6494_ = leanh::lean_ctor_get_uint8(v___x_6488_, 5 as u32);
                v_proofIrrelevance_6495_ = leanh::lean_ctor_get_uint8(v___x_6488_, 6 as u32);
                v_offsetCnstrs_6496_ = leanh::lean_ctor_get_uint8(v___x_6488_, 8 as u32);
                v_transparency_6497_ = leanh::lean_ctor_get_uint8(v___x_6488_, 9 as u32);
                v_etaStruct_6498_ = leanh::lean_ctor_get_uint8(v___x_6488_, 10 as u32);
                v_univApprox_6499_ = leanh::lean_ctor_get_uint8(v___x_6488_, 11 as u32);
                v_iota_6500_ = leanh::lean_ctor_get_uint8(v___x_6488_, 12 as u32);
                v_beta_6501_ = leanh::lean_ctor_get_uint8(v___x_6488_, 13 as u32);
                v_proj_6502_ = leanh::lean_ctor_get_uint8(v___x_6488_, 14 as u32);
                v_zeta_6503_ = leanh::lean_ctor_get_uint8(v___x_6488_, 15 as u32);
                v_zetaDelta_6504_ = leanh::lean_ctor_get_uint8(v___x_6488_, 16 as u32);
                v_zetaUnused_6505_ = leanh::lean_ctor_get_uint8(v___x_6488_, 17 as u32);
                v_zetaHave_6506_ = leanh::lean_ctor_get_uint8(v___x_6488_, 18 as u32);
                v_isSharedCheck_6536_ = (!leanh::lean_is_exclusive(v___x_6488_)) as u8;
                if v_isSharedCheck_6536_ == 0 {
                    v___x_6508_ = v___x_6488_;
                    v_isShared_6509_ = v_isSharedCheck_6536_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_6488_);
                    v___x_6508_ = leanh::lean_box(0);
                    v_isShared_6509_ = v_isSharedCheck_6536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_6510_ = leanh::lean_ctor_get_uint8(
                    v_a_6461_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_6511_ = leanh::lean_ctor_get(v_a_6461_, 1);
                v_lctx_6512_ = leanh::lean_ctor_get(v_a_6461_, 2);
                v_localInstances_6513_ = leanh::lean_ctor_get(v_a_6461_, 3);
                v_defEqCtx_x3f_6514_ = leanh::lean_ctor_get(v_a_6461_, 4);
                v_synthPendingDepth_6515_ = leanh::lean_ctor_get(v_a_6461_, 5);
                v_canUnfold_x3f_6516_ = leanh::lean_ctor_get(v_a_6461_, 6);
                v_univApprox_6517_ = leanh::lean_ctor_get_uint8(
                    v_a_6461_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_6518_ = leanh::lean_ctor_get_uint8(
                    v_a_6461_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_6519_ = leanh::lean_ctor_get_uint8(
                    v_a_6461_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_6509_ == 0 {
                    v___x_6521_ = v___x_6508_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6535_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        0 as u32,
                        v_foApprox_6489_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        1 as u32,
                        v_ctxApprox_6490_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        2 as u32,
                        v_quasiPatternApprox_6491_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        3 as u32,
                        v_constApprox_6492_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        4 as u32,
                        v_isDefEqStuckEx_6493_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        5 as u32,
                        v_unificationHints_6494_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        6 as u32,
                        v_proofIrrelevance_6495_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        8 as u32,
                        v_offsetCnstrs_6496_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        9 as u32,
                        v_transparency_6497_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        10 as u32,
                        v_etaStruct_6498_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        11 as u32,
                        v_univApprox_6499_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        12 as u32,
                        v_iota_6500_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        13 as u32,
                        v_beta_6501_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        14 as u32,
                        v_proj_6502_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        15 as u32,
                        v_zeta_6503_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        16 as u32,
                        v_zetaDelta_6504_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        17 as u32,
                        v_zetaUnused_6505_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6535_,
                        18 as u32,
                        v_zetaHave_6506_,
                    );
                    v___x_6521_ = v_reuseFailAlloc_6535_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(v___x_6521_, 7 as u32, v_allowNaturalHoles_6456_);
                v___x_6522_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6521_);
                leanh::lean_inc_ref(v_fixedTermElabs_6485_);
                leanh::lean_inc(v_tacSnap_x3f_6481_);
                leanh::lean_inc(v_sectionFVars_6474_);
                leanh::lean_inc(v_sectionVars_6473_);
                leanh::lean_inc_ref(v_autoBoundImplicitForbidden_6472_);
                leanh::lean_inc(v_autoBoundImplicitContext_6471_);
                leanh::lean_inc(v_macroStack_6468_);
                leanh::lean_inc(v_declName_x3f_6467_);
                v___x_6523_ = leanh::lean_alloc_ctor(0, 8, (11) as u32);
                leanh::lean_ctor_set(v___x_6523_, 0, v_declName_x3f_6467_);
                leanh::lean_ctor_set(v___x_6523_, 1, v_macroStack_6468_);
                leanh::lean_ctor_set(v___x_6523_, 2, v_autoBoundImplicitContext_6471_);
                leanh::lean_ctor_set(v___x_6523_, 3, v_autoBoundImplicitForbidden_6472_);
                leanh::lean_ctor_set(v___x_6523_, 4, v_sectionVars_6473_);
                leanh::lean_ctor_set(v___x_6523_, 5, v_sectionFVars_6474_);
                leanh::lean_ctor_set(v___x_6523_, 6, v_tacSnap_x3f_6481_);
                leanh::lean_ctor_set(v___x_6523_, 7, v_fixedTermElabs_6485_);
                leanh::lean_ctor_set_uint8(
                    v___x_6523_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    v_mayPostpone_6469_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6523_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 1) as u32,
                    v_errToSorry_6470_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6523_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                    v_implicitLambda_6475_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6523_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 3) as u32,
                    v_heedElabAsElim_6476_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6523_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 4) as u32,
                    v_isNoncomputableSection_6477_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6523_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 5) as u32,
                    v_isMetaSection_6478_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6523_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 6) as u32,
                    v_ignoreTCFailures_6479_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6523_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 7) as u32,
                    v_inPattern_6480_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6523_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 8) as u32,
                    v_saveRecAppSyntax_6482_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6523_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 9) as u32,
                    v___y_6487_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6523_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 10) as u32,
                    v_checkDeprecated_6484_,
                );
                v___x_6524_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_6524_, 0, v___x_6521_);
                leanh::lean_ctor_set_uint64(
                    v___x_6524_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_6522_,
                );
                leanh::lean_inc(v_canUnfold_x3f_6516_);
                leanh::lean_inc(v_synthPendingDepth_6515_);
                leanh::lean_inc(v_defEqCtx_x3f_6514_);
                leanh::lean_inc_ref(v_localInstances_6513_);
                leanh::lean_inc_ref(v_lctx_6512_);
                leanh::lean_inc(v_zetaDeltaSet_6511_);
                v___x_6525_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_6525_, 0, v___x_6524_);
                leanh::lean_ctor_set(v___x_6525_, 1, v_zetaDeltaSet_6511_);
                leanh::lean_ctor_set(v___x_6525_, 2, v_lctx_6512_);
                leanh::lean_ctor_set(v___x_6525_, 3, v_localInstances_6513_);
                leanh::lean_ctor_set(v___x_6525_, 4, v_defEqCtx_x3f_6514_);
                leanh::lean_ctor_set(v___x_6525_, 5, v_synthPendingDepth_6515_);
                leanh::lean_ctor_set(v___x_6525_, 6, v_canUnfold_x3f_6516_);
                leanh::lean_ctor_set_uint8(
                    v___x_6525_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_6510_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6525_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_6517_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6525_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_6518_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6525_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_6519_,
                );
                v___x_6526_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_6453_, v_parentTag_6454_, v_tagSuffix_6455_, v_allowNaturalHoles_6456_, v_a_6457_, v_a_6458_, v___x_6523_, v_a_6460_, v___x_6525_, v_a_6462_, v_a_6463_, v_a_6464_);
                leanh::lean_dec_ref_known(v___x_6525_, 7);
                leanh::lean_dec_ref_known(v___x_6523_, 8);
                if leanh::lean_obj_tag(v___x_6526_) == 0 {
                    v_a_6527_ = leanh::lean_ctor_get(v___x_6526_, 0);
                    v_isSharedCheck_6534_ = (!leanh::lean_is_exclusive(v___x_6526_)) as u8;
                    if v_isSharedCheck_6534_ == 0 {
                        v___x_6529_ = v___x_6526_;
                        v_isShared_6530_ = v_isSharedCheck_6534_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6527_);
                        leanh::lean_dec(v___x_6526_);
                        v___x_6529_ = leanh::lean_box(0);
                        v_isShared_6530_ = v_isSharedCheck_6534_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___x_6526_;
                }
            }
            4 => {
                if v_isShared_6530_ == 0 {
                    v___x_6532_ = v___x_6529_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6533_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6533_, 0, v_a_6527_);
                    v___x_6532_ = v_reuseFailAlloc_6533_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_withCollectingNewGoalsFrom___boxed(
    mut v_k_6537_: *mut leanh::LeanObject,
    mut v_parentTag_6538_: *mut leanh::LeanObject,
    mut v_tagSuffix_6539_: *mut leanh::LeanObject,
    mut v_allowNaturalHoles_6540_: *mut leanh::LeanObject,
    mut v_a_6541_: *mut leanh::LeanObject,
    mut v_a_6542_: *mut leanh::LeanObject,
    mut v_a_6543_: *mut leanh::LeanObject,
    mut v_a_6544_: *mut leanh::LeanObject,
    mut v_a_6545_: *mut leanh::LeanObject,
    mut v_a_6546_: *mut leanh::LeanObject,
    mut v_a_6547_: *mut leanh::LeanObject,
    mut v_a_6548_: *mut leanh::LeanObject,
    mut v_a_6549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowNaturalHoles_boxed_6550_: u8 = 0;
    let mut v_res_6551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowNaturalHoles_boxed_6550_ = (leanh::lean_unbox(v_allowNaturalHoles_6540_) as u8);
    v_res_6551_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(
        v_k_6537_,
        v_parentTag_6538_,
        v_tagSuffix_6539_,
        v_allowNaturalHoles_boxed_6550_,
        v_a_6541_,
        v_a_6542_,
        v_a_6543_,
        v_a_6544_,
        v_a_6545_,
        v_a_6546_,
        v_a_6547_,
        v_a_6548_,
    );
    leanh::lean_dec(v_a_6548_);
    leanh::lean_dec_ref(v_a_6547_);
    leanh::lean_dec(v_a_6546_);
    leanh::lean_dec_ref(v_a_6545_);
    leanh::lean_dec(v_a_6544_);
    leanh::lean_dec_ref(v_a_6543_);
    leanh::lean_dec(v_a_6542_);
    leanh::lean_dec_ref(v_a_6541_);
    return v_res_6551_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabTermWithHoles(
    mut v_stx_6552_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_6553_: *mut leanh::LeanObject,
    mut v_tagSuffix_6554_: *mut leanh::LeanObject,
    mut v_allowNaturalHoles_6555_: u8,
    mut v_parentTag_x3f_6556_: *mut leanh::LeanObject,
    mut v_a_6557_: *mut leanh::LeanObject,
    mut v_a_6558_: *mut leanh::LeanObject,
    mut v_a_6559_: *mut leanh::LeanObject,
    mut v_a_6560_: *mut leanh::LeanObject,
    mut v_a_6561_: *mut leanh::LeanObject,
    mut v_a_6562_: *mut leanh::LeanObject,
    mut v_a_6563_: *mut leanh::LeanObject,
    mut v_a_6564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: u8 = 0;
    let mut v___x_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6577_: u8 = 0;
    let mut v___x_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6581_: u8 = 0;
    let mut v_val_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_parentTag_x3f_6556_) == 0 {
                    v___x_6572_ = l_Lean_Elab_Tactic_getMainTag___redArg(
                        v_a_6558_, v_a_6561_, v_a_6562_, v_a_6563_, v_a_6564_,
                    );
                    if leanh::lean_obj_tag(v___x_6572_) == 0 {
                        v_a_6573_ = leanh::lean_ctor_get(v___x_6572_, 0);
                        leanh::lean_inc(v_a_6573_);
                        leanh::lean_dec_ref_known(v___x_6572_, 1);
                        v_a_6567_ = v_a_6573_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_tagSuffix_6554_);
                        leanh::lean_dec(v_expectedType_x3f_6553_);
                        leanh::lean_dec(v_stx_6552_);
                        v_a_6574_ = leanh::lean_ctor_get(v___x_6572_, 0);
                        v_isSharedCheck_6581_ =
                            (!leanh::lean_is_exclusive(v___x_6572_)) as u8;
                        if v_isSharedCheck_6581_ == 0 {
                            v___x_6576_ = v___x_6572_;
                            v_isShared_6577_ = v_isSharedCheck_6581_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6574_);
                            leanh::lean_dec(v___x_6572_);
                            v___x_6576_ = leanh::lean_box(0);
                            v_isShared_6577_ = v_isSharedCheck_6581_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_val_6582_ = leanh::lean_ctor_get(v_parentTag_x3f_6556_, 0);
                    leanh::lean_inc(v_val_6582_);
                    leanh::lean_dec_ref_known(v_parentTag_x3f_6556_, 1);
                    v_a_6567_ = v_val_6582_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6568_ = 0;
                v___x_6569_ = leanh::lean_box((v___x_6568_) as usize);
                v___x_6570_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    3,
                );
                leanh::lean_closure_set(v___x_6570_, 0, v_stx_6552_);
                leanh::lean_closure_set(v___x_6570_, 1, v_expectedType_x3f_6553_);
                leanh::lean_closure_set(v___x_6570_, 2, v___x_6569_);
                v___x_6571_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(
                    v___x_6570_,
                    v_a_6567_,
                    v_tagSuffix_6554_,
                    v_allowNaturalHoles_6555_,
                    v_a_6557_,
                    v_a_6558_,
                    v_a_6559_,
                    v_a_6560_,
                    v_a_6561_,
                    v_a_6562_,
                    v_a_6563_,
                    v_a_6564_,
                );
                return v___x_6571_;
            }
            2 => {
                if v_isShared_6577_ == 0 {
                    v___x_6579_ = v___x_6576_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6580_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6580_, 0, v_a_6574_);
                    v___x_6579_ = v_reuseFailAlloc_6580_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabTermWithHoles___boxed(
    mut v_stx_6583_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_6584_: *mut leanh::LeanObject,
    mut v_tagSuffix_6585_: *mut leanh::LeanObject,
    mut v_allowNaturalHoles_6586_: *mut leanh::LeanObject,
    mut v_parentTag_x3f_6587_: *mut leanh::LeanObject,
    mut v_a_6588_: *mut leanh::LeanObject,
    mut v_a_6589_: *mut leanh::LeanObject,
    mut v_a_6590_: *mut leanh::LeanObject,
    mut v_a_6591_: *mut leanh::LeanObject,
    mut v_a_6592_: *mut leanh::LeanObject,
    mut v_a_6593_: *mut leanh::LeanObject,
    mut v_a_6594_: *mut leanh::LeanObject,
    mut v_a_6595_: *mut leanh::LeanObject,
    mut v_a_6596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowNaturalHoles_boxed_6597_: u8 = 0;
    let mut v_res_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowNaturalHoles_boxed_6597_ = (leanh::lean_unbox(v_allowNaturalHoles_6586_) as u8);
    v_res_6598_ = l_Lean_Elab_Tactic_elabTermWithHoles(
        v_stx_6583_,
        v_expectedType_x3f_6584_,
        v_tagSuffix_6585_,
        v_allowNaturalHoles_boxed_6597_,
        v_parentTag_x3f_6587_,
        v_a_6588_,
        v_a_6589_,
        v_a_6590_,
        v_a_6591_,
        v_a_6592_,
        v_a_6593_,
        v_a_6594_,
        v_a_6595_,
    );
    leanh::lean_dec(v_a_6595_);
    leanh::lean_dec_ref(v_a_6594_);
    leanh::lean_dec(v_a_6593_);
    leanh::lean_dec_ref(v_a_6592_);
    leanh::lean_dec(v_a_6591_);
    leanh::lean_dec_ref(v_a_6590_);
    leanh::lean_dec(v_a_6589_);
    leanh::lean_dec_ref(v_a_6588_);
    return v_res_6598_;
}
pub unsafe fn l_Lean_Elab_Tactic_refineCore___lam__0(
    mut v_a_6599_: *mut leanh::LeanObject,
    mut v_x_6600_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6601_: u8 = 0;
    v___x_6601_ = l_Lean_instBEqMVarId_beq(v_x_6600_, v_a_6599_);
    return v___x_6601_;
}
pub unsafe fn l_Lean_Elab_Tactic_refineCore___lam__0___boxed(
    mut v_a_6602_: *mut leanh::LeanObject,
    mut v_x_6603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6604_: u8 = 0;
    let mut v_r_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6604_ = l_Lean_Elab_Tactic_refineCore___lam__0(v_a_6602_, v_x_6603_);
    leanh::lean_dec(v_x_6603_);
    leanh::lean_dec(v_a_6602_);
    v_r_6605_ = leanh::lean_box((v_res_6604_) as usize);
    return v_r_6605_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(
    mut v_x_6606_: *mut leanh::LeanObject,
    mut v_x_6607_: *mut leanh::LeanObject,
    mut v_x_6608_: *mut leanh::LeanObject,
    mut v_x_6609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_6610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6614_: u8 = 0;
    let mut v___x_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: u8 = 0;
    let mut v___x_6617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_6622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: u8 = 0;
    let mut v___x_6625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_6610_ = leanh::lean_ctor_get(v_x_6606_, 0);
                v_vs_6611_ = leanh::lean_ctor_get(v_x_6606_, 1);
                v_isSharedCheck_6635_ = (!leanh::lean_is_exclusive(v_x_6606_)) as u8;
                if v_isSharedCheck_6635_ == 0 {
                    v___x_6613_ = v_x_6606_;
                    v_isShared_6614_ = v_isSharedCheck_6635_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_6611_);
                    leanh::lean_inc(v_ks_6610_);
                    leanh::lean_dec(v_x_6606_);
                    v___x_6613_ = leanh::lean_box(0);
                    v_isShared_6614_ = v_isSharedCheck_6635_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6615_ = lean_array_get_size(v_ks_6610_);
                v___x_6616_ = lean_nat_dec_lt(v_x_6607_, v___x_6615_);
                if v___x_6616_ == 0 {
                    leanh::lean_dec(v_x_6607_);
                    v___x_6617_ = lean_array_push(v_ks_6610_, v_x_6608_);
                    v___x_6618_ = lean_array_push(v_vs_6611_, v_x_6609_);
                    if v_isShared_6614_ == 0 {
                        leanh::lean_ctor_set(v___x_6613_, 1, v___x_6618_);
                        leanh::lean_ctor_set(v___x_6613_, 0, v___x_6617_);
                        v___x_6620_ = v___x_6613_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6621_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6621_, 0, v___x_6617_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6621_, 1, v___x_6618_);
                        v___x_6620_ = v_reuseFailAlloc_6621_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_6622_ = lean_array_fget_borrowed(v_ks_6610_, v_x_6607_);
                    v___x_6623_ = l_Lean_instBEqMVarId_beq(v_x_6608_, v_k_x27_6622_);
                    if v___x_6623_ == 0 {
                        if v_isShared_6614_ == 0 {
                            v___x_6625_ = v___x_6613_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6629_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6629_, 0, v_ks_6610_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6629_, 1, v_vs_6611_);
                            v___x_6625_ = v_reuseFailAlloc_6629_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_6630_ = lean_array_fset(v_ks_6610_, v_x_6607_, v_x_6608_);
                        v___x_6631_ = lean_array_fset(v_vs_6611_, v_x_6607_, v_x_6609_);
                        leanh::lean_dec(v_x_6607_);
                        if v_isShared_6614_ == 0 {
                            leanh::lean_ctor_set(v___x_6613_, 1, v___x_6631_);
                            leanh::lean_ctor_set(v___x_6613_, 0, v___x_6630_);
                            v___x_6633_ = v___x_6613_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6634_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6634_, 0, v___x_6630_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6634_, 1, v___x_6631_);
                            v___x_6633_ = v_reuseFailAlloc_6634_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6620_;
            }
            3 => {
                v___x_6626_ = leanh::lean_unsigned_to_nat(1);
                v___x_6627_ = lean_nat_add(v_x_6607_, v___x_6626_);
                leanh::lean_dec(v_x_6607_);
                v_x_6606_ = v___x_6625_;
                v_x_6607_ = v___x_6627_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_6633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_n_6636_: *mut leanh::LeanObject,
    mut v_k_6637_: *mut leanh::LeanObject,
    mut v_v_6638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6639_ = leanh::lean_unsigned_to_nat(0);
    v___x_6640_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_n_6636_, v___x_6639_, v_k_6637_, v_v_6638_);
    return v___x_6640_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_6641_: usize = 0;
    let mut v___x_6642_: usize = 0;
    let mut v___x_6643_: usize = 0;
    v___x_6641_ = 5usize;
    v___x_6642_ = 1usize;
    v___x_6643_ = lean_usize_shift_left(v___x_6642_, v___x_6641_);
    return v___x_6643_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_6644_: usize = 0;
    let mut v___x_6645_: usize = 0;
    let mut v___x_6646_: usize = 0;
    v___x_6644_ = 1usize;
    v___x_6645_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_6646_ = lean_usize_sub(v___x_6645_, v___x_6644_);
    return v___x_6646_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6647_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6647_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(
    mut v_x_6648_: *mut leanh::LeanObject,
    mut v_x_6649_: usize,
    mut v_x_6650_: usize,
    mut v_x_6651_: *mut leanh::LeanObject,
    mut v_x_6652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_6653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: usize = 0;
    let mut v___x_6655_: usize = 0;
    let mut v___x_6656_: usize = 0;
    let mut v___x_6657_: usize = 0;
    let mut v_j_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: u8 = 0;
    let mut v___x_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6663_: u8 = 0;
    let mut v_v_6664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_6666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6677_: u8 = 0;
    let mut v___x_6678_: u8 = 0;
    let mut v___x_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6684_: u8 = 0;
    let mut v_node_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6688_: u8 = 0;
    let mut v___x_6689_: usize = 0;
    let mut v___x_6690_: usize = 0;
    let mut v___x_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6695_: u8 = 0;
    let mut v___x_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6697_: u8 = 0;
    let mut v_unused_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6703_: u8 = 0;
    let mut v___x_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6708_: u8 = 0;
    let mut v_ks_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_6710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: usize = 0;
    let mut v___x_6715_: u8 = 0;
    let mut v___x_6716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6718_: u8 = 0;
    let mut v_reuseFailAlloc_6719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6720_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6648_) == 0 {
                    v_es_6653_ = leanh::lean_ctor_get(v_x_6648_, 0);
                    v___x_6654_ = 5usize;
                    v___x_6655_ = 1usize;
                    v___x_6656_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_6657_ = lean_usize_land(v_x_6649_, v___x_6656_);
                    v_j_6658_ = lean_usize_to_nat(v___x_6657_);
                    v___x_6659_ = lean_array_get_size(v_es_6653_);
                    v___x_6660_ = lean_nat_dec_lt(v_j_6658_, v___x_6659_);
                    if v___x_6660_ == 0 {
                        leanh::lean_dec(v_j_6658_);
                        leanh::lean_dec(v_x_6652_);
                        leanh::lean_dec(v_x_6651_);
                        return v_x_6648_;
                    } else {
                        leanh::lean_inc_ref(v_es_6653_);
                        v_isSharedCheck_6697_ = (!leanh::lean_is_exclusive(v_x_6648_)) as u8;
                        if v_isSharedCheck_6697_ == 0 {
                            v_unused_6698_ = leanh::lean_ctor_get(v_x_6648_, 0);
                            leanh::lean_dec(v_unused_6698_);
                            v___x_6662_ = v_x_6648_;
                            v_isShared_6663_ = v_isSharedCheck_6697_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_6648_);
                            v___x_6662_ = leanh::lean_box(0);
                            v_isShared_6663_ = v_isSharedCheck_6697_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_6699_ = leanh::lean_ctor_get(v_x_6648_, 0);
                    v_vs_6700_ = leanh::lean_ctor_get(v_x_6648_, 1);
                    v_isSharedCheck_6720_ = (!leanh::lean_is_exclusive(v_x_6648_)) as u8;
                    if v_isSharedCheck_6720_ == 0 {
                        v___x_6702_ = v_x_6648_;
                        v_isShared_6703_ = v_isSharedCheck_6720_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_6700_);
                        leanh::lean_inc(v_ks_6699_);
                        leanh::lean_dec(v_x_6648_);
                        v___x_6702_ = leanh::lean_box(0);
                        v_isShared_6703_ = v_isSharedCheck_6720_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_6664_ = lean_array_fget(v_es_6653_, v_j_6658_);
                v___x_6665_ = leanh::lean_box(0);
                v_xs_x27_6666_ = lean_array_fset(v_es_6653_, v_j_6658_, v___x_6665_);
                match leanh::lean_obj_tag(v_v_6664_) {
                    0 => {
                        v_key_6673_ = leanh::lean_ctor_get(v_v_6664_, 0);
                        v_val_6674_ = leanh::lean_ctor_get(v_v_6664_, 1);
                        v_isSharedCheck_6684_ = (!leanh::lean_is_exclusive(v_v_6664_)) as u8;
                        if v_isSharedCheck_6684_ == 0 {
                            v___x_6676_ = v_v_6664_;
                            v_isShared_6677_ = v_isSharedCheck_6684_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_6674_);
                            leanh::lean_inc(v_key_6673_);
                            leanh::lean_dec(v_v_6664_);
                            v___x_6676_ = leanh::lean_box(0);
                            v_isShared_6677_ = v_isSharedCheck_6684_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_6685_ = leanh::lean_ctor_get(v_v_6664_, 0);
                        v_isSharedCheck_6695_ = (!leanh::lean_is_exclusive(v_v_6664_)) as u8;
                        if v_isSharedCheck_6695_ == 0 {
                            v___x_6687_ = v_v_6664_;
                            v_isShared_6688_ = v_isSharedCheck_6695_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_6685_);
                            leanh::lean_dec(v_v_6664_);
                            v___x_6687_ = leanh::lean_box(0);
                            v_isShared_6688_ = v_isSharedCheck_6695_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_6696_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6696_, 0, v_x_6651_);
                        leanh::lean_ctor_set(v___x_6696_, 1, v_x_6652_);
                        v___y_6668_ = v___x_6696_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6669_ = lean_array_fset(v_xs_x27_6666_, v_j_6658_, v___y_6668_);
                leanh::lean_dec(v_j_6658_);
                if v_isShared_6663_ == 0 {
                    leanh::lean_ctor_set(v___x_6662_, 0, v___x_6669_);
                    v___x_6671_ = v___x_6662_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6672_, 0, v___x_6669_);
                    v___x_6671_ = v_reuseFailAlloc_6672_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6671_;
            }
            4 => {
                v___x_6678_ = l_Lean_instBEqMVarId_beq(v_x_6651_, v_key_6673_);
                if v___x_6678_ == 0 {
                    leanh::lean_del_object(v___x_6676_);
                    v___x_6679_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_6673_,
                        v_val_6674_,
                        v_x_6651_,
                        v_x_6652_,
                    );
                    v___x_6680_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6680_, 0, v___x_6679_);
                    v___y_6668_ = v___x_6680_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_6674_);
                    leanh::lean_dec(v_key_6673_);
                    if v_isShared_6677_ == 0 {
                        leanh::lean_ctor_set(v___x_6676_, 1, v_x_6652_);
                        leanh::lean_ctor_set(v___x_6676_, 0, v_x_6651_);
                        v___x_6682_ = v___x_6676_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6683_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6683_, 0, v_x_6651_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6683_, 1, v_x_6652_);
                        v___x_6682_ = v_reuseFailAlloc_6683_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_6668_ = v___x_6682_;
                state = 2;
                continue;
            }
            6 => {
                v___x_6689_ = lean_usize_shift_right(v_x_6649_, v___x_6654_);
                v___x_6690_ = lean_usize_add(v_x_6650_, v___x_6655_);
                v___x_6691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_node_6685_, v___x_6689_, v___x_6690_, v_x_6651_, v_x_6652_);
                if v_isShared_6688_ == 0 {
                    leanh::lean_ctor_set(v___x_6687_, 0, v___x_6691_);
                    v___x_6693_ = v___x_6687_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6694_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6694_, 0, v___x_6691_);
                    v___x_6693_ = v_reuseFailAlloc_6694_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_6668_ = v___x_6693_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_6703_ == 0 {
                    v___x_6705_ = v___x_6702_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6719_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6719_, 0, v_ks_6699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6719_, 1, v_vs_6700_);
                    v___x_6705_ = v_reuseFailAlloc_6719_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_6706_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(v___x_6705_, v_x_6651_, v_x_6652_);
                v___x_6714_ = 7usize;
                v___x_6715_ = lean_usize_dec_le(v___x_6714_, v_x_6650_);
                if v___x_6715_ == 0 {
                    v___x_6716_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_6706_);
                    v___x_6717_ = leanh::lean_unsigned_to_nat(4);
                    v___x_6718_ = lean_nat_dec_lt(v___x_6716_, v___x_6717_);
                    leanh::lean_dec(v___x_6716_);
                    v___y_6708_ = v___x_6718_;
                    state = 10;
                    continue;
                } else {
                    v___y_6708_ = v___x_6715_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_6708_ == 0 {
                    v_ks_6709_ = leanh::lean_ctor_get(v_newNode_6706_, 0);
                    leanh::lean_inc_ref(v_ks_6709_);
                    v_vs_6710_ = leanh::lean_ctor_get(v_newNode_6706_, 1);
                    leanh::lean_inc_ref(v_vs_6710_);
                    leanh::lean_dec_ref(v_newNode_6706_);
                    v___x_6711_ = leanh::lean_unsigned_to_nat(0);
                    v___x_6712_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_6713_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_6650_, v_ks_6709_, v_vs_6710_, v___x_6711_, v___x_6712_);
                    leanh::lean_dec_ref(v_vs_6710_);
                    leanh::lean_dec_ref(v_ks_6709_);
                    return v___x_6713_;
                } else {
                    return v_newNode_6706_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_depth_6721_: usize,
    mut v_keys_6722_: *mut leanh::LeanObject,
    mut v_vals_6723_: *mut leanh::LeanObject,
    mut v_i_6724_: *mut leanh::LeanObject,
    mut v_entries_6725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: u8 = 0;
    let mut v_k_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: u64 = 0;
    let mut v_h_6731_: usize = 0;
    let mut v___x_6732_: usize = 0;
    let mut v___x_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: usize = 0;
    let mut v___x_6735_: usize = 0;
    let mut v___x_6736_: usize = 0;
    let mut v_h_6737_: usize = 0;
    let mut v___x_6738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6726_ = lean_array_get_size(v_keys_6722_);
                v___x_6727_ = lean_nat_dec_lt(v_i_6724_, v___x_6726_);
                if v___x_6727_ == 0 {
                    leanh::lean_dec(v_i_6724_);
                    return v_entries_6725_;
                } else {
                    v_k_6728_ = lean_array_fget_borrowed(v_keys_6722_, v_i_6724_);
                    v_v_6729_ = lean_array_fget_borrowed(v_vals_6723_, v_i_6724_);
                    v___x_6730_ = l_Lean_instHashableMVarId_hash(v_k_6728_);
                    v_h_6731_ = lean_uint64_to_usize(v___x_6730_);
                    v___x_6732_ = 5usize;
                    v___x_6733_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6734_ = 1usize;
                    v___x_6735_ = lean_usize_sub(v_depth_6721_, v___x_6734_);
                    v___x_6736_ = lean_usize_mul(v___x_6732_, v___x_6735_);
                    v_h_6737_ = lean_usize_shift_right(v_h_6731_, v___x_6736_);
                    v___x_6738_ = lean_nat_add(v_i_6724_, v___x_6733_);
                    leanh::lean_dec(v_i_6724_);
                    leanh::lean_inc(v_v_6729_);
                    leanh::lean_inc(v_k_6728_);
                    v___x_6739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_entries_6725_, v_h_6737_, v_depth_6721_, v_k_6728_, v_v_6729_);
                    v_i_6724_ = v___x_6738_;
                    v_entries_6725_ = v___x_6739_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_depth_6741_: *mut leanh::LeanObject,
    mut v_keys_6742_: *mut leanh::LeanObject,
    mut v_vals_6743_: *mut leanh::LeanObject,
    mut v_i_6744_: *mut leanh::LeanObject,
    mut v_entries_6745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_6746_: usize = 0;
    let mut v_res_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_6746_ = leanh::lean_unbox_usize(v_depth_6741_);
    leanh::lean_dec(v_depth_6741_);
    v_res_6747_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_boxed_6746_, v_keys_6742_, v_vals_6743_, v_i_6744_, v_entries_6745_);
    leanh::lean_dec_ref(v_vals_6743_);
    leanh::lean_dec_ref(v_keys_6742_);
    return v_res_6747_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_6748_: *mut leanh::LeanObject,
    mut v_x_6749_: *mut leanh::LeanObject,
    mut v_x_6750_: *mut leanh::LeanObject,
    mut v_x_6751_: *mut leanh::LeanObject,
    mut v_x_6752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3854__boxed_6753_: usize = 0;
    let mut v_x_3855__boxed_6754_: usize = 0;
    let mut v_res_6755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3854__boxed_6753_ = leanh::lean_unbox_usize(v_x_6749_);
    leanh::lean_dec(v_x_6749_);
    v_x_3855__boxed_6754_ = leanh::lean_unbox_usize(v_x_6750_);
    leanh::lean_dec(v_x_6750_);
    v_res_6755_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_6748_, v_x_3854__boxed_6753_, v_x_3855__boxed_6754_, v_x_6751_, v_x_6752_);
    return v_res_6755_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(
    mut v_x_6756_: *mut leanh::LeanObject,
    mut v_x_6757_: *mut leanh::LeanObject,
    mut v_x_6758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6759_: u64 = 0;
    let mut v___x_6760_: usize = 0;
    let mut v___x_6761_: usize = 0;
    let mut v___x_6762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6759_ = l_Lean_instHashableMVarId_hash(v_x_6757_);
    v___x_6760_ = lean_uint64_to_usize(v___x_6759_);
    v___x_6761_ = 1usize;
    v___x_6762_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_6756_, v___x_6760_, v___x_6761_, v_x_6757_, v_x_6758_);
    return v___x_6762_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(
    mut v_mvarId_6763_: *mut leanh::LeanObject,
    mut v_val_6764_: *mut leanh::LeanObject,
    mut v___y_6765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6775_: u8 = 0;
    let mut v_depth_6776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_6779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_6780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_6783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_6784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_6785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6788_: u8 = 0;
    let mut v___x_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6799_: u8 = 0;
    let mut v_isSharedCheck_6800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6767_ = lean_st_ref_take(v___y_6765_);
                v_mctx_6768_ = leanh::lean_ctor_get(v___x_6767_, 0);
                v_cache_6769_ = leanh::lean_ctor_get(v___x_6767_, 1);
                v_zetaDeltaFVarIds_6770_ = leanh::lean_ctor_get(v___x_6767_, 2);
                v_postponed_6771_ = leanh::lean_ctor_get(v___x_6767_, 3);
                v_diag_6772_ = leanh::lean_ctor_get(v___x_6767_, 4);
                v_isSharedCheck_6800_ = (!leanh::lean_is_exclusive(v___x_6767_)) as u8;
                if v_isSharedCheck_6800_ == 0 {
                    v___x_6774_ = v___x_6767_;
                    v_isShared_6775_ = v_isSharedCheck_6800_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_6772_);
                    leanh::lean_inc(v_postponed_6771_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_6770_);
                    leanh::lean_inc(v_cache_6769_);
                    leanh::lean_inc(v_mctx_6768_);
                    leanh::lean_dec(v___x_6767_);
                    v___x_6774_ = leanh::lean_box(0);
                    v_isShared_6775_ = v_isSharedCheck_6800_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_6776_ = leanh::lean_ctor_get(v_mctx_6768_, 0);
                v_levelAssignDepth_6777_ = leanh::lean_ctor_get(v_mctx_6768_, 1);
                v_lmvarCounter_6778_ = leanh::lean_ctor_get(v_mctx_6768_, 2);
                v_mvarCounter_6779_ = leanh::lean_ctor_get(v_mctx_6768_, 3);
                v_lDecls_6780_ = leanh::lean_ctor_get(v_mctx_6768_, 4);
                v_decls_6781_ = leanh::lean_ctor_get(v_mctx_6768_, 5);
                v_userNames_6782_ = leanh::lean_ctor_get(v_mctx_6768_, 6);
                v_lAssignment_6783_ = leanh::lean_ctor_get(v_mctx_6768_, 7);
                v_eAssignment_6784_ = leanh::lean_ctor_get(v_mctx_6768_, 8);
                v_dAssignment_6785_ = leanh::lean_ctor_get(v_mctx_6768_, 9);
                v_isSharedCheck_6799_ = (!leanh::lean_is_exclusive(v_mctx_6768_)) as u8;
                if v_isSharedCheck_6799_ == 0 {
                    v___x_6787_ = v_mctx_6768_;
                    v_isShared_6788_ = v_isSharedCheck_6799_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_6785_);
                    leanh::lean_inc(v_eAssignment_6784_);
                    leanh::lean_inc(v_lAssignment_6783_);
                    leanh::lean_inc(v_userNames_6782_);
                    leanh::lean_inc(v_decls_6781_);
                    leanh::lean_inc(v_lDecls_6780_);
                    leanh::lean_inc(v_mvarCounter_6779_);
                    leanh::lean_inc(v_lmvarCounter_6778_);
                    leanh::lean_inc(v_levelAssignDepth_6777_);
                    leanh::lean_inc(v_depth_6776_);
                    leanh::lean_dec(v_mctx_6768_);
                    v___x_6787_ = leanh::lean_box(0);
                    v_isShared_6788_ = v_isSharedCheck_6799_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6789_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(v_eAssignment_6784_, v_mvarId_6763_, v_val_6764_);
                if v_isShared_6788_ == 0 {
                    leanh::lean_ctor_set(v___x_6787_, 8, v___x_6789_);
                    v___x_6791_ = v___x_6787_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6798_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6798_, 0, v_depth_6776_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6798_,
                        1,
                        v_levelAssignDepth_6777_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6798_, 2, v_lmvarCounter_6778_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6798_, 3, v_mvarCounter_6779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6798_, 4, v_lDecls_6780_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6798_, 5, v_decls_6781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6798_, 6, v_userNames_6782_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6798_, 7, v_lAssignment_6783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6798_, 8, v___x_6789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6798_, 9, v_dAssignment_6785_);
                    v___x_6791_ = v_reuseFailAlloc_6798_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6775_ == 0 {
                    leanh::lean_ctor_set(v___x_6774_, 0, v___x_6791_);
                    v___x_6793_ = v___x_6774_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6797_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6797_, 0, v___x_6791_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6797_, 1, v_cache_6769_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6797_,
                        2,
                        v_zetaDeltaFVarIds_6770_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6797_, 3, v_postponed_6771_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6797_, 4, v_diag_6772_);
                    v___x_6793_ = v_reuseFailAlloc_6797_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6794_ = lean_st_ref_set(v___y_6765_, v___x_6793_);
                v___x_6795_ = leanh::lean_box(0);
                v___x_6796_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6796_, 0, v___x_6795_);
                return v___x_6796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg___boxed(
    mut v_mvarId_6801_: *mut leanh::LeanObject,
    mut v_val_6802_: *mut leanh::LeanObject,
    mut v___y_6803_: *mut leanh::LeanObject,
    mut v___y_6804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6805_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(
        v_mvarId_6801_,
        v_val_6802_,
        v___y_6803_,
    );
    leanh::lean_dec(v___y_6803_);
    return v_res_6805_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(
    mut v_msgData_6806_: *mut leanh::LeanObject,
    mut v___y_6807_: *mut leanh::LeanObject,
    mut v___y_6808_: *mut leanh::LeanObject,
    mut v___y_6809_: *mut leanh::LeanObject,
    mut v___y_6810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6812_ = lean_st_ref_get(v___y_6810_);
    v_env_6813_ = leanh::lean_ctor_get(v___x_6812_, 0);
    leanh::lean_inc_ref(v_env_6813_);
    leanh::lean_dec(v___x_6812_);
    v___x_6814_ = lean_st_ref_get(v___y_6808_);
    v_mctx_6815_ = leanh::lean_ctor_get(v___x_6814_, 0);
    leanh::lean_inc_ref(v_mctx_6815_);
    leanh::lean_dec(v___x_6814_);
    v_lctx_6816_ = leanh::lean_ctor_get(v___y_6807_, 2);
    v_options_6817_ = leanh::lean_ctor_get(v___y_6809_, 2);
    leanh::lean_inc_ref(v_options_6817_);
    leanh::lean_inc_ref(v_lctx_6816_);
    v___x_6818_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_6818_, 0, v_env_6813_);
    leanh::lean_ctor_set(v___x_6818_, 1, v_mctx_6815_);
    leanh::lean_ctor_set(v___x_6818_, 2, v_lctx_6816_);
    leanh::lean_ctor_set(v___x_6818_, 3, v_options_6817_);
    v___x_6819_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6819_, 0, v___x_6818_);
    leanh::lean_ctor_set(v___x_6819_, 1, v_msgData_6806_);
    v___x_6820_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6820_, 0, v___x_6819_);
    return v___x_6820_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2___boxed(
    mut v_msgData_6821_: *mut leanh::LeanObject,
    mut v___y_6822_: *mut leanh::LeanObject,
    mut v___y_6823_: *mut leanh::LeanObject,
    mut v___y_6824_: *mut leanh::LeanObject,
    mut v___y_6825_: *mut leanh::LeanObject,
    mut v___y_6826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6827_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msgData_6821_, v___y_6822_, v___y_6823_, v___y_6824_, v___y_6825_);
    leanh::lean_dec(v___y_6825_);
    leanh::lean_dec_ref(v___y_6824_);
    leanh::lean_dec(v___y_6823_);
    leanh::lean_dec_ref(v___y_6822_);
    return v_res_6827_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(
    mut v_msg_6828_: *mut leanh::LeanObject,
    mut v___y_6829_: *mut leanh::LeanObject,
    mut v___y_6830_: *mut leanh::LeanObject,
    mut v___y_6831_: *mut leanh::LeanObject,
    mut v___y_6832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6839_: u8 = 0;
    let mut v___x_6840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6844_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6834_ = leanh::lean_ctor_get(v___y_6831_, 5);
                v___x_6835_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msg_6828_, v___y_6829_, v___y_6830_, v___y_6831_, v___y_6832_);
                v_a_6836_ = leanh::lean_ctor_get(v___x_6835_, 0);
                v_isSharedCheck_6844_ = (!leanh::lean_is_exclusive(v___x_6835_)) as u8;
                if v_isSharedCheck_6844_ == 0 {
                    v___x_6838_ = v___x_6835_;
                    v_isShared_6839_ = v_isSharedCheck_6844_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6836_);
                    leanh::lean_dec(v___x_6835_);
                    v___x_6838_ = leanh::lean_box(0);
                    v_isShared_6839_ = v_isSharedCheck_6844_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_6834_);
                v___x_6840_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6840_, 0, v_ref_6834_);
                leanh::lean_ctor_set(v___x_6840_, 1, v_a_6836_);
                if v_isShared_6839_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6838_, 1);
                    leanh::lean_ctor_set(v___x_6838_, 0, v___x_6840_);
                    v___x_6842_ = v___x_6838_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6843_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6843_, 0, v___x_6840_);
                    v___x_6842_ = v_reuseFailAlloc_6843_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg___boxed(
    mut v_msg_6845_: *mut leanh::LeanObject,
    mut v___y_6846_: *mut leanh::LeanObject,
    mut v___y_6847_: *mut leanh::LeanObject,
    mut v___y_6848_: *mut leanh::LeanObject,
    mut v___y_6849_: *mut leanh::LeanObject,
    mut v___y_6850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6851_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(
        v_msg_6845_,
        v___y_6846_,
        v___y_6847_,
        v___y_6848_,
        v___y_6849_,
    );
    leanh::lean_dec(v___y_6849_);
    leanh::lean_dec_ref(v___y_6848_);
    leanh::lean_dec(v___y_6847_);
    leanh::lean_dec_ref(v___y_6846_);
    return v_res_6851_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6853_ = l_Lean_Elab_Tactic_refineCore___lam__1___closed__0;
    v___x_6854_ = l_Lean_stringToMessageData(v___x_6853_);
    return v___x_6854_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6856_ = l_Lean_Elab_Tactic_refineCore___lam__1___closed__2;
    v___x_6857_ = l_Lean_stringToMessageData(v___x_6856_);
    return v___x_6857_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_6859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6859_ = l_Lean_Elab_Tactic_refineCore___lam__1___closed__4;
    v___x_6860_ = l_Lean_stringToMessageData(v___x_6859_);
    return v___x_6860_;
}
pub unsafe fn l_Lean_Elab_Tactic_refineCore___lam__1(
    mut v_stx_6861_: *mut leanh::LeanObject,
    mut v_tagSuffix_6862_: *mut leanh::LeanObject,
    mut v_allowNaturalHoles_6863_: u8,
    mut v___y_6864_: *mut leanh::LeanObject,
    mut v___y_6865_: *mut leanh::LeanObject,
    mut v___y_6866_: *mut leanh::LeanObject,
    mut v___y_6867_: *mut leanh::LeanObject,
    mut v___y_6868_: *mut leanh::LeanObject,
    mut v___y_6869_: *mut leanh::LeanObject,
    mut v___y_6870_: *mut leanh::LeanObject,
    mut v___y_6871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6883_: u8 = 0;
    let mut v___x_6884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: u8 = 0;
    let mut v___f_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6921_: u8 = 0;
    let mut v___x_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6925_: u8 = 0;
    let mut v_isSharedCheck_6926_: u8 = 0;
    let mut v_a_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6930_: u8 = 0;
    let mut v___x_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6934_: u8 = 0;
    let mut v_a_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6938_: u8 = 0;
    let mut v___x_6940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6873_ = l_Lean_Elab_Tactic_getMainTarget(
                    v___y_6864_,
                    v___y_6865_,
                    v___y_6866_,
                    v___y_6867_,
                    v___y_6868_,
                    v___y_6869_,
                    v___y_6870_,
                    v___y_6871_,
                );
                if leanh::lean_obj_tag(v___x_6873_) == 0 {
                    v_a_6874_ = leanh::lean_ctor_get(v___x_6873_, 0);
                    leanh::lean_inc(v_a_6874_);
                    leanh::lean_dec_ref_known(v___x_6873_, 1);
                    v___x_6875_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6875_, 0, v_a_6874_);
                    v___x_6876_ = leanh::lean_box(0);
                    v___x_6877_ = l_Lean_Elab_Tactic_elabTermWithHoles(
                        v_stx_6861_,
                        v___x_6875_,
                        v_tagSuffix_6862_,
                        v_allowNaturalHoles_6863_,
                        v___x_6876_,
                        v___y_6864_,
                        v___y_6865_,
                        v___y_6866_,
                        v___y_6867_,
                        v___y_6868_,
                        v___y_6869_,
                        v___y_6870_,
                        v___y_6871_,
                    );
                    if leanh::lean_obj_tag(v___x_6877_) == 0 {
                        v_a_6878_ = leanh::lean_ctor_get(v___x_6877_, 0);
                        leanh::lean_inc(v_a_6878_);
                        leanh::lean_dec_ref_known(v___x_6877_, 1);
                        v_fst_6879_ = leanh::lean_ctor_get(v_a_6878_, 0);
                        v_snd_6880_ = leanh::lean_ctor_get(v_a_6878_, 1);
                        v_isSharedCheck_6926_ = (!leanh::lean_is_exclusive(v_a_6878_)) as u8;
                        if v_isSharedCheck_6926_ == 0 {
                            v___x_6882_ = v_a_6878_;
                            v_isShared_6883_ = v_isSharedCheck_6926_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_6880_);
                            leanh::lean_inc(v_fst_6879_);
                            leanh::lean_dec(v_a_6878_);
                            v___x_6882_ = leanh::lean_box(0);
                            v_isShared_6883_ = v_isSharedCheck_6926_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6927_ = leanh::lean_ctor_get(v___x_6877_, 0);
                        v_isSharedCheck_6934_ =
                            (!leanh::lean_is_exclusive(v___x_6877_)) as u8;
                        if v_isSharedCheck_6934_ == 0 {
                            v___x_6929_ = v___x_6877_;
                            v_isShared_6930_ = v_isSharedCheck_6934_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6927_);
                            leanh::lean_dec(v___x_6877_);
                            v___x_6929_ = leanh::lean_box(0);
                            v_isShared_6930_ = v_isSharedCheck_6934_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_tagSuffix_6862_);
                    leanh::lean_dec(v_stx_6861_);
                    v_a_6935_ = leanh::lean_ctor_get(v___x_6873_, 0);
                    v_isSharedCheck_6942_ = (!leanh::lean_is_exclusive(v___x_6873_)) as u8;
                    if v_isSharedCheck_6942_ == 0 {
                        v___x_6937_ = v___x_6873_;
                        v_isShared_6938_ = v_isSharedCheck_6942_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6935_);
                        leanh::lean_dec(v___x_6873_);
                        v___x_6937_ = leanh::lean_box(0);
                        v_isShared_6938_ = v_isSharedCheck_6942_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6884_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_6865_,
                    v___y_6868_,
                    v___y_6869_,
                    v___y_6870_,
                    v___y_6871_,
                );
                if leanh::lean_obj_tag(v___x_6884_) == 0 {
                    v_a_6885_ = leanh::lean_ctor_get(v___x_6884_, 0);
                    leanh::lean_inc_n(v_a_6885_, 2);
                    leanh::lean_dec_ref_known(v___x_6884_, 1);
                    v___x_6886_ =
                        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(
                            v_fst_6879_,
                            v___y_6869_,
                        );
                    v_a_6887_ = leanh::lean_ctor_get(v___x_6886_, 0);
                    leanh::lean_inc(v_a_6887_);
                    leanh::lean_dec_ref(v___x_6886_);
                    v___x_6899_ = l_Lean_mkMVar(v_a_6885_);
                    v___x_6913_ = lean_expr_eqv(v_a_6887_, v___x_6899_);
                    if v___x_6913_ == 0 {
                        leanh::lean_inc(v_a_6885_);
                        v___f_6914_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_refineCore___lam__0___boxed
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v___f_6914_, 0, v_a_6885_);
                        leanh::lean_inc(v_a_6887_);
                        v___x_6915_ = l_Lean_FindMVar_main(v___f_6914_, v_a_6887_, v___x_6876_);
                        if leanh::lean_obj_tag(v___x_6915_) == 1 {
                            leanh::lean_dec_ref_known(v___x_6915_, 1);
                            leanh::lean_dec(v_a_6885_);
                            leanh::lean_dec(v_snd_6880_);
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_6915_);
                            if v___x_6913_ == 0 {
                                leanh::lean_dec_ref(v___x_6899_);
                                leanh::lean_del_object(v___x_6882_);
                                v___y_6889_ = v___y_6864_;
                                v___y_6890_ = v___y_6865_;
                                v___y_6891_ = v___y_6866_;
                                v___y_6892_ = v___y_6867_;
                                v___y_6893_ = v___y_6868_;
                                v___y_6894_ = v___y_6869_;
                                v___y_6895_ = v___y_6870_;
                                v___y_6896_ = v___y_6871_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_6885_);
                                leanh::lean_dec(v_snd_6880_);
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_6899_);
                        leanh::lean_dec(v_a_6887_);
                        leanh::lean_del_object(v___x_6882_);
                        v___x_6916_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6916_, 0, v_a_6885_);
                        leanh::lean_ctor_set(v___x_6916_, 1, v_snd_6880_);
                        v___x_6917_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_6916_,
                            v___y_6865_,
                            v___y_6868_,
                            v___y_6869_,
                            v___y_6870_,
                            v___y_6871_,
                        );
                        return v___x_6917_;
                    }
                } else {
                    leanh::lean_del_object(v___x_6882_);
                    leanh::lean_dec(v_snd_6880_);
                    leanh::lean_dec(v_fst_6879_);
                    v_a_6918_ = leanh::lean_ctor_get(v___x_6884_, 0);
                    v_isSharedCheck_6925_ = (!leanh::lean_is_exclusive(v___x_6884_)) as u8;
                    if v_isSharedCheck_6925_ == 0 {
                        v___x_6920_ = v___x_6884_;
                        v_isShared_6921_ = v_isSharedCheck_6925_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6918_);
                        leanh::lean_dec(v___x_6884_);
                        v___x_6920_ = leanh::lean_box(0);
                        v_isShared_6921_ = v_isSharedCheck_6925_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6897_ =
                    l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(
                        v_a_6885_,
                        v_a_6887_,
                        v___y_6894_,
                    );
                leanh::lean_dec_ref(v___x_6897_);
                v___x_6898_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v_snd_6880_,
                    v___y_6890_,
                    v___y_6893_,
                    v___y_6894_,
                    v___y_6895_,
                    v___y_6896_,
                );
                return v___x_6898_;
            }
            3 => {
                v___x_6901_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_refineCore___lam__1___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_refineCore___lam__1___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__1,
                );
                v___x_6902_ = l_Lean_indentExpr(v_a_6887_);
                if v_isShared_6883_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6882_, 7);
                    leanh::lean_ctor_set(v___x_6882_, 1, v___x_6902_);
                    leanh::lean_ctor_set(v___x_6882_, 0, v___x_6901_);
                    v___x_6904_ = v___x_6882_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6912_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6912_, 0, v___x_6901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6912_, 1, v___x_6902_);
                    v___x_6904_ = v_reuseFailAlloc_6912_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6905_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_refineCore___lam__1___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_refineCore___lam__1___closed__3_once
                    ),
                    _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__3,
                );
                v___x_6906_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6906_, 0, v___x_6904_);
                leanh::lean_ctor_set(v___x_6906_, 1, v___x_6905_);
                v___x_6907_ = l_Lean_MessageData_ofExpr(v___x_6899_);
                v___x_6908_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6908_, 0, v___x_6906_);
                leanh::lean_ctor_set(v___x_6908_, 1, v___x_6907_);
                v___x_6909_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_refineCore___lam__1___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once
                    ),
                    _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5,
                );
                v___x_6910_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6910_, 0, v___x_6908_);
                leanh::lean_ctor_set(v___x_6910_, 1, v___x_6909_);
                v___x_6911_ =
                    l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(
                        v___x_6910_,
                        v___y_6868_,
                        v___y_6869_,
                        v___y_6870_,
                        v___y_6871_,
                    );
                return v___x_6911_;
            }
            5 => {
                if v_isShared_6921_ == 0 {
                    v___x_6923_ = v___x_6920_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6924_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6924_, 0, v_a_6918_);
                    v___x_6923_ = v_reuseFailAlloc_6924_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6923_;
            }
            7 => {
                if v_isShared_6930_ == 0 {
                    v___x_6932_ = v___x_6929_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6933_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6933_, 0, v_a_6927_);
                    v___x_6932_ = v_reuseFailAlloc_6933_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6932_;
            }
            9 => {
                if v_isShared_6938_ == 0 {
                    v___x_6940_ = v___x_6937_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6941_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6941_, 0, v_a_6935_);
                    v___x_6940_ = v_reuseFailAlloc_6941_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_refineCore___lam__1___boxed(
    mut v_stx_6943_: *mut leanh::LeanObject,
    mut v_tagSuffix_6944_: *mut leanh::LeanObject,
    mut v_allowNaturalHoles_6945_: *mut leanh::LeanObject,
    mut v___y_6946_: *mut leanh::LeanObject,
    mut v___y_6947_: *mut leanh::LeanObject,
    mut v___y_6948_: *mut leanh::LeanObject,
    mut v___y_6949_: *mut leanh::LeanObject,
    mut v___y_6950_: *mut leanh::LeanObject,
    mut v___y_6951_: *mut leanh::LeanObject,
    mut v___y_6952_: *mut leanh::LeanObject,
    mut v___y_6953_: *mut leanh::LeanObject,
    mut v___y_6954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowNaturalHoles_boxed_6955_: u8 = 0;
    let mut v_res_6956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowNaturalHoles_boxed_6955_ = (leanh::lean_unbox(v_allowNaturalHoles_6945_) as u8);
    v_res_6956_ = l_Lean_Elab_Tactic_refineCore___lam__1(
        v_stx_6943_,
        v_tagSuffix_6944_,
        v_allowNaturalHoles_boxed_6955_,
        v___y_6946_,
        v___y_6947_,
        v___y_6948_,
        v___y_6949_,
        v___y_6950_,
        v___y_6951_,
        v___y_6952_,
        v___y_6953_,
    );
    leanh::lean_dec(v___y_6953_);
    leanh::lean_dec_ref(v___y_6952_);
    leanh::lean_dec(v___y_6951_);
    leanh::lean_dec_ref(v___y_6950_);
    leanh::lean_dec(v___y_6949_);
    leanh::lean_dec_ref(v___y_6948_);
    leanh::lean_dec(v___y_6947_);
    leanh::lean_dec_ref(v___y_6946_);
    return v_res_6956_;
}
pub unsafe fn l_Lean_Elab_Tactic_refineCore(
    mut v_stx_6957_: *mut leanh::LeanObject,
    mut v_tagSuffix_6958_: *mut leanh::LeanObject,
    mut v_allowNaturalHoles_6959_: u8,
    mut v_a_6960_: *mut leanh::LeanObject,
    mut v_a_6961_: *mut leanh::LeanObject,
    mut v_a_6962_: *mut leanh::LeanObject,
    mut v_a_6963_: *mut leanh::LeanObject,
    mut v_a_6964_: *mut leanh::LeanObject,
    mut v_a_6965_: *mut leanh::LeanObject,
    mut v_a_6966_: *mut leanh::LeanObject,
    mut v_a_6967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6969_ = leanh::lean_box((v_allowNaturalHoles_6959_) as usize);
    v___f_6970_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_refineCore___lam__1___boxed as *mut core::ffi::c_void,
        12,
        3,
    );
    leanh::lean_closure_set(v___f_6970_, 0, v_stx_6957_);
    leanh::lean_closure_set(v___f_6970_, 1, v_tagSuffix_6958_);
    leanh::lean_closure_set(v___f_6970_, 2, v___x_6969_);
    v___x_6971_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_6970_,
        v_a_6960_,
        v_a_6961_,
        v_a_6962_,
        v_a_6963_,
        v_a_6964_,
        v_a_6965_,
        v_a_6966_,
        v_a_6967_,
    );
    return v___x_6971_;
}
pub unsafe fn l_Lean_Elab_Tactic_refineCore___boxed(
    mut v_stx_6972_: *mut leanh::LeanObject,
    mut v_tagSuffix_6973_: *mut leanh::LeanObject,
    mut v_allowNaturalHoles_6974_: *mut leanh::LeanObject,
    mut v_a_6975_: *mut leanh::LeanObject,
    mut v_a_6976_: *mut leanh::LeanObject,
    mut v_a_6977_: *mut leanh::LeanObject,
    mut v_a_6978_: *mut leanh::LeanObject,
    mut v_a_6979_: *mut leanh::LeanObject,
    mut v_a_6980_: *mut leanh::LeanObject,
    mut v_a_6981_: *mut leanh::LeanObject,
    mut v_a_6982_: *mut leanh::LeanObject,
    mut v_a_6983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowNaturalHoles_boxed_6984_: u8 = 0;
    let mut v_res_6985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowNaturalHoles_boxed_6984_ = (leanh::lean_unbox(v_allowNaturalHoles_6974_) as u8);
    v_res_6985_ = l_Lean_Elab_Tactic_refineCore(
        v_stx_6972_,
        v_tagSuffix_6973_,
        v_allowNaturalHoles_boxed_6984_,
        v_a_6975_,
        v_a_6976_,
        v_a_6977_,
        v_a_6978_,
        v_a_6979_,
        v_a_6980_,
        v_a_6981_,
        v_a_6982_,
    );
    leanh::lean_dec(v_a_6982_);
    leanh::lean_dec_ref(v_a_6981_);
    leanh::lean_dec(v_a_6980_);
    leanh::lean_dec_ref(v_a_6979_);
    leanh::lean_dec(v_a_6978_);
    leanh::lean_dec_ref(v_a_6977_);
    leanh::lean_dec(v_a_6976_);
    leanh::lean_dec_ref(v_a_6975_);
    return v_res_6985_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0(
    mut v_mvarId_6986_: *mut leanh::LeanObject,
    mut v_val_6987_: *mut leanh::LeanObject,
    mut v___y_6988_: *mut leanh::LeanObject,
    mut v___y_6989_: *mut leanh::LeanObject,
    mut v___y_6990_: *mut leanh::LeanObject,
    mut v___y_6991_: *mut leanh::LeanObject,
    mut v___y_6992_: *mut leanh::LeanObject,
    mut v___y_6993_: *mut leanh::LeanObject,
    mut v___y_6994_: *mut leanh::LeanObject,
    mut v___y_6995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6997_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(
        v_mvarId_6986_,
        v_val_6987_,
        v___y_6993_,
    );
    return v___x_6997_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___boxed(
    mut v_mvarId_6998_: *mut leanh::LeanObject,
    mut v_val_6999_: *mut leanh::LeanObject,
    mut v___y_7000_: *mut leanh::LeanObject,
    mut v___y_7001_: *mut leanh::LeanObject,
    mut v___y_7002_: *mut leanh::LeanObject,
    mut v___y_7003_: *mut leanh::LeanObject,
    mut v___y_7004_: *mut leanh::LeanObject,
    mut v___y_7005_: *mut leanh::LeanObject,
    mut v___y_7006_: *mut leanh::LeanObject,
    mut v___y_7007_: *mut leanh::LeanObject,
    mut v___y_7008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7009_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0(
        v_mvarId_6998_,
        v_val_6999_,
        v___y_7000_,
        v___y_7001_,
        v___y_7002_,
        v___y_7003_,
        v___y_7004_,
        v___y_7005_,
        v___y_7006_,
        v___y_7007_,
    );
    leanh::lean_dec(v___y_7007_);
    leanh::lean_dec_ref(v___y_7006_);
    leanh::lean_dec(v___y_7005_);
    leanh::lean_dec_ref(v___y_7004_);
    leanh::lean_dec(v___y_7003_);
    leanh::lean_dec_ref(v___y_7002_);
    leanh::lean_dec(v___y_7001_);
    leanh::lean_dec_ref(v___y_7000_);
    return v_res_7009_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1(
    mut v_00_u03b1_7010_: *mut leanh::LeanObject,
    mut v_msg_7011_: *mut leanh::LeanObject,
    mut v___y_7012_: *mut leanh::LeanObject,
    mut v___y_7013_: *mut leanh::LeanObject,
    mut v___y_7014_: *mut leanh::LeanObject,
    mut v___y_7015_: *mut leanh::LeanObject,
    mut v___y_7016_: *mut leanh::LeanObject,
    mut v___y_7017_: *mut leanh::LeanObject,
    mut v___y_7018_: *mut leanh::LeanObject,
    mut v___y_7019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7021_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(
        v_msg_7011_,
        v___y_7016_,
        v___y_7017_,
        v___y_7018_,
        v___y_7019_,
    );
    return v___x_7021_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___boxed(
    mut v_00_u03b1_7022_: *mut leanh::LeanObject,
    mut v_msg_7023_: *mut leanh::LeanObject,
    mut v___y_7024_: *mut leanh::LeanObject,
    mut v___y_7025_: *mut leanh::LeanObject,
    mut v___y_7026_: *mut leanh::LeanObject,
    mut v___y_7027_: *mut leanh::LeanObject,
    mut v___y_7028_: *mut leanh::LeanObject,
    mut v___y_7029_: *mut leanh::LeanObject,
    mut v___y_7030_: *mut leanh::LeanObject,
    mut v___y_7031_: *mut leanh::LeanObject,
    mut v___y_7032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7033_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1(
        v_00_u03b1_7022_,
        v_msg_7023_,
        v___y_7024_,
        v___y_7025_,
        v___y_7026_,
        v___y_7027_,
        v___y_7028_,
        v___y_7029_,
        v___y_7030_,
        v___y_7031_,
    );
    leanh::lean_dec(v___y_7031_);
    leanh::lean_dec_ref(v___y_7030_);
    leanh::lean_dec(v___y_7029_);
    leanh::lean_dec_ref(v___y_7028_);
    leanh::lean_dec(v___y_7027_);
    leanh::lean_dec_ref(v___y_7026_);
    leanh::lean_dec(v___y_7025_);
    leanh::lean_dec_ref(v___y_7024_);
    return v_res_7033_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0(
    mut v_00_u03b2_7034_: *mut leanh::LeanObject,
    mut v_x_7035_: *mut leanh::LeanObject,
    mut v_x_7036_: *mut leanh::LeanObject,
    mut v_x_7037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7038_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(v_x_7035_, v_x_7036_, v_x_7037_);
    return v___x_7038_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(
    mut v_00_u03b2_7039_: *mut leanh::LeanObject,
    mut v_x_7040_: *mut leanh::LeanObject,
    mut v_x_7041_: usize,
    mut v_x_7042_: usize,
    mut v_x_7043_: *mut leanh::LeanObject,
    mut v_x_7044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7045_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_7040_, v_x_7041_, v_x_7042_, v_x_7043_, v_x_7044_);
    return v___x_7045_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_7046_: *mut leanh::LeanObject,
    mut v_x_7047_: *mut leanh::LeanObject,
    mut v_x_7048_: *mut leanh::LeanObject,
    mut v_x_7049_: *mut leanh::LeanObject,
    mut v_x_7050_: *mut leanh::LeanObject,
    mut v_x_7051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4410__boxed_7052_: usize = 0;
    let mut v_x_4411__boxed_7053_: usize = 0;
    let mut v_res_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4410__boxed_7052_ = leanh::lean_unbox_usize(v_x_7048_);
    leanh::lean_dec(v_x_7048_);
    v_x_4411__boxed_7053_ = leanh::lean_unbox_usize(v_x_7049_);
    leanh::lean_dec(v_x_7049_);
    v_res_7054_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(v_00_u03b2_7046_, v_x_7047_, v_x_4410__boxed_7052_, v_x_4411__boxed_7053_, v_x_7050_, v_x_7051_);
    return v_res_7054_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_7055_: *mut leanh::LeanObject,
    mut v_n_7056_: *mut leanh::LeanObject,
    mut v_k_7057_: *mut leanh::LeanObject,
    mut v_v_7058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7059_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_7056_, v_k_7057_, v_v_7058_);
    return v___x_7059_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03b2_7060_: *mut leanh::LeanObject,
    mut v_depth_7061_: usize,
    mut v_keys_7062_: *mut leanh::LeanObject,
    mut v_vals_7063_: *mut leanh::LeanObject,
    mut v_heq_7064_: *mut leanh::LeanObject,
    mut v_i_7065_: *mut leanh::LeanObject,
    mut v_entries_7066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7067_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_7061_, v_keys_7062_, v_vals_7063_, v_i_7065_, v_entries_7066_);
    return v___x_7067_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03b2_7068_: *mut leanh::LeanObject,
    mut v_depth_7069_: *mut leanh::LeanObject,
    mut v_keys_7070_: *mut leanh::LeanObject,
    mut v_vals_7071_: *mut leanh::LeanObject,
    mut v_heq_7072_: *mut leanh::LeanObject,
    mut v_i_7073_: *mut leanh::LeanObject,
    mut v_entries_7074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_7075_: usize = 0;
    let mut v_res_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_7075_ = leanh::lean_unbox_usize(v_depth_7069_);
    leanh::lean_dec(v_depth_7069_);
    v_res_7076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_7068_, v_depth_boxed_7075_, v_keys_7070_, v_vals_7071_, v_heq_7072_, v_i_7073_, v_entries_7074_);
    leanh::lean_dec_ref(v_vals_7071_);
    leanh::lean_dec_ref(v_keys_7070_);
    return v_res_7076_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_00_u03b2_7077_: *mut leanh::LeanObject,
    mut v_x_7078_: *mut leanh::LeanObject,
    mut v_x_7079_: *mut leanh::LeanObject,
    mut v_x_7080_: *mut leanh::LeanObject,
    mut v_x_7081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7082_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_7078_, v_x_7079_, v_x_7080_, v_x_7081_);
    return v___x_7082_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRefine(
    mut v_stx_7091_: *mut leanh::LeanObject,
    mut v_a_7092_: *mut leanh::LeanObject,
    mut v_a_7093_: *mut leanh::LeanObject,
    mut v_a_7094_: *mut leanh::LeanObject,
    mut v_a_7095_: *mut leanh::LeanObject,
    mut v_a_7096_: *mut leanh::LeanObject,
    mut v_a_7097_: *mut leanh::LeanObject,
    mut v_a_7098_: *mut leanh::LeanObject,
    mut v_a_7099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: u8 = 0;
    v___x_7101_ = l_Lean_Elab_Tactic_evalRefine___closed__1;
    leanh::lean_inc(v_stx_7091_);
    v___x_7102_ = l_Lean_Syntax_isOfKind(v_stx_7091_, v___x_7101_);
    if v___x_7102_ == 0 {
        let mut v___x_7103_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_7091_);
        v___x_7103_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg(
            );
        return v___x_7103_;
    } else {
        let mut v___x_7104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7105_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7106_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7107_: u8 = 0;
        let mut v___x_7108_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7104_ = leanh::lean_unsigned_to_nat(1);
        v___x_7105_ = l_Lean_Syntax_getArg(v_stx_7091_, v___x_7104_);
        leanh::lean_dec(v_stx_7091_);
        v___x_7106_ = l_Lean_Elab_Tactic_evalRefine___closed__2;
        v___x_7107_ = 0;
        v___x_7108_ = l_Lean_Elab_Tactic_refineCore(
            v___x_7105_,
            v___x_7106_,
            v___x_7107_,
            v_a_7092_,
            v_a_7093_,
            v_a_7094_,
            v_a_7095_,
            v_a_7096_,
            v_a_7097_,
            v_a_7098_,
            v_a_7099_,
        );
        return v___x_7108_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalRefine___boxed(
    mut v_stx_7109_: *mut leanh::LeanObject,
    mut v_a_7110_: *mut leanh::LeanObject,
    mut v_a_7111_: *mut leanh::LeanObject,
    mut v_a_7112_: *mut leanh::LeanObject,
    mut v_a_7113_: *mut leanh::LeanObject,
    mut v_a_7114_: *mut leanh::LeanObject,
    mut v_a_7115_: *mut leanh::LeanObject,
    mut v_a_7116_: *mut leanh::LeanObject,
    mut v_a_7117_: *mut leanh::LeanObject,
    mut v_a_7118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7119_ = l_Lean_Elab_Tactic_evalRefine(
        v_stx_7109_,
        v_a_7110_,
        v_a_7111_,
        v_a_7112_,
        v_a_7113_,
        v_a_7114_,
        v_a_7115_,
        v_a_7116_,
        v_a_7117_,
    );
    leanh::lean_dec(v_a_7117_);
    leanh::lean_dec_ref(v_a_7116_);
    leanh::lean_dec(v_a_7115_);
    leanh::lean_dec_ref(v_a_7114_);
    leanh::lean_dec(v_a_7113_);
    leanh::lean_dec_ref(v_a_7112_);
    leanh::lean_dec(v_a_7111_);
    leanh::lean_dec_ref(v_a_7110_);
    return v_res_7119_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1()
-> *mut leanh::LeanObject {
    let mut v___x_7127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7127_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7128_ = l_Lean_Elab_Tactic_evalRefine___closed__1;
    v___x_7129_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1;
    v___x_7130_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalRefine___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7131_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7127_,
        v___x_7128_,
        v___x_7129_,
        v___x_7130_,
    );
    return v___x_7131_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___boxed(
    mut v_a_7132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7133_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1();
    return v_res_7133_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_7160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7160_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1;
    v___x_7161_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6;
    v___x_7162_ = l_Lean_addBuiltinDeclarationRanges(v___x_7160_, v___x_7161_);
    return v___x_7162_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___boxed(
    mut v_a_7163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7164_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3();
    return v_res_7164_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRefine_x27(
    mut v_stx_7173_: *mut leanh::LeanObject,
    mut v_a_7174_: *mut leanh::LeanObject,
    mut v_a_7175_: *mut leanh::LeanObject,
    mut v_a_7176_: *mut leanh::LeanObject,
    mut v_a_7177_: *mut leanh::LeanObject,
    mut v_a_7178_: *mut leanh::LeanObject,
    mut v_a_7179_: *mut leanh::LeanObject,
    mut v_a_7180_: *mut leanh::LeanObject,
    mut v_a_7181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: u8 = 0;
    v___x_7183_ = l_Lean_Elab_Tactic_evalRefine_x27___closed__1;
    leanh::lean_inc(v_stx_7173_);
    v___x_7184_ = l_Lean_Syntax_isOfKind(v_stx_7173_, v___x_7183_);
    if v___x_7184_ == 0 {
        let mut v___x_7185_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_7173_);
        v___x_7185_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg(
            );
        return v___x_7185_;
    } else {
        let mut v___x_7186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7189_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7186_ = leanh::lean_unsigned_to_nat(1);
        v___x_7187_ = l_Lean_Syntax_getArg(v_stx_7173_, v___x_7186_);
        leanh::lean_dec(v_stx_7173_);
        v___x_7188_ = l_Lean_Elab_Tactic_evalRefine_x27___closed__2;
        v___x_7189_ = l_Lean_Elab_Tactic_refineCore(
            v___x_7187_,
            v___x_7188_,
            v___x_7184_,
            v_a_7174_,
            v_a_7175_,
            v_a_7176_,
            v_a_7177_,
            v_a_7178_,
            v_a_7179_,
            v_a_7180_,
            v_a_7181_,
        );
        return v___x_7189_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalRefine_x27___boxed(
    mut v_stx_7190_: *mut leanh::LeanObject,
    mut v_a_7191_: *mut leanh::LeanObject,
    mut v_a_7192_: *mut leanh::LeanObject,
    mut v_a_7193_: *mut leanh::LeanObject,
    mut v_a_7194_: *mut leanh::LeanObject,
    mut v_a_7195_: *mut leanh::LeanObject,
    mut v_a_7196_: *mut leanh::LeanObject,
    mut v_a_7197_: *mut leanh::LeanObject,
    mut v_a_7198_: *mut leanh::LeanObject,
    mut v_a_7199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7200_ = l_Lean_Elab_Tactic_evalRefine_x27(
        v_stx_7190_,
        v_a_7191_,
        v_a_7192_,
        v_a_7193_,
        v_a_7194_,
        v_a_7195_,
        v_a_7196_,
        v_a_7197_,
        v_a_7198_,
    );
    leanh::lean_dec(v_a_7198_);
    leanh::lean_dec_ref(v_a_7197_);
    leanh::lean_dec(v_a_7196_);
    leanh::lean_dec_ref(v_a_7195_);
    leanh::lean_dec(v_a_7194_);
    leanh::lean_dec_ref(v_a_7193_);
    leanh::lean_dec(v_a_7192_);
    leanh::lean_dec_ref(v_a_7191_);
    return v_res_7200_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1()
-> *mut leanh::LeanObject {
    let mut v___x_7208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7208_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7209_ = l_Lean_Elab_Tactic_evalRefine_x27___closed__1;
    v___x_7210_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1;
    v___x_7211_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalRefine_x27___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7212_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7208_,
        v___x_7209_,
        v___x_7210_,
        v___x_7211_,
    );
    return v___x_7212_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___boxed(
    mut v_a_7213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7214_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1();
    return v_res_7214_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_7241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7241_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1;
    v___x_7242_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6;
    v___x_7243_ = l_Lean_addBuiltinDeclarationRanges(v___x_7241_, v___x_7242_);
    return v___x_7243_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___boxed(
    mut v_a_7244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7245_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3();
    return v_res_7245_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7247_ = l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0;
    v___x_7248_ = l_Lean_stringToMessageData(v___x_7247_);
    return v___x_7248_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSpecialize___lam__0(
    mut v___x_7249_: u8,
    mut v_stx_7250_: *mut leanh::LeanObject,
    mut v___x_7251_: *mut leanh::LeanObject,
    mut v___x_7252_: u8,
    mut v___y_7253_: *mut leanh::LeanObject,
    mut v___y_7254_: *mut leanh::LeanObject,
    mut v___y_7255_: *mut leanh::LeanObject,
    mut v___y_7256_: *mut leanh::LeanObject,
    mut v___y_7257_: *mut leanh::LeanObject,
    mut v___y_7258_: *mut leanh::LeanObject,
    mut v___y_7259_: *mut leanh::LeanObject,
    mut v___y_7260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7273_: u8 = 0;
    let mut v___x_7274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_7285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7295_: u8 = 0;
    let mut v___x_7297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7299_: u8 = 0;
    let mut v_a_7300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7303_: u8 = 0;
    let mut v___x_7305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7307_: u8 = 0;
    let mut v_a_7308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7311_: u8 = 0;
    let mut v___x_7313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7315_: u8 = 0;
    let mut v___x_7316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7318_: u8 = 0;
    let mut v_a_7319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7322_: u8 = 0;
    let mut v___x_7324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_7249_ == 0 {
                    leanh::lean_dec_ref(v___x_7251_);
                    v___x_7262_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
                    return v___x_7262_;
                } else {
                    v___x_7263_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7264_ = l_Lean_Syntax_getArg(v_stx_7250_, v___x_7263_);
                    v___x_7265_ = leanh::lean_box(0);
                    v___x_7266_ = l_Lean_Name_mkStr1(v___x_7251_);
                    v___x_7267_ = l_Lean_Elab_Tactic_elabTermWithHoles(
                        v___x_7264_,
                        v___x_7265_,
                        v___x_7266_,
                        v___x_7252_,
                        v___x_7265_,
                        v___y_7253_,
                        v___y_7254_,
                        v___y_7255_,
                        v___y_7256_,
                        v___y_7257_,
                        v___y_7258_,
                        v___y_7259_,
                        v___y_7260_,
                    );
                    if leanh::lean_obj_tag(v___x_7267_) == 0 {
                        v_a_7268_ = leanh::lean_ctor_get(v___x_7267_, 0);
                        leanh::lean_inc(v_a_7268_);
                        leanh::lean_dec_ref_known(v___x_7267_, 1);
                        v_fst_7269_ = leanh::lean_ctor_get(v_a_7268_, 0);
                        v_snd_7270_ = leanh::lean_ctor_get(v_a_7268_, 1);
                        v_isSharedCheck_7318_ = (!leanh::lean_is_exclusive(v_a_7268_)) as u8;
                        if v_isSharedCheck_7318_ == 0 {
                            v___x_7272_ = v_a_7268_;
                            v_isShared_7273_ = v_isSharedCheck_7318_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_7270_);
                            leanh::lean_inc(v_fst_7269_);
                            leanh::lean_dec(v_a_7268_);
                            v___x_7272_ = leanh::lean_box(0);
                            v_isShared_7273_ = v_isSharedCheck_7318_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7319_ = leanh::lean_ctor_get(v___x_7267_, 0);
                        v_isSharedCheck_7326_ =
                            (!leanh::lean_is_exclusive(v___x_7267_)) as u8;
                        if v_isSharedCheck_7326_ == 0 {
                            v___x_7321_ = v___x_7267_;
                            v_isShared_7322_ = v_isSharedCheck_7326_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7319_);
                            leanh::lean_dec(v___x_7267_);
                            v___x_7321_ = leanh::lean_box(0);
                            v_isShared_7322_ = v_isSharedCheck_7326_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7274_ = l_Lean_Expr_getLambdaBody(v_fst_7269_);
                v___x_7275_ = l_Lean_Expr_getAppFn(v___x_7274_);
                leanh::lean_dec_ref(v___x_7274_);
                if leanh::lean_obj_tag(v___x_7275_) == 1 {
                    v_fvarId_7276_ = leanh::lean_ctor_get(v___x_7275_, 0);
                    leanh::lean_inc(v_fvarId_7276_);
                    leanh::lean_dec_ref_known(v___x_7275_, 1);
                    v___x_7277_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v___y_7254_,
                        v___y_7257_,
                        v___y_7258_,
                        v___y_7259_,
                        v___y_7260_,
                    );
                    if leanh::lean_obj_tag(v___x_7277_) == 0 {
                        v_a_7278_ = leanh::lean_ctor_get(v___x_7277_, 0);
                        leanh::lean_inc(v_a_7278_);
                        leanh::lean_dec_ref_known(v___x_7277_, 1);
                        leanh::lean_inc(v___y_7260_);
                        leanh::lean_inc_ref(v___y_7259_);
                        leanh::lean_inc(v___y_7258_);
                        leanh::lean_inc_ref(v___y_7257_);
                        leanh::lean_inc(v_fst_7269_);
                        v___x_7279_ = lean_infer_type(
                            v_fst_7269_,
                            v___y_7257_,
                            v___y_7258_,
                            v___y_7259_,
                            v___y_7260_,
                        );
                        if leanh::lean_obj_tag(v___x_7279_) == 0 {
                            v_a_7280_ = leanh::lean_ctor_get(v___x_7279_, 0);
                            leanh::lean_inc(v_a_7280_);
                            leanh::lean_dec_ref_known(v___x_7279_, 1);
                            v___x_7281_ = l_Lean_Expr_headBeta(v_a_7280_);
                            v___x_7282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_7282_, 0, v___x_7281_);
                            v___x_7283_ = l_Lean_MVarId_replace(
                                v_a_7278_,
                                v_fvarId_7276_,
                                v_fst_7269_,
                                v___x_7282_,
                                v___x_7265_,
                                v___y_7257_,
                                v___y_7258_,
                                v___y_7259_,
                                v___y_7260_,
                            );
                            if leanh::lean_obj_tag(v___x_7283_) == 0 {
                                v_a_7284_ = leanh::lean_ctor_get(v___x_7283_, 0);
                                leanh::lean_inc(v_a_7284_);
                                leanh::lean_dec_ref_known(v___x_7283_, 1);
                                v_mvarId_7285_ = leanh::lean_ctor_get(v_a_7284_, 1);
                                leanh::lean_inc(v_mvarId_7285_);
                                leanh::lean_dec(v_a_7284_);
                                v___x_7286_ = leanh::lean_box(0);
                                if v_isShared_7273_ == 0 {
                                    leanh::lean_ctor_set_tag(v___x_7272_, 1);
                                    leanh::lean_ctor_set(v___x_7272_, 1, v___x_7286_);
                                    leanh::lean_ctor_set(v___x_7272_, 0, v_mvarId_7285_);
                                    v___x_7288_ = v___x_7272_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7291_ =
                                        leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7291_,
                                        0,
                                        v_mvarId_7285_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7291_,
                                        1,
                                        v___x_7286_,
                                    );
                                    v___x_7288_ = v_reuseFailAlloc_7291_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_7272_);
                                leanh::lean_dec(v_snd_7270_);
                                v_a_7292_ = leanh::lean_ctor_get(v___x_7283_, 0);
                                v_isSharedCheck_7299_ =
                                    (!leanh::lean_is_exclusive(v___x_7283_)) as u8;
                                if v_isSharedCheck_7299_ == 0 {
                                    v___x_7294_ = v___x_7283_;
                                    v_isShared_7295_ = v_isSharedCheck_7299_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7292_);
                                    leanh::lean_dec(v___x_7283_);
                                    v___x_7294_ = leanh::lean_box(0);
                                    v_isShared_7295_ = v_isSharedCheck_7299_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_7278_);
                            leanh::lean_dec(v_fvarId_7276_);
                            leanh::lean_del_object(v___x_7272_);
                            leanh::lean_dec(v_snd_7270_);
                            leanh::lean_dec(v_fst_7269_);
                            v_a_7300_ = leanh::lean_ctor_get(v___x_7279_, 0);
                            v_isSharedCheck_7307_ =
                                (!leanh::lean_is_exclusive(v___x_7279_)) as u8;
                            if v_isSharedCheck_7307_ == 0 {
                                v___x_7302_ = v___x_7279_;
                                v_isShared_7303_ = v_isSharedCheck_7307_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7300_);
                                leanh::lean_dec(v___x_7279_);
                                v___x_7302_ = leanh::lean_box(0);
                                v_isShared_7303_ = v_isSharedCheck_7307_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_fvarId_7276_);
                        leanh::lean_del_object(v___x_7272_);
                        leanh::lean_dec(v_snd_7270_);
                        leanh::lean_dec(v_fst_7269_);
                        v_a_7308_ = leanh::lean_ctor_get(v___x_7277_, 0);
                        v_isSharedCheck_7315_ =
                            (!leanh::lean_is_exclusive(v___x_7277_)) as u8;
                        if v_isSharedCheck_7315_ == 0 {
                            v___x_7310_ = v___x_7277_;
                            v_isShared_7311_ = v_isSharedCheck_7315_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7308_);
                            leanh::lean_dec(v___x_7277_);
                            v___x_7310_ = leanh::lean_box(0);
                            v_isShared_7311_ = v_isSharedCheck_7315_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_7275_);
                    leanh::lean_del_object(v___x_7272_);
                    leanh::lean_dec(v_snd_7270_);
                    leanh::lean_dec(v_fst_7269_);
                    v___x_7316_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1,
                    );
                    v___x_7317_ =
                        l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(
                            v___x_7316_,
                            v___y_7257_,
                            v___y_7258_,
                            v___y_7259_,
                            v___y_7260_,
                        );
                    return v___x_7317_;
                }
            }
            2 => {
                v___x_7289_ = l_List_appendTR___redArg(v_snd_7270_, v___x_7288_);
                v___x_7290_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_7289_,
                    v___y_7254_,
                    v___y_7257_,
                    v___y_7258_,
                    v___y_7259_,
                    v___y_7260_,
                );
                return v___x_7290_;
            }
            3 => {
                if v_isShared_7295_ == 0 {
                    v___x_7297_ = v___x_7294_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7298_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7298_, 0, v_a_7292_);
                    v___x_7297_ = v_reuseFailAlloc_7298_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7297_;
            }
            5 => {
                if v_isShared_7303_ == 0 {
                    v___x_7305_ = v___x_7302_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7306_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7306_, 0, v_a_7300_);
                    v___x_7305_ = v_reuseFailAlloc_7306_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7305_;
            }
            7 => {
                if v_isShared_7311_ == 0 {
                    v___x_7313_ = v___x_7310_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7314_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7314_, 0, v_a_7308_);
                    v___x_7313_ = v_reuseFailAlloc_7314_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7313_;
            }
            9 => {
                if v_isShared_7322_ == 0 {
                    v___x_7324_ = v___x_7321_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7325_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7325_, 0, v_a_7319_);
                    v___x_7324_ = v_reuseFailAlloc_7325_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed(
    mut v___x_7327_: *mut leanh::LeanObject,
    mut v_stx_7328_: *mut leanh::LeanObject,
    mut v___x_7329_: *mut leanh::LeanObject,
    mut v___x_7330_: *mut leanh::LeanObject,
    mut v___y_7331_: *mut leanh::LeanObject,
    mut v___y_7332_: *mut leanh::LeanObject,
    mut v___y_7333_: *mut leanh::LeanObject,
    mut v___y_7334_: *mut leanh::LeanObject,
    mut v___y_7335_: *mut leanh::LeanObject,
    mut v___y_7336_: *mut leanh::LeanObject,
    mut v___y_7337_: *mut leanh::LeanObject,
    mut v___y_7338_: *mut leanh::LeanObject,
    mut v___y_7339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1129__boxed_7340_: u8 = 0;
    let mut v___x_1131__boxed_7341_: u8 = 0;
    let mut v_res_7342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1129__boxed_7340_ = (leanh::lean_unbox(v___x_7327_) as u8);
    v___x_1131__boxed_7341_ = (leanh::lean_unbox(v___x_7330_) as u8);
    v_res_7342_ = l_Lean_Elab_Tactic_evalSpecialize___lam__0(
        v___x_1129__boxed_7340_,
        v_stx_7328_,
        v___x_7329_,
        v___x_1131__boxed_7341_,
        v___y_7331_,
        v___y_7332_,
        v___y_7333_,
        v___y_7334_,
        v___y_7335_,
        v___y_7336_,
        v___y_7337_,
        v___y_7338_,
    );
    leanh::lean_dec(v___y_7338_);
    leanh::lean_dec_ref(v___y_7337_);
    leanh::lean_dec(v___y_7336_);
    leanh::lean_dec_ref(v___y_7335_);
    leanh::lean_dec(v___y_7334_);
    leanh::lean_dec_ref(v___y_7333_);
    leanh::lean_dec(v___y_7332_);
    leanh::lean_dec_ref(v___y_7331_);
    leanh::lean_dec(v_stx_7328_);
    return v_res_7342_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSpecialize(
    mut v_stx_7349_: *mut leanh::LeanObject,
    mut v_a_7350_: *mut leanh::LeanObject,
    mut v_a_7351_: *mut leanh::LeanObject,
    mut v_a_7352_: *mut leanh::LeanObject,
    mut v_a_7353_: *mut leanh::LeanObject,
    mut v_a_7354_: *mut leanh::LeanObject,
    mut v_a_7355_: *mut leanh::LeanObject,
    mut v_a_7356_: *mut leanh::LeanObject,
    mut v_a_7357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: u8 = 0;
    let mut v___x_7362_: u8 = 0;
    let mut v___x_7363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7359_ = l_Lean_Elab_Tactic_evalSpecialize___closed__0;
    v___x_7360_ = l_Lean_Elab_Tactic_evalSpecialize___closed__1;
    leanh::lean_inc(v_stx_7349_);
    v___x_7361_ = l_Lean_Syntax_isOfKind(v_stx_7349_, v___x_7360_);
    v___x_7362_ = 1;
    v___x_7363_ = leanh::lean_box((v___x_7361_) as usize);
    v___x_7364_ = leanh::lean_box((v___x_7362_) as usize);
    v___y_7365_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed as *mut core::ffi::c_void,
        13,
        4,
    );
    leanh::lean_closure_set(v___y_7365_, 0, v___x_7363_);
    leanh::lean_closure_set(v___y_7365_, 1, v_stx_7349_);
    leanh::lean_closure_set(v___y_7365_, 2, v___x_7359_);
    leanh::lean_closure_set(v___y_7365_, 3, v___x_7364_);
    v___x_7366_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___y_7365_,
        v_a_7350_,
        v_a_7351_,
        v_a_7352_,
        v_a_7353_,
        v_a_7354_,
        v_a_7355_,
        v_a_7356_,
        v_a_7357_,
    );
    return v___x_7366_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSpecialize___boxed(
    mut v_stx_7367_: *mut leanh::LeanObject,
    mut v_a_7368_: *mut leanh::LeanObject,
    mut v_a_7369_: *mut leanh::LeanObject,
    mut v_a_7370_: *mut leanh::LeanObject,
    mut v_a_7371_: *mut leanh::LeanObject,
    mut v_a_7372_: *mut leanh::LeanObject,
    mut v_a_7373_: *mut leanh::LeanObject,
    mut v_a_7374_: *mut leanh::LeanObject,
    mut v_a_7375_: *mut leanh::LeanObject,
    mut v_a_7376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7377_ = l_Lean_Elab_Tactic_evalSpecialize(
        v_stx_7367_,
        v_a_7368_,
        v_a_7369_,
        v_a_7370_,
        v_a_7371_,
        v_a_7372_,
        v_a_7373_,
        v_a_7374_,
        v_a_7375_,
    );
    leanh::lean_dec(v_a_7375_);
    leanh::lean_dec_ref(v_a_7374_);
    leanh::lean_dec(v_a_7373_);
    leanh::lean_dec_ref(v_a_7372_);
    leanh::lean_dec(v_a_7371_);
    leanh::lean_dec_ref(v_a_7370_);
    leanh::lean_dec(v_a_7369_);
    leanh::lean_dec_ref(v_a_7368_);
    return v_res_7377_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1()
-> *mut leanh::LeanObject {
    let mut v___x_7385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7385_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7386_ = l_Lean_Elab_Tactic_evalSpecialize___closed__1;
    v___x_7387_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1;
    v___x_7388_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSpecialize___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7389_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7385_,
        v___x_7386_,
        v___x_7387_,
        v___x_7388_,
    );
    return v___x_7389_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___boxed(
    mut v_a_7390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7391_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1();
    return v_res_7391_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_7417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7417_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1;
    v___x_7418_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6;
    v___x_7419_ = l_Lean_addBuiltinDeclarationRanges(v___x_7417_, v___x_7418_);
    return v___x_7419_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___boxed(
    mut v_a_7420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7421_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3();
    return v_res_7421_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabTermForApply(
    mut v_stx_7423_: *mut leanh::LeanObject,
    mut v_mayPostpone_7424_: u8,
    mut v_a_7425_: *mut leanh::LeanObject,
    mut v_a_7426_: *mut leanh::LeanObject,
    mut v_a_7427_: *mut leanh::LeanObject,
    mut v_a_7428_: *mut leanh::LeanObject,
    mut v_a_7429_: *mut leanh::LeanObject,
    mut v_a_7430_: *mut leanh::LeanObject,
    mut v_a_7431_: *mut leanh::LeanObject,
    mut v_a_7432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_7435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: u8 = 0;
    let mut v___x_7446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7451_: u8 = 0;
    let mut v_val_7452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7456_: u8 = 0;
    let mut v_a_7457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7460_: u8 = 0;
    let mut v___x_7462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7445_ = l_Lean_Syntax_isIdent(v_stx_7423_);
                if v___x_7445_ == 0 {
                    v___y_7435_ = v_a_7425_;
                    v___y_7436_ = v_a_7426_;
                    v___y_7437_ = v_a_7427_;
                    v___y_7438_ = v_a_7428_;
                    v___y_7439_ = v_a_7429_;
                    v___y_7440_ = v_a_7430_;
                    v___y_7441_ = v_a_7431_;
                    v___y_7442_ = v_a_7432_;
                    state = 1;
                    continue;
                } else {
                    v___x_7446_ = l_Lean_Elab_Tactic_elabTermForApply___closed__0;
                    leanh::lean_inc(v_stx_7423_);
                    v___x_7447_ = l_Lean_Elab_Term_resolveId_x3f(
                        v_stx_7423_,
                        v___x_7446_,
                        v___x_7445_,
                        v_a_7427_,
                        v_a_7428_,
                        v_a_7429_,
                        v_a_7430_,
                        v_a_7431_,
                        v_a_7432_,
                    );
                    if leanh::lean_obj_tag(v___x_7447_) == 0 {
                        v_a_7448_ = leanh::lean_ctor_get(v___x_7447_, 0);
                        v_isSharedCheck_7456_ =
                            (!leanh::lean_is_exclusive(v___x_7447_)) as u8;
                        if v_isSharedCheck_7456_ == 0 {
                            v___x_7450_ = v___x_7447_;
                            v_isShared_7451_ = v_isSharedCheck_7456_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7448_);
                            leanh::lean_dec(v___x_7447_);
                            v___x_7450_ = leanh::lean_box(0);
                            v_isShared_7451_ = v_isSharedCheck_7456_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_stx_7423_);
                        v_a_7457_ = leanh::lean_ctor_get(v___x_7447_, 0);
                        v_isSharedCheck_7464_ =
                            (!leanh::lean_is_exclusive(v___x_7447_)) as u8;
                        if v_isSharedCheck_7464_ == 0 {
                            v___x_7459_ = v___x_7447_;
                            v_isShared_7460_ = v_isSharedCheck_7464_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7457_);
                            leanh::lean_dec(v___x_7447_);
                            v___x_7459_ = leanh::lean_box(0);
                            v_isShared_7460_ = v_isSharedCheck_7464_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7443_ = leanh::lean_box(0);
                v___x_7444_ = l_Lean_Elab_Tactic_elabTerm(
                    v_stx_7423_,
                    v___x_7443_,
                    v_mayPostpone_7424_,
                    v___y_7435_,
                    v___y_7436_,
                    v___y_7437_,
                    v___y_7438_,
                    v___y_7439_,
                    v___y_7440_,
                    v___y_7441_,
                    v___y_7442_,
                );
                return v___x_7444_;
            }
            2 => {
                if leanh::lean_obj_tag(v_a_7448_) == 1 {
                    leanh::lean_dec(v_stx_7423_);
                    v_val_7452_ = leanh::lean_ctor_get(v_a_7448_, 0);
                    leanh::lean_inc(v_val_7452_);
                    leanh::lean_dec_ref_known(v_a_7448_, 1);
                    if v_isShared_7451_ == 0 {
                        leanh::lean_ctor_set(v___x_7450_, 0, v_val_7452_);
                        v___x_7454_ = v___x_7450_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7455_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7455_, 0, v_val_7452_);
                        v___x_7454_ = v_reuseFailAlloc_7455_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7450_);
                    leanh::lean_dec(v_a_7448_);
                    v___y_7435_ = v_a_7425_;
                    v___y_7436_ = v_a_7426_;
                    v___y_7437_ = v_a_7427_;
                    v___y_7438_ = v_a_7428_;
                    v___y_7439_ = v_a_7429_;
                    v___y_7440_ = v_a_7430_;
                    v___y_7441_ = v_a_7431_;
                    v___y_7442_ = v_a_7432_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_7454_;
            }
            4 => {
                if v_isShared_7460_ == 0 {
                    v___x_7462_ = v___x_7459_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7463_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7463_, 0, v_a_7457_);
                    v___x_7462_ = v_reuseFailAlloc_7463_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabTermForApply___boxed(
    mut v_stx_7465_: *mut leanh::LeanObject,
    mut v_mayPostpone_7466_: *mut leanh::LeanObject,
    mut v_a_7467_: *mut leanh::LeanObject,
    mut v_a_7468_: *mut leanh::LeanObject,
    mut v_a_7469_: *mut leanh::LeanObject,
    mut v_a_7470_: *mut leanh::LeanObject,
    mut v_a_7471_: *mut leanh::LeanObject,
    mut v_a_7472_: *mut leanh::LeanObject,
    mut v_a_7473_: *mut leanh::LeanObject,
    mut v_a_7474_: *mut leanh::LeanObject,
    mut v_a_7475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mayPostpone_boxed_7476_: u8 = 0;
    let mut v_res_7477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_7476_ = (leanh::lean_unbox(v_mayPostpone_7466_) as u8);
    v_res_7477_ = l_Lean_Elab_Tactic_elabTermForApply(
        v_stx_7465_,
        v_mayPostpone_boxed_7476_,
        v_a_7467_,
        v_a_7468_,
        v_a_7469_,
        v_a_7470_,
        v_a_7471_,
        v_a_7472_,
        v_a_7473_,
        v_a_7474_,
    );
    leanh::lean_dec(v_a_7474_);
    leanh::lean_dec_ref(v_a_7473_);
    leanh::lean_dec(v_a_7472_);
    leanh::lean_dec_ref(v_a_7471_);
    leanh::lean_dec(v_a_7470_);
    leanh::lean_dec_ref(v_a_7469_);
    leanh::lean_dec(v_a_7468_);
    leanh::lean_dec_ref(v_a_7467_);
    return v_res_7477_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7479_ = l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0;
    v___x_7480_ = l_Lean_stringToMessageData(v___x_7479_);
    return v___x_7480_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7482_ = l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2;
    v___x_7483_ = l_Lean_stringToMessageData(v___x_7482_);
    return v___x_7483_;
}
pub unsafe fn l_Lean_Elab_Tactic_getFVarId___lam__0(
    mut v___x_7484_: *mut leanh::LeanObject,
    mut v___y_7485_: *mut leanh::LeanObject,
    mut v___y_7486_: *mut leanh::LeanObject,
    mut v___y_7487_: *mut leanh::LeanObject,
    mut v___y_7488_: *mut leanh::LeanObject,
    mut v___y_7489_: *mut leanh::LeanObject,
    mut v___y_7490_: *mut leanh::LeanObject,
    mut v___y_7491_: *mut leanh::LeanObject,
    mut v___y_7492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7498_: u8 = 0;
    let mut v_fvarId_7499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7509_: u8 = 0;
    let mut v_a_7510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7513_: u8 = 0;
    let mut v___x_7515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7494_ = l_Lean_Elab_Tactic_withoutRecover___redArg(
                    v___x_7484_,
                    v___y_7485_,
                    v___y_7486_,
                    v___y_7487_,
                    v___y_7488_,
                    v___y_7489_,
                    v___y_7490_,
                    v___y_7491_,
                    v___y_7492_,
                );
                if leanh::lean_obj_tag(v___x_7494_) == 0 {
                    v_a_7495_ = leanh::lean_ctor_get(v___x_7494_, 0);
                    v_isSharedCheck_7509_ = (!leanh::lean_is_exclusive(v___x_7494_)) as u8;
                    if v_isSharedCheck_7509_ == 0 {
                        v___x_7497_ = v___x_7494_;
                        v_isShared_7498_ = v_isSharedCheck_7509_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7495_);
                        leanh::lean_dec(v___x_7494_);
                        v___x_7497_ = leanh::lean_box(0);
                        v_isShared_7498_ = v_isSharedCheck_7509_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7510_ = leanh::lean_ctor_get(v___x_7494_, 0);
                    v_isSharedCheck_7517_ = (!leanh::lean_is_exclusive(v___x_7494_)) as u8;
                    if v_isSharedCheck_7517_ == 0 {
                        v___x_7512_ = v___x_7494_;
                        v_isShared_7513_ = v_isSharedCheck_7517_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7510_);
                        leanh::lean_dec(v___x_7494_);
                        v___x_7512_ = leanh::lean_box(0);
                        v_isShared_7513_ = v_isSharedCheck_7517_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_7495_) == 1 {
                    v_fvarId_7499_ = leanh::lean_ctor_get(v_a_7495_, 0);
                    leanh::lean_inc(v_fvarId_7499_);
                    leanh::lean_dec_ref_known(v_a_7495_, 1);
                    if v_isShared_7498_ == 0 {
                        leanh::lean_ctor_set(v___x_7497_, 0, v_fvarId_7499_);
                        v___x_7501_ = v___x_7497_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7502_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7502_, 0, v_fvarId_7499_);
                        v___x_7501_ = v_reuseFailAlloc_7502_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7497_);
                    v___x_7503_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1,
                    );
                    v___x_7504_ = l_Lean_MessageData_ofExpr(v_a_7495_);
                    v___x_7505_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7505_, 0, v___x_7503_);
                    leanh::lean_ctor_set(v___x_7505_, 1, v___x_7504_);
                    v___x_7506_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3,
                    );
                    v___x_7507_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7507_, 0, v___x_7505_);
                    leanh::lean_ctor_set(v___x_7507_, 1, v___x_7506_);
                    v___x_7508_ =
                        l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(
                            v___x_7507_,
                            v___y_7489_,
                            v___y_7490_,
                            v___y_7491_,
                            v___y_7492_,
                        );
                    return v___x_7508_;
                }
            }
            2 => {
                return v___x_7501_;
            }
            3 => {
                if v_isShared_7513_ == 0 {
                    v___x_7515_ = v___x_7512_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7516_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7516_, 0, v_a_7510_);
                    v___x_7515_ = v_reuseFailAlloc_7516_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_getFVarId___lam__0___boxed(
    mut v___x_7518_: *mut leanh::LeanObject,
    mut v___y_7519_: *mut leanh::LeanObject,
    mut v___y_7520_: *mut leanh::LeanObject,
    mut v___y_7521_: *mut leanh::LeanObject,
    mut v___y_7522_: *mut leanh::LeanObject,
    mut v___y_7523_: *mut leanh::LeanObject,
    mut v___y_7524_: *mut leanh::LeanObject,
    mut v___y_7525_: *mut leanh::LeanObject,
    mut v___y_7526_: *mut leanh::LeanObject,
    mut v___y_7527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7528_ = l_Lean_Elab_Tactic_getFVarId___lam__0(
        v___x_7518_,
        v___y_7519_,
        v___y_7520_,
        v___y_7521_,
        v___y_7522_,
        v___y_7523_,
        v___y_7524_,
        v___y_7525_,
        v___y_7526_,
    );
    leanh::lean_dec(v___y_7526_);
    leanh::lean_dec_ref(v___y_7525_);
    leanh::lean_dec(v___y_7524_);
    leanh::lean_dec_ref(v___y_7523_);
    leanh::lean_dec(v___y_7522_);
    leanh::lean_dec_ref(v___y_7521_);
    leanh::lean_dec(v___y_7520_);
    leanh::lean_dec_ref(v___y_7519_);
    return v_res_7528_;
}
pub unsafe fn l_Lean_Elab_Tactic_getFVarId(
    mut v_id_7529_: *mut leanh::LeanObject,
    mut v_a_7530_: *mut leanh::LeanObject,
    mut v_a_7531_: *mut leanh::LeanObject,
    mut v_a_7532_: *mut leanh::LeanObject,
    mut v_a_7533_: *mut leanh::LeanObject,
    mut v_a_7534_: *mut leanh::LeanObject,
    mut v_a_7535_: *mut leanh::LeanObject,
    mut v_a_7536_: *mut leanh::LeanObject,
    mut v_a_7537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_7539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7551_: u8 = 0;
    let mut v_cancelTk_x3f_7552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7553_: u8 = 0;
    let mut v_inheritedTraceOptions_7554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7555_: u8 = 0;
    let mut v___x_7556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_7539_ = leanh::lean_ctor_get(v_a_7536_, 0);
    v_fileMap_7540_ = leanh::lean_ctor_get(v_a_7536_, 1);
    v_options_7541_ = leanh::lean_ctor_get(v_a_7536_, 2);
    v_currRecDepth_7542_ = leanh::lean_ctor_get(v_a_7536_, 3);
    v_maxRecDepth_7543_ = leanh::lean_ctor_get(v_a_7536_, 4);
    v_ref_7544_ = leanh::lean_ctor_get(v_a_7536_, 5);
    v_currNamespace_7545_ = leanh::lean_ctor_get(v_a_7536_, 6);
    v_openDecls_7546_ = leanh::lean_ctor_get(v_a_7536_, 7);
    v_initHeartbeats_7547_ = leanh::lean_ctor_get(v_a_7536_, 8);
    v_maxHeartbeats_7548_ = leanh::lean_ctor_get(v_a_7536_, 9);
    v_quotContext_7549_ = leanh::lean_ctor_get(v_a_7536_, 10);
    v_currMacroScope_7550_ = leanh::lean_ctor_get(v_a_7536_, 11);
    v_diag_7551_ = leanh::lean_ctor_get_uint8(
        v_a_7536_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_7552_ = leanh::lean_ctor_get(v_a_7536_, 12);
    v_suppressElabErrors_7553_ = leanh::lean_ctor_get_uint8(
        v_a_7536_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_7554_ = leanh::lean_ctor_get(v_a_7536_, 13);
    v___x_7555_ = 0;
    v___x_7556_ = leanh::lean_box((v___x_7555_) as usize);
    leanh::lean_inc(v_id_7529_);
    v___x_7557_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_elabTermForApply___boxed as *mut core::ffi::c_void,
        11,
        2,
    );
    leanh::lean_closure_set(v___x_7557_, 0, v_id_7529_);
    leanh::lean_closure_set(v___x_7557_, 1, v___x_7556_);
    v___f_7558_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_getFVarId___lam__0___boxed as *mut core::ffi::c_void,
        10,
        1,
    );
    leanh::lean_closure_set(v___f_7558_, 0, v___x_7557_);
    v_ref_7559_ = l_Lean_replaceRef(v_id_7529_, v_ref_7544_);
    leanh::lean_dec(v_id_7529_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_7554_);
    leanh::lean_inc(v_cancelTk_x3f_7552_);
    leanh::lean_inc(v_currMacroScope_7550_);
    leanh::lean_inc(v_quotContext_7549_);
    leanh::lean_inc(v_maxHeartbeats_7548_);
    leanh::lean_inc(v_initHeartbeats_7547_);
    leanh::lean_inc(v_openDecls_7546_);
    leanh::lean_inc(v_currNamespace_7545_);
    leanh::lean_inc(v_maxRecDepth_7543_);
    leanh::lean_inc(v_currRecDepth_7542_);
    leanh::lean_inc_ref(v_options_7541_);
    leanh::lean_inc_ref(v_fileMap_7540_);
    leanh::lean_inc_ref(v_fileName_7539_);
    v___x_7560_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_7560_, 0, v_fileName_7539_);
    leanh::lean_ctor_set(v___x_7560_, 1, v_fileMap_7540_);
    leanh::lean_ctor_set(v___x_7560_, 2, v_options_7541_);
    leanh::lean_ctor_set(v___x_7560_, 3, v_currRecDepth_7542_);
    leanh::lean_ctor_set(v___x_7560_, 4, v_maxRecDepth_7543_);
    leanh::lean_ctor_set(v___x_7560_, 5, v_ref_7559_);
    leanh::lean_ctor_set(v___x_7560_, 6, v_currNamespace_7545_);
    leanh::lean_ctor_set(v___x_7560_, 7, v_openDecls_7546_);
    leanh::lean_ctor_set(v___x_7560_, 8, v_initHeartbeats_7547_);
    leanh::lean_ctor_set(v___x_7560_, 9, v_maxHeartbeats_7548_);
    leanh::lean_ctor_set(v___x_7560_, 10, v_quotContext_7549_);
    leanh::lean_ctor_set(v___x_7560_, 11, v_currMacroScope_7550_);
    leanh::lean_ctor_set(v___x_7560_, 12, v_cancelTk_x3f_7552_);
    leanh::lean_ctor_set(v___x_7560_, 13, v_inheritedTraceOptions_7554_);
    leanh::lean_ctor_set_uint8(
        v___x_7560_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_7551_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_7560_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_7553_,
    );
    v___x_7561_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_7558_,
        v_a_7530_,
        v_a_7531_,
        v_a_7532_,
        v_a_7533_,
        v_a_7534_,
        v_a_7535_,
        v___x_7560_,
        v_a_7537_,
    );
    leanh::lean_dec_ref_known(v___x_7560_, 14);
    return v___x_7561_;
}
pub unsafe fn l_Lean_Elab_Tactic_getFVarId___boxed(
    mut v_id_7562_: *mut leanh::LeanObject,
    mut v_a_7563_: *mut leanh::LeanObject,
    mut v_a_7564_: *mut leanh::LeanObject,
    mut v_a_7565_: *mut leanh::LeanObject,
    mut v_a_7566_: *mut leanh::LeanObject,
    mut v_a_7567_: *mut leanh::LeanObject,
    mut v_a_7568_: *mut leanh::LeanObject,
    mut v_a_7569_: *mut leanh::LeanObject,
    mut v_a_7570_: *mut leanh::LeanObject,
    mut v_a_7571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7572_ = l_Lean_Elab_Tactic_getFVarId(
        v_id_7562_, v_a_7563_, v_a_7564_, v_a_7565_, v_a_7566_, v_a_7567_, v_a_7568_, v_a_7569_,
        v_a_7570_,
    );
    leanh::lean_dec(v_a_7570_);
    leanh::lean_dec_ref(v_a_7569_);
    leanh::lean_dec(v_a_7568_);
    leanh::lean_dec_ref(v_a_7567_);
    leanh::lean_dec(v_a_7566_);
    leanh::lean_dec_ref(v_a_7565_);
    leanh::lean_dec(v_a_7564_);
    leanh::lean_dec_ref(v_a_7563_);
    return v_res_7572_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(
    mut v_sz_7573_: usize,
    mut v_i_7574_: usize,
    mut v_bs_7575_: *mut leanh::LeanObject,
    mut v___y_7576_: *mut leanh::LeanObject,
    mut v___y_7577_: *mut leanh::LeanObject,
    mut v___y_7578_: *mut leanh::LeanObject,
    mut v___y_7579_: *mut leanh::LeanObject,
    mut v___y_7580_: *mut leanh::LeanObject,
    mut v___y_7581_: *mut leanh::LeanObject,
    mut v___y_7582_: *mut leanh::LeanObject,
    mut v___y_7583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7585_: u8 = 0;
    let mut v___x_7586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7592_: usize = 0;
    let mut v___x_7593_: usize = 0;
    let mut v___x_7594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7599_: u8 = 0;
    let mut v___x_7601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7585_ = lean_usize_dec_lt(v_i_7574_, v_sz_7573_);
                if v___x_7585_ == 0 {
                    v___x_7586_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7586_, 0, v_bs_7575_);
                    return v___x_7586_;
                } else {
                    v_v_7587_ = lean_array_uget_borrowed(v_bs_7575_, v_i_7574_);
                    leanh::lean_inc(v_v_7587_);
                    v___x_7588_ = l_Lean_Elab_Tactic_getFVarId(
                        v_v_7587_,
                        v___y_7576_,
                        v___y_7577_,
                        v___y_7578_,
                        v___y_7579_,
                        v___y_7580_,
                        v___y_7581_,
                        v___y_7582_,
                        v___y_7583_,
                    );
                    if leanh::lean_obj_tag(v___x_7588_) == 0 {
                        v_a_7589_ = leanh::lean_ctor_get(v___x_7588_, 0);
                        leanh::lean_inc(v_a_7589_);
                        leanh::lean_dec_ref_known(v___x_7588_, 1);
                        v___x_7590_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_7591_ = lean_array_uset(v_bs_7575_, v_i_7574_, v___x_7590_);
                        v___x_7592_ = 1usize;
                        v___x_7593_ = lean_usize_add(v_i_7574_, v___x_7592_);
                        v___x_7594_ = lean_array_uset(v_bs_x27_7591_, v_i_7574_, v_a_7589_);
                        v_i_7574_ = v___x_7593_;
                        v_bs_7575_ = v___x_7594_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_7575_);
                        v_a_7596_ = leanh::lean_ctor_get(v___x_7588_, 0);
                        v_isSharedCheck_7603_ =
                            (!leanh::lean_is_exclusive(v___x_7588_)) as u8;
                        if v_isSharedCheck_7603_ == 0 {
                            v___x_7598_ = v___x_7588_;
                            v_isShared_7599_ = v_isSharedCheck_7603_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7596_);
                            leanh::lean_dec(v___x_7588_);
                            v___x_7598_ = leanh::lean_box(0);
                            v_isShared_7599_ = v_isSharedCheck_7603_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7599_ == 0 {
                    v___x_7601_ = v___x_7598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7602_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7602_, 0, v_a_7596_);
                    v___x_7601_ = v_reuseFailAlloc_7602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed(
    mut v_sz_7604_: *mut leanh::LeanObject,
    mut v_i_7605_: *mut leanh::LeanObject,
    mut v_bs_7606_: *mut leanh::LeanObject,
    mut v___y_7607_: *mut leanh::LeanObject,
    mut v___y_7608_: *mut leanh::LeanObject,
    mut v___y_7609_: *mut leanh::LeanObject,
    mut v___y_7610_: *mut leanh::LeanObject,
    mut v___y_7611_: *mut leanh::LeanObject,
    mut v___y_7612_: *mut leanh::LeanObject,
    mut v___y_7613_: *mut leanh::LeanObject,
    mut v___y_7614_: *mut leanh::LeanObject,
    mut v___y_7615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7616_: usize = 0;
    let mut v_i_boxed_7617_: usize = 0;
    let mut v_res_7618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7616_ = leanh::lean_unbox_usize(v_sz_7604_);
    leanh::lean_dec(v_sz_7604_);
    v_i_boxed_7617_ = leanh::lean_unbox_usize(v_i_7605_);
    leanh::lean_dec(v_i_7605_);
    v_res_7618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(v_sz_boxed_7616_, v_i_boxed_7617_, v_bs_7606_, v___y_7607_, v___y_7608_, v___y_7609_, v___y_7610_, v___y_7611_, v___y_7612_, v___y_7613_, v___y_7614_);
    leanh::lean_dec(v___y_7614_);
    leanh::lean_dec_ref(v___y_7613_);
    leanh::lean_dec(v___y_7612_);
    leanh::lean_dec_ref(v___y_7611_);
    leanh::lean_dec(v___y_7610_);
    leanh::lean_dec_ref(v___y_7609_);
    leanh::lean_dec(v___y_7608_);
    leanh::lean_dec_ref(v___y_7607_);
    return v_res_7618_;
}
pub unsafe fn l_Lean_Elab_Tactic_getFVarIds(
    mut v_ids_7621_: *mut leanh::LeanObject,
    mut v_a_7622_: *mut leanh::LeanObject,
    mut v_a_7623_: *mut leanh::LeanObject,
    mut v_a_7624_: *mut leanh::LeanObject,
    mut v_a_7625_: *mut leanh::LeanObject,
    mut v_a_7626_: *mut leanh::LeanObject,
    mut v_a_7627_: *mut leanh::LeanObject,
    mut v_a_7628_: *mut leanh::LeanObject,
    mut v_a_7629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_7631_: usize = 0;
    let mut v___x_7632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_7631_ = lean_array_size(v_ids_7621_);
    v___x_7632_ = leanh::lean_box_usize(v_sz_7631_);
    v___x_7633_ = l_Lean_Elab_Tactic_getFVarIds___boxed__const__1;
    v___x_7634_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed as *mut core::ffi::c_void, 12, 3);
    leanh::lean_closure_set(v___x_7634_, 0, v___x_7632_);
    leanh::lean_closure_set(v___x_7634_, 1, v___x_7633_);
    leanh::lean_closure_set(v___x_7634_, 2, v_ids_7621_);
    v___x_7635_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___x_7634_,
        v_a_7622_,
        v_a_7623_,
        v_a_7624_,
        v_a_7625_,
        v_a_7626_,
        v_a_7627_,
        v_a_7628_,
        v_a_7629_,
    );
    return v___x_7635_;
}
pub unsafe fn l_Lean_Elab_Tactic_getFVarIds___boxed(
    mut v_ids_7636_: *mut leanh::LeanObject,
    mut v_a_7637_: *mut leanh::LeanObject,
    mut v_a_7638_: *mut leanh::LeanObject,
    mut v_a_7639_: *mut leanh::LeanObject,
    mut v_a_7640_: *mut leanh::LeanObject,
    mut v_a_7641_: *mut leanh::LeanObject,
    mut v_a_7642_: *mut leanh::LeanObject,
    mut v_a_7643_: *mut leanh::LeanObject,
    mut v_a_7644_: *mut leanh::LeanObject,
    mut v_a_7645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7646_ = l_Lean_Elab_Tactic_getFVarIds(
        v_ids_7636_,
        v_a_7637_,
        v_a_7638_,
        v_a_7639_,
        v_a_7640_,
        v_a_7641_,
        v_a_7642_,
        v_a_7643_,
        v_a_7644_,
    );
    leanh::lean_dec(v_a_7644_);
    leanh::lean_dec_ref(v_a_7643_);
    leanh::lean_dec(v_a_7642_);
    leanh::lean_dec_ref(v_a_7641_);
    leanh::lean_dec(v_a_7640_);
    leanh::lean_dec_ref(v_a_7639_);
    leanh::lean_dec(v_a_7638_);
    leanh::lean_dec_ref(v_a_7637_);
    return v_res_7646_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(
    mut v_e_7647_: *mut leanh::LeanObject,
    mut v___x_7648_: u8,
    mut v_tac_7649_: *mut leanh::LeanObject,
    mut v___y_7650_: *mut leanh::LeanObject,
    mut v___y_7651_: *mut leanh::LeanObject,
    mut v___y_7652_: *mut leanh::LeanObject,
    mut v___y_7653_: *mut leanh::LeanObject,
    mut v___y_7654_: *mut leanh::LeanObject,
    mut v___y_7655_: *mut leanh::LeanObject,
    mut v___y_7656_: *mut leanh::LeanObject,
    mut v___y_7657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_7660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7672_: u8 = 0;
    let mut v___x_7673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7678_: u8 = 0;
    let mut v___x_7680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7682_: u8 = 0;
    let mut v_a_7683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7686_: u8 = 0;
    let mut v___x_7688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7690_: u8 = 0;
    let mut v___x_7691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7695_: u8 = 0;
    let mut v___x_7696_: u8 = 0;
    let mut v___x_7697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7703_: u8 = 0;
    let mut v___x_7705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7691_ = l_Lean_Elab_Tactic_elabTermForApply(
                    v_e_7647_,
                    v___x_7648_,
                    v___y_7650_,
                    v___y_7651_,
                    v___y_7652_,
                    v___y_7653_,
                    v___y_7654_,
                    v___y_7655_,
                    v___y_7656_,
                    v___y_7657_,
                );
                if leanh::lean_obj_tag(v___x_7691_) == 0 {
                    v_a_7692_ = leanh::lean_ctor_get(v___x_7691_, 0);
                    leanh::lean_inc(v_a_7692_);
                    leanh::lean_dec_ref_known(v___x_7691_, 1);
                    v___x_7693_ =
                        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(
                            v_a_7692_,
                            v___y_7655_,
                        );
                    v_a_7694_ = leanh::lean_ctor_get(v___x_7693_, 0);
                    leanh::lean_inc(v_a_7694_);
                    leanh::lean_dec_ref(v___x_7693_);
                    v___x_7695_ = l_Lean_Expr_isMVar(v_a_7694_);
                    if v___x_7695_ == 0 {
                        v_val_7660_ = v_a_7694_;
                        v___y_7661_ = v___y_7651_;
                        v___y_7662_ = v___y_7652_;
                        v___y_7663_ = v___y_7653_;
                        v___y_7664_ = v___y_7654_;
                        v___y_7665_ = v___y_7655_;
                        v___y_7666_ = v___y_7656_;
                        v___y_7667_ = v___y_7657_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7696_ = 0;
                        v___x_7697_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(
                            v___x_7696_,
                            v___y_7652_,
                            v___y_7653_,
                            v___y_7654_,
                            v___y_7655_,
                            v___y_7656_,
                            v___y_7657_,
                        );
                        if leanh::lean_obj_tag(v___x_7697_) == 0 {
                            leanh::lean_dec_ref_known(v___x_7697_, 1);
                            v___x_7698_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_7694_, v___y_7655_);
                            v_a_7699_ = leanh::lean_ctor_get(v___x_7698_, 0);
                            leanh::lean_inc(v_a_7699_);
                            leanh::lean_dec_ref(v___x_7698_);
                            v_val_7660_ = v_a_7699_;
                            v___y_7661_ = v___y_7651_;
                            v___y_7662_ = v___y_7652_;
                            v___y_7663_ = v___y_7653_;
                            v___y_7664_ = v___y_7654_;
                            v___y_7665_ = v___y_7655_;
                            v___y_7666_ = v___y_7656_;
                            v___y_7667_ = v___y_7657_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_7694_);
                            leanh::lean_dec(v___y_7657_);
                            leanh::lean_dec_ref(v___y_7656_);
                            leanh::lean_dec(v___y_7655_);
                            leanh::lean_dec_ref(v___y_7654_);
                            leanh::lean_dec_ref(v_tac_7649_);
                            return v___x_7697_;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_7657_);
                    leanh::lean_dec_ref(v___y_7656_);
                    leanh::lean_dec(v___y_7655_);
                    leanh::lean_dec_ref(v___y_7654_);
                    leanh::lean_dec_ref(v_tac_7649_);
                    v_a_7700_ = leanh::lean_ctor_get(v___x_7691_, 0);
                    v_isSharedCheck_7707_ = (!leanh::lean_is_exclusive(v___x_7691_)) as u8;
                    if v_isSharedCheck_7707_ == 0 {
                        v___x_7702_ = v___x_7691_;
                        v_isShared_7703_ = v_isSharedCheck_7707_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7700_);
                        leanh::lean_dec(v___x_7691_);
                        v___x_7702_ = leanh::lean_box(0);
                        v_isShared_7703_ = v_isSharedCheck_7707_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7668_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_7661_,
                    v___y_7664_,
                    v___y_7665_,
                    v___y_7666_,
                    v___y_7667_,
                );
                if leanh::lean_obj_tag(v___x_7668_) == 0 {
                    v_a_7669_ = leanh::lean_ctor_get(v___x_7668_, 0);
                    leanh::lean_inc(v_a_7669_);
                    leanh::lean_dec_ref_known(v___x_7668_, 1);
                    leanh::lean_inc(v___y_7667_);
                    leanh::lean_inc_ref(v___y_7666_);
                    leanh::lean_inc(v___y_7665_);
                    leanh::lean_inc_ref(v___y_7664_);
                    v___x_7670_ = leanh::lean_apply_7(
                        v_tac_7649_,
                        v_a_7669_,
                        v_val_7660_,
                        v___y_7664_,
                        v___y_7665_,
                        v___y_7666_,
                        v___y_7667_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_7670_) == 0 {
                        v_a_7671_ = leanh::lean_ctor_get(v___x_7670_, 0);
                        leanh::lean_inc(v_a_7671_);
                        leanh::lean_dec_ref_known(v___x_7670_, 1);
                        v___x_7672_ = 0;
                        v___x_7673_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(
                            v___x_7672_,
                            v___y_7662_,
                            v___y_7663_,
                            v___y_7664_,
                            v___y_7665_,
                            v___y_7666_,
                            v___y_7667_,
                        );
                        if leanh::lean_obj_tag(v___x_7673_) == 0 {
                            leanh::lean_dec_ref_known(v___x_7673_, 1);
                            v___x_7674_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v_a_7671_,
                                v___y_7661_,
                                v___y_7664_,
                                v___y_7665_,
                                v___y_7666_,
                                v___y_7667_,
                            );
                            leanh::lean_dec(v___y_7667_);
                            leanh::lean_dec_ref(v___y_7666_);
                            leanh::lean_dec(v___y_7665_);
                            leanh::lean_dec_ref(v___y_7664_);
                            return v___x_7674_;
                        } else {
                            leanh::lean_dec(v_a_7671_);
                            leanh::lean_dec(v___y_7667_);
                            leanh::lean_dec_ref(v___y_7666_);
                            leanh::lean_dec(v___y_7665_);
                            leanh::lean_dec_ref(v___y_7664_);
                            return v___x_7673_;
                        }
                    } else {
                        leanh::lean_dec(v___y_7667_);
                        leanh::lean_dec_ref(v___y_7666_);
                        leanh::lean_dec(v___y_7665_);
                        leanh::lean_dec_ref(v___y_7664_);
                        v_a_7675_ = leanh::lean_ctor_get(v___x_7670_, 0);
                        v_isSharedCheck_7682_ =
                            (!leanh::lean_is_exclusive(v___x_7670_)) as u8;
                        if v_isSharedCheck_7682_ == 0 {
                            v___x_7677_ = v___x_7670_;
                            v_isShared_7678_ = v_isSharedCheck_7682_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7675_);
                            leanh::lean_dec(v___x_7670_);
                            v___x_7677_ = leanh::lean_box(0);
                            v_isShared_7678_ = v_isSharedCheck_7682_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_7667_);
                    leanh::lean_dec_ref(v___y_7666_);
                    leanh::lean_dec(v___y_7665_);
                    leanh::lean_dec_ref(v___y_7664_);
                    leanh::lean_dec_ref(v_val_7660_);
                    leanh::lean_dec_ref(v_tac_7649_);
                    v_a_7683_ = leanh::lean_ctor_get(v___x_7668_, 0);
                    v_isSharedCheck_7690_ = (!leanh::lean_is_exclusive(v___x_7668_)) as u8;
                    if v_isSharedCheck_7690_ == 0 {
                        v___x_7685_ = v___x_7668_;
                        v_isShared_7686_ = v_isSharedCheck_7690_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7683_);
                        leanh::lean_dec(v___x_7668_);
                        v___x_7685_ = leanh::lean_box(0);
                        v_isShared_7686_ = v_isSharedCheck_7690_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7678_ == 0 {
                    v___x_7680_ = v___x_7677_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7681_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7681_, 0, v_a_7675_);
                    v___x_7680_ = v_reuseFailAlloc_7681_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7680_;
            }
            4 => {
                if v_isShared_7686_ == 0 {
                    v___x_7688_ = v___x_7685_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7689_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7689_, 0, v_a_7683_);
                    v___x_7688_ = v_reuseFailAlloc_7689_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7688_;
            }
            6 => {
                if v_isShared_7703_ == 0 {
                    v___x_7705_ = v___x_7702_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7706_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7706_, 0, v_a_7700_);
                    v___x_7705_ = v_reuseFailAlloc_7706_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed(
    mut v_e_7708_: *mut leanh::LeanObject,
    mut v___x_7709_: *mut leanh::LeanObject,
    mut v_tac_7710_: *mut leanh::LeanObject,
    mut v___y_7711_: *mut leanh::LeanObject,
    mut v___y_7712_: *mut leanh::LeanObject,
    mut v___y_7713_: *mut leanh::LeanObject,
    mut v___y_7714_: *mut leanh::LeanObject,
    mut v___y_7715_: *mut leanh::LeanObject,
    mut v___y_7716_: *mut leanh::LeanObject,
    mut v___y_7717_: *mut leanh::LeanObject,
    mut v___y_7718_: *mut leanh::LeanObject,
    mut v___y_7719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_977__boxed_7720_: u8 = 0;
    let mut v_res_7721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_977__boxed_7720_ = (leanh::lean_unbox(v___x_7709_) as u8);
    v_res_7721_ = l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(
        v_e_7708_,
        v___x_977__boxed_7720_,
        v_tac_7710_,
        v___y_7711_,
        v___y_7712_,
        v___y_7713_,
        v___y_7714_,
        v___y_7715_,
        v___y_7716_,
        v___y_7717_,
        v___y_7718_,
    );
    leanh::lean_dec(v___y_7714_);
    leanh::lean_dec_ref(v___y_7713_);
    leanh::lean_dec(v___y_7712_);
    leanh::lean_dec_ref(v___y_7711_);
    return v_res_7721_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalApplyLikeTactic(
    mut v_tac_7722_: *mut leanh::LeanObject,
    mut v_e_7723_: *mut leanh::LeanObject,
    mut v_a_7724_: *mut leanh::LeanObject,
    mut v_a_7725_: *mut leanh::LeanObject,
    mut v_a_7726_: *mut leanh::LeanObject,
    mut v_a_7727_: *mut leanh::LeanObject,
    mut v_a_7728_: *mut leanh::LeanObject,
    mut v_a_7729_: *mut leanh::LeanObject,
    mut v_a_7730_: *mut leanh::LeanObject,
    mut v_a_7731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7733_: u8 = 0;
    let mut v___x_7734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7733_ = 1;
    v___x_7734_ = leanh::lean_box((v___x_7733_) as usize);
    v___f_7735_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed as *mut core::ffi::c_void,
        12,
        3,
    );
    leanh::lean_closure_set(v___f_7735_, 0, v_e_7723_);
    leanh::lean_closure_set(v___f_7735_, 1, v___x_7734_);
    leanh::lean_closure_set(v___f_7735_, 2, v_tac_7722_);
    v___x_7736_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_7735_,
        v_a_7724_,
        v_a_7725_,
        v_a_7726_,
        v_a_7727_,
        v_a_7728_,
        v_a_7729_,
        v_a_7730_,
        v_a_7731_,
    );
    return v___x_7736_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalApplyLikeTactic___boxed(
    mut v_tac_7737_: *mut leanh::LeanObject,
    mut v_e_7738_: *mut leanh::LeanObject,
    mut v_a_7739_: *mut leanh::LeanObject,
    mut v_a_7740_: *mut leanh::LeanObject,
    mut v_a_7741_: *mut leanh::LeanObject,
    mut v_a_7742_: *mut leanh::LeanObject,
    mut v_a_7743_: *mut leanh::LeanObject,
    mut v_a_7744_: *mut leanh::LeanObject,
    mut v_a_7745_: *mut leanh::LeanObject,
    mut v_a_7746_: *mut leanh::LeanObject,
    mut v_a_7747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7748_ = l_Lean_Elab_Tactic_evalApplyLikeTactic(
        v_tac_7737_,
        v_e_7738_,
        v_a_7739_,
        v_a_7740_,
        v_a_7741_,
        v_a_7742_,
        v_a_7743_,
        v_a_7744_,
        v_a_7745_,
        v_a_7746_,
    );
    leanh::lean_dec(v_a_7746_);
    leanh::lean_dec_ref(v_a_7745_);
    leanh::lean_dec(v_a_7744_);
    leanh::lean_dec_ref(v_a_7743_);
    leanh::lean_dec(v_a_7742_);
    leanh::lean_dec_ref(v_a_7741_);
    leanh::lean_dec(v_a_7740_);
    leanh::lean_dec_ref(v_a_7739_);
    return v_res_7748_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalApply___lam__0(
    mut v___x_7749_: u8,
    mut v_g_7750_: *mut leanh::LeanObject,
    mut v_e_7751_: *mut leanh::LeanObject,
    mut v___y_7752_: *mut leanh::LeanObject,
    mut v___y_7753_: *mut leanh::LeanObject,
    mut v___y_7754_: *mut leanh::LeanObject,
    mut v___y_7755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7757_: u8 = 0;
    let mut v___x_7758_: u8 = 0;
    let mut v___x_7759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7757_ = 0;
    v___x_7758_ = 0;
    v___x_7759_ = leanh::lean_alloc_ctor(0, 0, (4) as u32);
    leanh::lean_ctor_set_uint8(v___x_7759_, 0 as u32, v___x_7757_);
    leanh::lean_ctor_set_uint8(v___x_7759_, 1 as u32, v___x_7749_);
    leanh::lean_ctor_set_uint8(v___x_7759_, 2 as u32, v___x_7758_);
    leanh::lean_ctor_set_uint8(v___x_7759_, 3 as u32, v___x_7749_);
    v___x_7760_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_refineCore___lam__1___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once),
        _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5,
    );
    leanh::lean_inc_ref(v_e_7751_);
    v___x_7761_ = l_Lean_MessageData_ofExpr(v_e_7751_);
    v___x_7762_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7762_, 0, v___x_7760_);
    leanh::lean_ctor_set(v___x_7762_, 1, v___x_7761_);
    v___x_7763_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7763_, 0, v___x_7762_);
    leanh::lean_ctor_set(v___x_7763_, 1, v___x_7760_);
    v___x_7764_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7764_, 0, v___x_7763_);
    v___x_7765_ = l_Lean_MVarId_apply(
        v_g_7750_,
        v_e_7751_,
        v___x_7759_,
        v___x_7764_,
        v___y_7752_,
        v___y_7753_,
        v___y_7754_,
        v___y_7755_,
    );
    return v___x_7765_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalApply___lam__0___boxed(
    mut v___x_7766_: *mut leanh::LeanObject,
    mut v_g_7767_: *mut leanh::LeanObject,
    mut v_e_7768_: *mut leanh::LeanObject,
    mut v___y_7769_: *mut leanh::LeanObject,
    mut v___y_7770_: *mut leanh::LeanObject,
    mut v___y_7771_: *mut leanh::LeanObject,
    mut v___y_7772_: *mut leanh::LeanObject,
    mut v___y_7773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_233__boxed_7774_: u8 = 0;
    let mut v_res_7775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_233__boxed_7774_ = (leanh::lean_unbox(v___x_7766_) as u8);
    v_res_7775_ = l_Lean_Elab_Tactic_evalApply___lam__0(
        v___x_233__boxed_7774_,
        v_g_7767_,
        v_e_7768_,
        v___y_7769_,
        v___y_7770_,
        v___y_7771_,
        v___y_7772_,
    );
    leanh::lean_dec(v___y_7772_);
    leanh::lean_dec_ref(v___y_7771_);
    leanh::lean_dec(v___y_7770_);
    leanh::lean_dec_ref(v___y_7769_);
    return v_res_7775_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalApply(
    mut v_stx_7782_: *mut leanh::LeanObject,
    mut v_a_7783_: *mut leanh::LeanObject,
    mut v_a_7784_: *mut leanh::LeanObject,
    mut v_a_7785_: *mut leanh::LeanObject,
    mut v_a_7786_: *mut leanh::LeanObject,
    mut v_a_7787_: *mut leanh::LeanObject,
    mut v_a_7788_: *mut leanh::LeanObject,
    mut v_a_7789_: *mut leanh::LeanObject,
    mut v_a_7790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: u8 = 0;
    v___x_7792_ = l_Lean_Elab_Tactic_evalApply___closed__1;
    leanh::lean_inc(v_stx_7782_);
    v___x_7793_ = l_Lean_Syntax_isOfKind(v_stx_7782_, v___x_7792_);
    if v___x_7793_ == 0 {
        let mut v___x_7794_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_7782_);
        v___x_7794_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg(
            );
        return v___x_7794_;
    } else {
        let mut v___x_7795_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7796_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7797_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7798_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7799_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7795_ = leanh::lean_box((v___x_7793_) as usize);
        v___f_7796_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_evalApply___lam__0___boxed as *mut core::ffi::c_void,
            8,
            1,
        );
        leanh::lean_closure_set(v___f_7796_, 0, v___x_7795_);
        v___x_7797_ = leanh::lean_unsigned_to_nat(1);
        v___x_7798_ = l_Lean_Syntax_getArg(v_stx_7782_, v___x_7797_);
        leanh::lean_dec(v_stx_7782_);
        v___x_7799_ = l_Lean_Elab_Tactic_evalApplyLikeTactic(
            v___f_7796_,
            v___x_7798_,
            v_a_7783_,
            v_a_7784_,
            v_a_7785_,
            v_a_7786_,
            v_a_7787_,
            v_a_7788_,
            v_a_7789_,
            v_a_7790_,
        );
        return v___x_7799_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalApply___boxed(
    mut v_stx_7800_: *mut leanh::LeanObject,
    mut v_a_7801_: *mut leanh::LeanObject,
    mut v_a_7802_: *mut leanh::LeanObject,
    mut v_a_7803_: *mut leanh::LeanObject,
    mut v_a_7804_: *mut leanh::LeanObject,
    mut v_a_7805_: *mut leanh::LeanObject,
    mut v_a_7806_: *mut leanh::LeanObject,
    mut v_a_7807_: *mut leanh::LeanObject,
    mut v_a_7808_: *mut leanh::LeanObject,
    mut v_a_7809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7810_ = l_Lean_Elab_Tactic_evalApply(
        v_stx_7800_,
        v_a_7801_,
        v_a_7802_,
        v_a_7803_,
        v_a_7804_,
        v_a_7805_,
        v_a_7806_,
        v_a_7807_,
        v_a_7808_,
    );
    leanh::lean_dec(v_a_7808_);
    leanh::lean_dec_ref(v_a_7807_);
    leanh::lean_dec(v_a_7806_);
    leanh::lean_dec_ref(v_a_7805_);
    leanh::lean_dec(v_a_7804_);
    leanh::lean_dec_ref(v_a_7803_);
    leanh::lean_dec(v_a_7802_);
    leanh::lean_dec_ref(v_a_7801_);
    return v_res_7810_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1()
-> *mut leanh::LeanObject {
    let mut v___x_7818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7818_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7819_ = l_Lean_Elab_Tactic_evalApply___closed__1;
    v___x_7820_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1;
    v___x_7821_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalApply___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7822_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7818_,
        v___x_7819_,
        v___x_7820_,
        v___x_7821_,
    );
    return v___x_7822_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___boxed(
    mut v_a_7823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7824_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1();
    return v_res_7824_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_7851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7851_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1;
    v___x_7852_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6;
    v___x_7853_ = l_Lean_addBuiltinDeclarationRanges(v___x_7851_, v___x_7852_);
    return v___x_7853_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___boxed(
    mut v_a_7854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7855_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3();
    return v_res_7855_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0(
    mut v___y_7860_: *mut leanh::LeanObject,
    mut v___y_7861_: *mut leanh::LeanObject,
    mut v___y_7862_: *mut leanh::LeanObject,
    mut v___y_7863_: *mut leanh::LeanObject,
    mut v___y_7864_: *mut leanh::LeanObject,
    mut v___y_7865_: *mut leanh::LeanObject,
    mut v___y_7866_: *mut leanh::LeanObject,
    mut v___y_7867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7871_: u8 = 0;
    let mut v___x_7872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7880_: u8 = 0;
    let mut v___x_7882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7884_: u8 = 0;
    let mut v_a_7885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7888_: u8 = 0;
    let mut v___x_7890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7869_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_7861_,
                    v___y_7864_,
                    v___y_7865_,
                    v___y_7866_,
                    v___y_7867_,
                );
                if leanh::lean_obj_tag(v___x_7869_) == 0 {
                    v_a_7870_ = leanh::lean_ctor_get(v___x_7869_, 0);
                    leanh::lean_inc(v_a_7870_);
                    leanh::lean_dec_ref_known(v___x_7869_, 1);
                    v___x_7871_ = 0;
                    v___x_7872_ = l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0;
                    v___x_7873_ = l_Lean_MVarId_constructor(
                        v_a_7870_,
                        v___x_7872_,
                        v___y_7864_,
                        v___y_7865_,
                        v___y_7866_,
                        v___y_7867_,
                    );
                    if leanh::lean_obj_tag(v___x_7873_) == 0 {
                        v_a_7874_ = leanh::lean_ctor_get(v___x_7873_, 0);
                        leanh::lean_inc(v_a_7874_);
                        leanh::lean_dec_ref_known(v___x_7873_, 1);
                        v___x_7875_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(
                            v___x_7871_,
                            v___y_7862_,
                            v___y_7863_,
                            v___y_7864_,
                            v___y_7865_,
                            v___y_7866_,
                            v___y_7867_,
                        );
                        if leanh::lean_obj_tag(v___x_7875_) == 0 {
                            leanh::lean_dec_ref_known(v___x_7875_, 1);
                            v___x_7876_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v_a_7874_,
                                v___y_7861_,
                                v___y_7864_,
                                v___y_7865_,
                                v___y_7866_,
                                v___y_7867_,
                            );
                            return v___x_7876_;
                        } else {
                            leanh::lean_dec(v_a_7874_);
                            return v___x_7875_;
                        }
                    } else {
                        v_a_7877_ = leanh::lean_ctor_get(v___x_7873_, 0);
                        v_isSharedCheck_7884_ =
                            (!leanh::lean_is_exclusive(v___x_7873_)) as u8;
                        if v_isSharedCheck_7884_ == 0 {
                            v___x_7879_ = v___x_7873_;
                            v_isShared_7880_ = v_isSharedCheck_7884_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7877_);
                            leanh::lean_dec(v___x_7873_);
                            v___x_7879_ = leanh::lean_box(0);
                            v_isShared_7880_ = v_isSharedCheck_7884_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_7885_ = leanh::lean_ctor_get(v___x_7869_, 0);
                    v_isSharedCheck_7892_ = (!leanh::lean_is_exclusive(v___x_7869_)) as u8;
                    if v_isSharedCheck_7892_ == 0 {
                        v___x_7887_ = v___x_7869_;
                        v_isShared_7888_ = v_isSharedCheck_7892_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7885_);
                        leanh::lean_dec(v___x_7869_);
                        v___x_7887_ = leanh::lean_box(0);
                        v_isShared_7888_ = v_isSharedCheck_7892_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7880_ == 0 {
                    v___x_7882_ = v___x_7879_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7883_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7883_, 0, v_a_7877_);
                    v___x_7882_ = v_reuseFailAlloc_7883_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7882_;
            }
            3 => {
                if v_isShared_7888_ == 0 {
                    v___x_7890_ = v___x_7887_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7891_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7891_, 0, v_a_7885_);
                    v___x_7890_ = v_reuseFailAlloc_7891_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___boxed(
    mut v___y_7893_: *mut leanh::LeanObject,
    mut v___y_7894_: *mut leanh::LeanObject,
    mut v___y_7895_: *mut leanh::LeanObject,
    mut v___y_7896_: *mut leanh::LeanObject,
    mut v___y_7897_: *mut leanh::LeanObject,
    mut v___y_7898_: *mut leanh::LeanObject,
    mut v___y_7899_: *mut leanh::LeanObject,
    mut v___y_7900_: *mut leanh::LeanObject,
    mut v___y_7901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7902_ = l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0(
        v___y_7893_,
        v___y_7894_,
        v___y_7895_,
        v___y_7896_,
        v___y_7897_,
        v___y_7898_,
        v___y_7899_,
        v___y_7900_,
    );
    leanh::lean_dec(v___y_7900_);
    leanh::lean_dec_ref(v___y_7899_);
    leanh::lean_dec(v___y_7898_);
    leanh::lean_dec_ref(v___y_7897_);
    leanh::lean_dec(v___y_7896_);
    leanh::lean_dec_ref(v___y_7895_);
    leanh::lean_dec(v___y_7894_);
    leanh::lean_dec_ref(v___y_7893_);
    return v_res_7902_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalConstructor___redArg(
    mut v_a_7904_: *mut leanh::LeanObject,
    mut v_a_7905_: *mut leanh::LeanObject,
    mut v_a_7906_: *mut leanh::LeanObject,
    mut v_a_7907_: *mut leanh::LeanObject,
    mut v_a_7908_: *mut leanh::LeanObject,
    mut v_a_7909_: *mut leanh::LeanObject,
    mut v_a_7910_: *mut leanh::LeanObject,
    mut v_a_7911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7913_ = l_Lean_Elab_Tactic_evalConstructor___redArg___closed__0;
    v___x_7914_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_7913_,
        v_a_7904_,
        v_a_7905_,
        v_a_7906_,
        v_a_7907_,
        v_a_7908_,
        v_a_7909_,
        v_a_7910_,
        v_a_7911_,
    );
    return v___x_7914_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalConstructor___redArg___boxed(
    mut v_a_7915_: *mut leanh::LeanObject,
    mut v_a_7916_: *mut leanh::LeanObject,
    mut v_a_7917_: *mut leanh::LeanObject,
    mut v_a_7918_: *mut leanh::LeanObject,
    mut v_a_7919_: *mut leanh::LeanObject,
    mut v_a_7920_: *mut leanh::LeanObject,
    mut v_a_7921_: *mut leanh::LeanObject,
    mut v_a_7922_: *mut leanh::LeanObject,
    mut v_a_7923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7924_ = l_Lean_Elab_Tactic_evalConstructor___redArg(
        v_a_7915_, v_a_7916_, v_a_7917_, v_a_7918_, v_a_7919_, v_a_7920_, v_a_7921_, v_a_7922_,
    );
    leanh::lean_dec(v_a_7922_);
    leanh::lean_dec_ref(v_a_7921_);
    leanh::lean_dec(v_a_7920_);
    leanh::lean_dec_ref(v_a_7919_);
    leanh::lean_dec(v_a_7918_);
    leanh::lean_dec_ref(v_a_7917_);
    leanh::lean_dec(v_a_7916_);
    leanh::lean_dec_ref(v_a_7915_);
    return v_res_7924_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalConstructor(
    mut v_x_7925_: *mut leanh::LeanObject,
    mut v_a_7926_: *mut leanh::LeanObject,
    mut v_a_7927_: *mut leanh::LeanObject,
    mut v_a_7928_: *mut leanh::LeanObject,
    mut v_a_7929_: *mut leanh::LeanObject,
    mut v_a_7930_: *mut leanh::LeanObject,
    mut v_a_7931_: *mut leanh::LeanObject,
    mut v_a_7932_: *mut leanh::LeanObject,
    mut v_a_7933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7935_ = l_Lean_Elab_Tactic_evalConstructor___redArg(
        v_a_7926_, v_a_7927_, v_a_7928_, v_a_7929_, v_a_7930_, v_a_7931_, v_a_7932_, v_a_7933_,
    );
    return v___x_7935_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalConstructor___boxed(
    mut v_x_7936_: *mut leanh::LeanObject,
    mut v_a_7937_: *mut leanh::LeanObject,
    mut v_a_7938_: *mut leanh::LeanObject,
    mut v_a_7939_: *mut leanh::LeanObject,
    mut v_a_7940_: *mut leanh::LeanObject,
    mut v_a_7941_: *mut leanh::LeanObject,
    mut v_a_7942_: *mut leanh::LeanObject,
    mut v_a_7943_: *mut leanh::LeanObject,
    mut v_a_7944_: *mut leanh::LeanObject,
    mut v_a_7945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7946_ = l_Lean_Elab_Tactic_evalConstructor(
        v_x_7936_, v_a_7937_, v_a_7938_, v_a_7939_, v_a_7940_, v_a_7941_, v_a_7942_, v_a_7943_,
        v_a_7944_,
    );
    leanh::lean_dec(v_a_7944_);
    leanh::lean_dec_ref(v_a_7943_);
    leanh::lean_dec(v_a_7942_);
    leanh::lean_dec_ref(v_a_7941_);
    leanh::lean_dec(v_a_7940_);
    leanh::lean_dec_ref(v_a_7939_);
    leanh::lean_dec(v_a_7938_);
    leanh::lean_dec_ref(v_a_7937_);
    leanh::lean_dec(v_x_7936_);
    return v_res_7946_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1()
-> *mut leanh::LeanObject {
    let mut v___x_7960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7960_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7961_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1;
    v___x_7962_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3;
    v___x_7963_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalConstructor___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7964_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7960_,
        v___x_7961_,
        v___x_7962_,
        v___x_7963_,
    );
    return v___x_7964_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___boxed(
    mut v_a_7965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7966_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1();
    return v_res_7966_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_7993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7993_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3;
    v___x_7994_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6;
    v___x_7995_ = l_Lean_addBuiltinDeclarationRanges(v___x_7993_, v___x_7994_);
    return v___x_7995_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___boxed(
    mut v_a_7996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7997_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3();
    return v_res_7997_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalWithReducible___closed__0() -> u64 {
    let mut v___x_7998_: u8 = 0;
    let mut v___x_7999_: u64 = 0;
    v___x_7998_ = 2;
    v___x_7999_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_7998_);
    return v___x_7999_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalWithReducible(
    mut v_stx_8000_: *mut leanh::LeanObject,
    mut v_a_8001_: *mut leanh::LeanObject,
    mut v_a_8002_: *mut leanh::LeanObject,
    mut v_a_8003_: *mut leanh::LeanObject,
    mut v_a_8004_: *mut leanh::LeanObject,
    mut v_a_8005_: *mut leanh::LeanObject,
    mut v_a_8006_: *mut leanh::LeanObject,
    mut v_a_8007_: *mut leanh::LeanObject,
    mut v_a_8008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_8011_: u8 = 0;
    let mut v_ctxApprox_8012_: u8 = 0;
    let mut v_quasiPatternApprox_8013_: u8 = 0;
    let mut v_constApprox_8014_: u8 = 0;
    let mut v_isDefEqStuckEx_8015_: u8 = 0;
    let mut v_unificationHints_8016_: u8 = 0;
    let mut v_proofIrrelevance_8017_: u8 = 0;
    let mut v_assignSyntheticOpaque_8018_: u8 = 0;
    let mut v_offsetCnstrs_8019_: u8 = 0;
    let mut v_etaStruct_8020_: u8 = 0;
    let mut v_univApprox_8021_: u8 = 0;
    let mut v_iota_8022_: u8 = 0;
    let mut v_beta_8023_: u8 = 0;
    let mut v_proj_8024_: u8 = 0;
    let mut v_zeta_8025_: u8 = 0;
    let mut v_zetaDelta_8026_: u8 = 0;
    let mut v_zetaUnused_8027_: u8 = 0;
    let mut v_zetaHave_8028_: u8 = 0;
    let mut v___x_8030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8031_: u8 = 0;
    let mut v_trackZetaDelta_8032_: u8 = 0;
    let mut v_zetaDeltaSet_8033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_8034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_8035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_8036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_8037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_8038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_8039_: u8 = 0;
    let mut v_inTypeClassResolution_8040_: u8 = 0;
    let mut v_cacheInferType_8041_: u8 = 0;
    let mut v___x_8042_: u8 = 0;
    let mut v_config_8044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8045_: u64 = 0;
    let mut v___x_8046_: u64 = 0;
    let mut v___x_8047_: u64 = 0;
    let mut v___x_8048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8050_: u64 = 0;
    let mut v___x_8051_: u64 = 0;
    let mut v_key_8052_: u64 = 0;
    let mut v___x_8053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8059_: u8 = 0;
    let mut v___x_8061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8063_: u8 = 0;
    let mut v_reuseFailAlloc_8064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8010_ = l_Lean_Meta_Context_config(v_a_8005_);
                v_foApprox_8011_ = leanh::lean_ctor_get_uint8(v___x_8010_, 0 as u32);
                v_ctxApprox_8012_ = leanh::lean_ctor_get_uint8(v___x_8010_, 1 as u32);
                v_quasiPatternApprox_8013_ =
                    leanh::lean_ctor_get_uint8(v___x_8010_, 2 as u32);
                v_constApprox_8014_ = leanh::lean_ctor_get_uint8(v___x_8010_, 3 as u32);
                v_isDefEqStuckEx_8015_ = leanh::lean_ctor_get_uint8(v___x_8010_, 4 as u32);
                v_unificationHints_8016_ = leanh::lean_ctor_get_uint8(v___x_8010_, 5 as u32);
                v_proofIrrelevance_8017_ = leanh::lean_ctor_get_uint8(v___x_8010_, 6 as u32);
                v_assignSyntheticOpaque_8018_ =
                    leanh::lean_ctor_get_uint8(v___x_8010_, 7 as u32);
                v_offsetCnstrs_8019_ = leanh::lean_ctor_get_uint8(v___x_8010_, 8 as u32);
                v_etaStruct_8020_ = leanh::lean_ctor_get_uint8(v___x_8010_, 10 as u32);
                v_univApprox_8021_ = leanh::lean_ctor_get_uint8(v___x_8010_, 11 as u32);
                v_iota_8022_ = leanh::lean_ctor_get_uint8(v___x_8010_, 12 as u32);
                v_beta_8023_ = leanh::lean_ctor_get_uint8(v___x_8010_, 13 as u32);
                v_proj_8024_ = leanh::lean_ctor_get_uint8(v___x_8010_, 14 as u32);
                v_zeta_8025_ = leanh::lean_ctor_get_uint8(v___x_8010_, 15 as u32);
                v_zetaDelta_8026_ = leanh::lean_ctor_get_uint8(v___x_8010_, 16 as u32);
                v_zetaUnused_8027_ = leanh::lean_ctor_get_uint8(v___x_8010_, 17 as u32);
                v_zetaHave_8028_ = leanh::lean_ctor_get_uint8(v___x_8010_, 18 as u32);
                v_isSharedCheck_8065_ = (!leanh::lean_is_exclusive(v___x_8010_)) as u8;
                if v_isSharedCheck_8065_ == 0 {
                    v___x_8030_ = v___x_8010_;
                    v_isShared_8031_ = v_isSharedCheck_8065_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_8010_);
                    v___x_8030_ = leanh::lean_box(0);
                    v_isShared_8031_ = v_isSharedCheck_8065_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_8032_ = leanh::lean_ctor_get_uint8(
                    v_a_8005_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_8033_ = leanh::lean_ctor_get(v_a_8005_, 1);
                v_lctx_8034_ = leanh::lean_ctor_get(v_a_8005_, 2);
                v_localInstances_8035_ = leanh::lean_ctor_get(v_a_8005_, 3);
                v_defEqCtx_x3f_8036_ = leanh::lean_ctor_get(v_a_8005_, 4);
                v_synthPendingDepth_8037_ = leanh::lean_ctor_get(v_a_8005_, 5);
                v_canUnfold_x3f_8038_ = leanh::lean_ctor_get(v_a_8005_, 6);
                v_univApprox_8039_ = leanh::lean_ctor_get_uint8(
                    v_a_8005_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_8040_ = leanh::lean_ctor_get_uint8(
                    v_a_8005_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_8041_ = leanh::lean_ctor_get_uint8(
                    v_a_8005_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_8042_ = 2;
                if v_isShared_8031_ == 0 {
                    v_config_8044_ = v___x_8030_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8064_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        0 as u32,
                        v_foApprox_8011_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        1 as u32,
                        v_ctxApprox_8012_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        2 as u32,
                        v_quasiPatternApprox_8013_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        3 as u32,
                        v_constApprox_8014_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        4 as u32,
                        v_isDefEqStuckEx_8015_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        5 as u32,
                        v_unificationHints_8016_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        6 as u32,
                        v_proofIrrelevance_8017_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        7 as u32,
                        v_assignSyntheticOpaque_8018_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        8 as u32,
                        v_offsetCnstrs_8019_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        10 as u32,
                        v_etaStruct_8020_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        11 as u32,
                        v_univApprox_8021_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        12 as u32,
                        v_iota_8022_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        13 as u32,
                        v_beta_8023_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        14 as u32,
                        v_proj_8024_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        15 as u32,
                        v_zeta_8025_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        16 as u32,
                        v_zetaDelta_8026_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        17 as u32,
                        v_zetaUnused_8027_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8064_,
                        18 as u32,
                        v_zetaHave_8028_,
                    );
                    v_config_8044_ = v_reuseFailAlloc_8064_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_8044_, 9 as u32, v___x_8042_);
                v___x_8045_ = l_Lean_Meta_Context_configKey(v_a_8005_);
                v___x_8046_ = 3u64;
                v___x_8047_ = lean_uint64_shift_right(v___x_8045_, v___x_8046_);
                v___x_8048_ = leanh::lean_unsigned_to_nat(1);
                v___x_8049_ = l_Lean_Syntax_getArg(v_stx_8000_, v___x_8048_);
                v___x_8050_ = lean_uint64_shift_left(v___x_8047_, v___x_8046_);
                v___x_8051_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalWithReducible___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalWithReducible___closed__0_once),
                    _init_l_Lean_Elab_Tactic_evalWithReducible___closed__0,
                );
                v_key_8052_ = lean_uint64_lor(v___x_8050_, v___x_8051_);
                v___x_8053_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_8053_, 0, v_config_8044_);
                leanh::lean_ctor_set_uint64(
                    v___x_8053_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_8052_,
                );
                leanh::lean_inc(v_canUnfold_x3f_8038_);
                leanh::lean_inc(v_synthPendingDepth_8037_);
                leanh::lean_inc(v_defEqCtx_x3f_8036_);
                leanh::lean_inc_ref(v_localInstances_8035_);
                leanh::lean_inc_ref(v_lctx_8034_);
                leanh::lean_inc(v_zetaDeltaSet_8033_);
                v___x_8054_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_8054_, 0, v___x_8053_);
                leanh::lean_ctor_set(v___x_8054_, 1, v_zetaDeltaSet_8033_);
                leanh::lean_ctor_set(v___x_8054_, 2, v_lctx_8034_);
                leanh::lean_ctor_set(v___x_8054_, 3, v_localInstances_8035_);
                leanh::lean_ctor_set(v___x_8054_, 4, v_defEqCtx_x3f_8036_);
                leanh::lean_ctor_set(v___x_8054_, 5, v_synthPendingDepth_8037_);
                leanh::lean_ctor_set(v___x_8054_, 6, v_canUnfold_x3f_8038_);
                leanh::lean_ctor_set_uint8(
                    v___x_8054_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_8032_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8054_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_8039_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8054_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_8040_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8054_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_8041_,
                );
                v___x_8055_ = l_Lean_Elab_Tactic_evalTactic(
                    v___x_8049_,
                    v_a_8001_,
                    v_a_8002_,
                    v_a_8003_,
                    v_a_8004_,
                    v___x_8054_,
                    v_a_8006_,
                    v_a_8007_,
                    v_a_8008_,
                );
                leanh::lean_dec_ref_known(v___x_8054_, 7);
                if leanh::lean_obj_tag(v___x_8055_) == 0 {
                    v_a_8056_ = leanh::lean_ctor_get(v___x_8055_, 0);
                    v_isSharedCheck_8063_ = (!leanh::lean_is_exclusive(v___x_8055_)) as u8;
                    if v_isSharedCheck_8063_ == 0 {
                        v___x_8058_ = v___x_8055_;
                        v_isShared_8059_ = v_isSharedCheck_8063_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8056_);
                        leanh::lean_dec(v___x_8055_);
                        v___x_8058_ = leanh::lean_box(0);
                        v_isShared_8059_ = v_isSharedCheck_8063_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_8055_;
                }
            }
            3 => {
                if v_isShared_8059_ == 0 {
                    v___x_8061_ = v___x_8058_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8062_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8062_, 0, v_a_8056_);
                    v___x_8061_ = v_reuseFailAlloc_8062_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalWithReducible___boxed(
    mut v_stx_8066_: *mut leanh::LeanObject,
    mut v_a_8067_: *mut leanh::LeanObject,
    mut v_a_8068_: *mut leanh::LeanObject,
    mut v_a_8069_: *mut leanh::LeanObject,
    mut v_a_8070_: *mut leanh::LeanObject,
    mut v_a_8071_: *mut leanh::LeanObject,
    mut v_a_8072_: *mut leanh::LeanObject,
    mut v_a_8073_: *mut leanh::LeanObject,
    mut v_a_8074_: *mut leanh::LeanObject,
    mut v_a_8075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8076_ = l_Lean_Elab_Tactic_evalWithReducible(
        v_stx_8066_,
        v_a_8067_,
        v_a_8068_,
        v_a_8069_,
        v_a_8070_,
        v_a_8071_,
        v_a_8072_,
        v_a_8073_,
        v_a_8074_,
    );
    leanh::lean_dec(v_a_8074_);
    leanh::lean_dec_ref(v_a_8073_);
    leanh::lean_dec(v_a_8072_);
    leanh::lean_dec_ref(v_a_8071_);
    leanh::lean_dec(v_a_8070_);
    leanh::lean_dec_ref(v_a_8069_);
    leanh::lean_dec(v_a_8068_);
    leanh::lean_dec_ref(v_a_8067_);
    leanh::lean_dec(v_stx_8066_);
    return v_res_8076_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1()
-> *mut leanh::LeanObject {
    let mut v___x_8090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8090_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_8091_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1;
    v___x_8092_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3;
    v___x_8093_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalWithReducible___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_8094_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_8090_,
        v___x_8091_,
        v___x_8092_,
        v___x_8093_,
    );
    return v___x_8094_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___boxed(
    mut v_a_8095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8096_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1();
    return v_res_8096_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_8123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8123_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3;
    v___x_8124_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6;
    v___x_8125_ = l_Lean_addBuiltinDeclarationRanges(v___x_8123_, v___x_8124_);
    return v___x_8125_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___boxed(
    mut v_a_8126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8127_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3();
    return v_res_8127_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0() -> u64 {
    let mut v___x_8128_: u8 = 0;
    let mut v___x_8129_: u64 = 0;
    v___x_8128_ = 3;
    v___x_8129_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_8128_);
    return v___x_8129_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalWithReducibleAndInstances(
    mut v_stx_8130_: *mut leanh::LeanObject,
    mut v_a_8131_: *mut leanh::LeanObject,
    mut v_a_8132_: *mut leanh::LeanObject,
    mut v_a_8133_: *mut leanh::LeanObject,
    mut v_a_8134_: *mut leanh::LeanObject,
    mut v_a_8135_: *mut leanh::LeanObject,
    mut v_a_8136_: *mut leanh::LeanObject,
    mut v_a_8137_: *mut leanh::LeanObject,
    mut v_a_8138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_8141_: u8 = 0;
    let mut v_ctxApprox_8142_: u8 = 0;
    let mut v_quasiPatternApprox_8143_: u8 = 0;
    let mut v_constApprox_8144_: u8 = 0;
    let mut v_isDefEqStuckEx_8145_: u8 = 0;
    let mut v_unificationHints_8146_: u8 = 0;
    let mut v_proofIrrelevance_8147_: u8 = 0;
    let mut v_assignSyntheticOpaque_8148_: u8 = 0;
    let mut v_offsetCnstrs_8149_: u8 = 0;
    let mut v_etaStruct_8150_: u8 = 0;
    let mut v_univApprox_8151_: u8 = 0;
    let mut v_iota_8152_: u8 = 0;
    let mut v_beta_8153_: u8 = 0;
    let mut v_proj_8154_: u8 = 0;
    let mut v_zeta_8155_: u8 = 0;
    let mut v_zetaDelta_8156_: u8 = 0;
    let mut v_zetaUnused_8157_: u8 = 0;
    let mut v_zetaHave_8158_: u8 = 0;
    let mut v___x_8160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8161_: u8 = 0;
    let mut v_trackZetaDelta_8162_: u8 = 0;
    let mut v_zetaDeltaSet_8163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_8164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_8165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_8166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_8167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_8168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_8169_: u8 = 0;
    let mut v_inTypeClassResolution_8170_: u8 = 0;
    let mut v_cacheInferType_8171_: u8 = 0;
    let mut v___x_8172_: u8 = 0;
    let mut v_config_8174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8175_: u64 = 0;
    let mut v___x_8176_: u64 = 0;
    let mut v___x_8177_: u64 = 0;
    let mut v___x_8178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8180_: u64 = 0;
    let mut v___x_8181_: u64 = 0;
    let mut v_key_8182_: u64 = 0;
    let mut v___x_8183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8189_: u8 = 0;
    let mut v___x_8191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8193_: u8 = 0;
    let mut v_reuseFailAlloc_8194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8140_ = l_Lean_Meta_Context_config(v_a_8135_);
                v_foApprox_8141_ = leanh::lean_ctor_get_uint8(v___x_8140_, 0 as u32);
                v_ctxApprox_8142_ = leanh::lean_ctor_get_uint8(v___x_8140_, 1 as u32);
                v_quasiPatternApprox_8143_ =
                    leanh::lean_ctor_get_uint8(v___x_8140_, 2 as u32);
                v_constApprox_8144_ = leanh::lean_ctor_get_uint8(v___x_8140_, 3 as u32);
                v_isDefEqStuckEx_8145_ = leanh::lean_ctor_get_uint8(v___x_8140_, 4 as u32);
                v_unificationHints_8146_ = leanh::lean_ctor_get_uint8(v___x_8140_, 5 as u32);
                v_proofIrrelevance_8147_ = leanh::lean_ctor_get_uint8(v___x_8140_, 6 as u32);
                v_assignSyntheticOpaque_8148_ =
                    leanh::lean_ctor_get_uint8(v___x_8140_, 7 as u32);
                v_offsetCnstrs_8149_ = leanh::lean_ctor_get_uint8(v___x_8140_, 8 as u32);
                v_etaStruct_8150_ = leanh::lean_ctor_get_uint8(v___x_8140_, 10 as u32);
                v_univApprox_8151_ = leanh::lean_ctor_get_uint8(v___x_8140_, 11 as u32);
                v_iota_8152_ = leanh::lean_ctor_get_uint8(v___x_8140_, 12 as u32);
                v_beta_8153_ = leanh::lean_ctor_get_uint8(v___x_8140_, 13 as u32);
                v_proj_8154_ = leanh::lean_ctor_get_uint8(v___x_8140_, 14 as u32);
                v_zeta_8155_ = leanh::lean_ctor_get_uint8(v___x_8140_, 15 as u32);
                v_zetaDelta_8156_ = leanh::lean_ctor_get_uint8(v___x_8140_, 16 as u32);
                v_zetaUnused_8157_ = leanh::lean_ctor_get_uint8(v___x_8140_, 17 as u32);
                v_zetaHave_8158_ = leanh::lean_ctor_get_uint8(v___x_8140_, 18 as u32);
                v_isSharedCheck_8195_ = (!leanh::lean_is_exclusive(v___x_8140_)) as u8;
                if v_isSharedCheck_8195_ == 0 {
                    v___x_8160_ = v___x_8140_;
                    v_isShared_8161_ = v_isSharedCheck_8195_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_8140_);
                    v___x_8160_ = leanh::lean_box(0);
                    v_isShared_8161_ = v_isSharedCheck_8195_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_8162_ = leanh::lean_ctor_get_uint8(
                    v_a_8135_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_8163_ = leanh::lean_ctor_get(v_a_8135_, 1);
                v_lctx_8164_ = leanh::lean_ctor_get(v_a_8135_, 2);
                v_localInstances_8165_ = leanh::lean_ctor_get(v_a_8135_, 3);
                v_defEqCtx_x3f_8166_ = leanh::lean_ctor_get(v_a_8135_, 4);
                v_synthPendingDepth_8167_ = leanh::lean_ctor_get(v_a_8135_, 5);
                v_canUnfold_x3f_8168_ = leanh::lean_ctor_get(v_a_8135_, 6);
                v_univApprox_8169_ = leanh::lean_ctor_get_uint8(
                    v_a_8135_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_8170_ = leanh::lean_ctor_get_uint8(
                    v_a_8135_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_8171_ = leanh::lean_ctor_get_uint8(
                    v_a_8135_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_8172_ = 3;
                if v_isShared_8161_ == 0 {
                    v_config_8174_ = v___x_8160_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8194_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        0 as u32,
                        v_foApprox_8141_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        1 as u32,
                        v_ctxApprox_8142_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        2 as u32,
                        v_quasiPatternApprox_8143_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        3 as u32,
                        v_constApprox_8144_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        4 as u32,
                        v_isDefEqStuckEx_8145_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        5 as u32,
                        v_unificationHints_8146_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        6 as u32,
                        v_proofIrrelevance_8147_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        7 as u32,
                        v_assignSyntheticOpaque_8148_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        8 as u32,
                        v_offsetCnstrs_8149_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        10 as u32,
                        v_etaStruct_8150_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        11 as u32,
                        v_univApprox_8151_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        12 as u32,
                        v_iota_8152_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        13 as u32,
                        v_beta_8153_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        14 as u32,
                        v_proj_8154_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        15 as u32,
                        v_zeta_8155_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        16 as u32,
                        v_zetaDelta_8156_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        17 as u32,
                        v_zetaUnused_8157_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8194_,
                        18 as u32,
                        v_zetaHave_8158_,
                    );
                    v_config_8174_ = v_reuseFailAlloc_8194_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_8174_, 9 as u32, v___x_8172_);
                v___x_8175_ = l_Lean_Meta_Context_configKey(v_a_8135_);
                v___x_8176_ = 3u64;
                v___x_8177_ = lean_uint64_shift_right(v___x_8175_, v___x_8176_);
                v___x_8178_ = leanh::lean_unsigned_to_nat(1);
                v___x_8179_ = l_Lean_Syntax_getArg(v_stx_8130_, v___x_8178_);
                v___x_8180_ = lean_uint64_shift_left(v___x_8177_, v___x_8176_);
                v___x_8181_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0_once
                    ),
                    _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0,
                );
                v_key_8182_ = lean_uint64_lor(v___x_8180_, v___x_8181_);
                v___x_8183_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_8183_, 0, v_config_8174_);
                leanh::lean_ctor_set_uint64(
                    v___x_8183_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_8182_,
                );
                leanh::lean_inc(v_canUnfold_x3f_8168_);
                leanh::lean_inc(v_synthPendingDepth_8167_);
                leanh::lean_inc(v_defEqCtx_x3f_8166_);
                leanh::lean_inc_ref(v_localInstances_8165_);
                leanh::lean_inc_ref(v_lctx_8164_);
                leanh::lean_inc(v_zetaDeltaSet_8163_);
                v___x_8184_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_8184_, 0, v___x_8183_);
                leanh::lean_ctor_set(v___x_8184_, 1, v_zetaDeltaSet_8163_);
                leanh::lean_ctor_set(v___x_8184_, 2, v_lctx_8164_);
                leanh::lean_ctor_set(v___x_8184_, 3, v_localInstances_8165_);
                leanh::lean_ctor_set(v___x_8184_, 4, v_defEqCtx_x3f_8166_);
                leanh::lean_ctor_set(v___x_8184_, 5, v_synthPendingDepth_8167_);
                leanh::lean_ctor_set(v___x_8184_, 6, v_canUnfold_x3f_8168_);
                leanh::lean_ctor_set_uint8(
                    v___x_8184_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_8162_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8184_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_8169_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8184_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_8170_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8184_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_8171_,
                );
                v___x_8185_ = l_Lean_Elab_Tactic_evalTactic(
                    v___x_8179_,
                    v_a_8131_,
                    v_a_8132_,
                    v_a_8133_,
                    v_a_8134_,
                    v___x_8184_,
                    v_a_8136_,
                    v_a_8137_,
                    v_a_8138_,
                );
                leanh::lean_dec_ref_known(v___x_8184_, 7);
                if leanh::lean_obj_tag(v___x_8185_) == 0 {
                    v_a_8186_ = leanh::lean_ctor_get(v___x_8185_, 0);
                    v_isSharedCheck_8193_ = (!leanh::lean_is_exclusive(v___x_8185_)) as u8;
                    if v_isSharedCheck_8193_ == 0 {
                        v___x_8188_ = v___x_8185_;
                        v_isShared_8189_ = v_isSharedCheck_8193_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8186_);
                        leanh::lean_dec(v___x_8185_);
                        v___x_8188_ = leanh::lean_box(0);
                        v_isShared_8189_ = v_isSharedCheck_8193_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_8185_;
                }
            }
            3 => {
                if v_isShared_8189_ == 0 {
                    v___x_8191_ = v___x_8188_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8192_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8192_, 0, v_a_8186_);
                    v___x_8191_ = v_reuseFailAlloc_8192_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed(
    mut v_stx_8196_: *mut leanh::LeanObject,
    mut v_a_8197_: *mut leanh::LeanObject,
    mut v_a_8198_: *mut leanh::LeanObject,
    mut v_a_8199_: *mut leanh::LeanObject,
    mut v_a_8200_: *mut leanh::LeanObject,
    mut v_a_8201_: *mut leanh::LeanObject,
    mut v_a_8202_: *mut leanh::LeanObject,
    mut v_a_8203_: *mut leanh::LeanObject,
    mut v_a_8204_: *mut leanh::LeanObject,
    mut v_a_8205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8206_ = l_Lean_Elab_Tactic_evalWithReducibleAndInstances(
        v_stx_8196_,
        v_a_8197_,
        v_a_8198_,
        v_a_8199_,
        v_a_8200_,
        v_a_8201_,
        v_a_8202_,
        v_a_8203_,
        v_a_8204_,
    );
    leanh::lean_dec(v_a_8204_);
    leanh::lean_dec_ref(v_a_8203_);
    leanh::lean_dec(v_a_8202_);
    leanh::lean_dec_ref(v_a_8201_);
    leanh::lean_dec(v_a_8200_);
    leanh::lean_dec_ref(v_a_8199_);
    leanh::lean_dec(v_a_8198_);
    leanh::lean_dec_ref(v_a_8197_);
    leanh::lean_dec(v_stx_8196_);
    return v_res_8206_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1()
-> *mut leanh::LeanObject {
    let mut v___x_8220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8220_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_8221_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1;
    v___x_8222_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3;
    v___x_8223_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_8224_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_8220_,
        v___x_8221_,
        v___x_8222_,
        v___x_8223_,
    );
    return v___x_8224_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___boxed(
    mut v_a_8225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8226_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1();
    return v_res_8226_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_8253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8253_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3;
    v___x_8254_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6;
    v___x_8255_ = l_Lean_addBuiltinDeclarationRanges(v___x_8253_, v___x_8254_);
    return v___x_8255_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___boxed(
    mut v_a_8256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8257_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3();
    return v_res_8257_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0() -> u64 {
    let mut v___x_8258_: u8 = 0;
    let mut v___x_8259_: u64 = 0;
    v___x_8258_ = 0;
    v___x_8259_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_8258_);
    return v___x_8259_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalWithUnfoldingAll(
    mut v_stx_8260_: *mut leanh::LeanObject,
    mut v_a_8261_: *mut leanh::LeanObject,
    mut v_a_8262_: *mut leanh::LeanObject,
    mut v_a_8263_: *mut leanh::LeanObject,
    mut v_a_8264_: *mut leanh::LeanObject,
    mut v_a_8265_: *mut leanh::LeanObject,
    mut v_a_8266_: *mut leanh::LeanObject,
    mut v_a_8267_: *mut leanh::LeanObject,
    mut v_a_8268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_8271_: u8 = 0;
    let mut v_ctxApprox_8272_: u8 = 0;
    let mut v_quasiPatternApprox_8273_: u8 = 0;
    let mut v_constApprox_8274_: u8 = 0;
    let mut v_isDefEqStuckEx_8275_: u8 = 0;
    let mut v_unificationHints_8276_: u8 = 0;
    let mut v_proofIrrelevance_8277_: u8 = 0;
    let mut v_assignSyntheticOpaque_8278_: u8 = 0;
    let mut v_offsetCnstrs_8279_: u8 = 0;
    let mut v_etaStruct_8280_: u8 = 0;
    let mut v_univApprox_8281_: u8 = 0;
    let mut v_iota_8282_: u8 = 0;
    let mut v_beta_8283_: u8 = 0;
    let mut v_proj_8284_: u8 = 0;
    let mut v_zeta_8285_: u8 = 0;
    let mut v_zetaDelta_8286_: u8 = 0;
    let mut v_zetaUnused_8287_: u8 = 0;
    let mut v_zetaHave_8288_: u8 = 0;
    let mut v___x_8290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8291_: u8 = 0;
    let mut v_trackZetaDelta_8292_: u8 = 0;
    let mut v_zetaDeltaSet_8293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_8294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_8295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_8296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_8297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_8298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_8299_: u8 = 0;
    let mut v_inTypeClassResolution_8300_: u8 = 0;
    let mut v_cacheInferType_8301_: u8 = 0;
    let mut v___x_8302_: u8 = 0;
    let mut v_config_8304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8305_: u64 = 0;
    let mut v___x_8306_: u64 = 0;
    let mut v___x_8307_: u64 = 0;
    let mut v___x_8308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8310_: u64 = 0;
    let mut v___x_8311_: u64 = 0;
    let mut v_key_8312_: u64 = 0;
    let mut v___x_8313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8319_: u8 = 0;
    let mut v___x_8321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8323_: u8 = 0;
    let mut v_reuseFailAlloc_8324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8325_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8270_ = l_Lean_Meta_Context_config(v_a_8265_);
                v_foApprox_8271_ = leanh::lean_ctor_get_uint8(v___x_8270_, 0 as u32);
                v_ctxApprox_8272_ = leanh::lean_ctor_get_uint8(v___x_8270_, 1 as u32);
                v_quasiPatternApprox_8273_ =
                    leanh::lean_ctor_get_uint8(v___x_8270_, 2 as u32);
                v_constApprox_8274_ = leanh::lean_ctor_get_uint8(v___x_8270_, 3 as u32);
                v_isDefEqStuckEx_8275_ = leanh::lean_ctor_get_uint8(v___x_8270_, 4 as u32);
                v_unificationHints_8276_ = leanh::lean_ctor_get_uint8(v___x_8270_, 5 as u32);
                v_proofIrrelevance_8277_ = leanh::lean_ctor_get_uint8(v___x_8270_, 6 as u32);
                v_assignSyntheticOpaque_8278_ =
                    leanh::lean_ctor_get_uint8(v___x_8270_, 7 as u32);
                v_offsetCnstrs_8279_ = leanh::lean_ctor_get_uint8(v___x_8270_, 8 as u32);
                v_etaStruct_8280_ = leanh::lean_ctor_get_uint8(v___x_8270_, 10 as u32);
                v_univApprox_8281_ = leanh::lean_ctor_get_uint8(v___x_8270_, 11 as u32);
                v_iota_8282_ = leanh::lean_ctor_get_uint8(v___x_8270_, 12 as u32);
                v_beta_8283_ = leanh::lean_ctor_get_uint8(v___x_8270_, 13 as u32);
                v_proj_8284_ = leanh::lean_ctor_get_uint8(v___x_8270_, 14 as u32);
                v_zeta_8285_ = leanh::lean_ctor_get_uint8(v___x_8270_, 15 as u32);
                v_zetaDelta_8286_ = leanh::lean_ctor_get_uint8(v___x_8270_, 16 as u32);
                v_zetaUnused_8287_ = leanh::lean_ctor_get_uint8(v___x_8270_, 17 as u32);
                v_zetaHave_8288_ = leanh::lean_ctor_get_uint8(v___x_8270_, 18 as u32);
                v_isSharedCheck_8325_ = (!leanh::lean_is_exclusive(v___x_8270_)) as u8;
                if v_isSharedCheck_8325_ == 0 {
                    v___x_8290_ = v___x_8270_;
                    v_isShared_8291_ = v_isSharedCheck_8325_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_8270_);
                    v___x_8290_ = leanh::lean_box(0);
                    v_isShared_8291_ = v_isSharedCheck_8325_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_8292_ = leanh::lean_ctor_get_uint8(
                    v_a_8265_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_8293_ = leanh::lean_ctor_get(v_a_8265_, 1);
                v_lctx_8294_ = leanh::lean_ctor_get(v_a_8265_, 2);
                v_localInstances_8295_ = leanh::lean_ctor_get(v_a_8265_, 3);
                v_defEqCtx_x3f_8296_ = leanh::lean_ctor_get(v_a_8265_, 4);
                v_synthPendingDepth_8297_ = leanh::lean_ctor_get(v_a_8265_, 5);
                v_canUnfold_x3f_8298_ = leanh::lean_ctor_get(v_a_8265_, 6);
                v_univApprox_8299_ = leanh::lean_ctor_get_uint8(
                    v_a_8265_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_8300_ = leanh::lean_ctor_get_uint8(
                    v_a_8265_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_8301_ = leanh::lean_ctor_get_uint8(
                    v_a_8265_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_8302_ = 0;
                if v_isShared_8291_ == 0 {
                    v_config_8304_ = v___x_8290_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8324_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        0 as u32,
                        v_foApprox_8271_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        1 as u32,
                        v_ctxApprox_8272_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        2 as u32,
                        v_quasiPatternApprox_8273_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        3 as u32,
                        v_constApprox_8274_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        4 as u32,
                        v_isDefEqStuckEx_8275_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        5 as u32,
                        v_unificationHints_8276_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        6 as u32,
                        v_proofIrrelevance_8277_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        7 as u32,
                        v_assignSyntheticOpaque_8278_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        8 as u32,
                        v_offsetCnstrs_8279_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        10 as u32,
                        v_etaStruct_8280_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        11 as u32,
                        v_univApprox_8281_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        12 as u32,
                        v_iota_8282_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        13 as u32,
                        v_beta_8283_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        14 as u32,
                        v_proj_8284_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        15 as u32,
                        v_zeta_8285_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        16 as u32,
                        v_zetaDelta_8286_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        17 as u32,
                        v_zetaUnused_8287_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8324_,
                        18 as u32,
                        v_zetaHave_8288_,
                    );
                    v_config_8304_ = v_reuseFailAlloc_8324_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_8304_, 9 as u32, v___x_8302_);
                v___x_8305_ = l_Lean_Meta_Context_configKey(v_a_8265_);
                v___x_8306_ = 3u64;
                v___x_8307_ = lean_uint64_shift_right(v___x_8305_, v___x_8306_);
                v___x_8308_ = leanh::lean_unsigned_to_nat(1);
                v___x_8309_ = l_Lean_Syntax_getArg(v_stx_8260_, v___x_8308_);
                v___x_8310_ = lean_uint64_shift_left(v___x_8307_, v___x_8306_);
                v___x_8311_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0_once
                    ),
                    _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0,
                );
                v_key_8312_ = lean_uint64_lor(v___x_8310_, v___x_8311_);
                v___x_8313_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_8313_, 0, v_config_8304_);
                leanh::lean_ctor_set_uint64(
                    v___x_8313_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_8312_,
                );
                leanh::lean_inc(v_canUnfold_x3f_8298_);
                leanh::lean_inc(v_synthPendingDepth_8297_);
                leanh::lean_inc(v_defEqCtx_x3f_8296_);
                leanh::lean_inc_ref(v_localInstances_8295_);
                leanh::lean_inc_ref(v_lctx_8294_);
                leanh::lean_inc(v_zetaDeltaSet_8293_);
                v___x_8314_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_8314_, 0, v___x_8313_);
                leanh::lean_ctor_set(v___x_8314_, 1, v_zetaDeltaSet_8293_);
                leanh::lean_ctor_set(v___x_8314_, 2, v_lctx_8294_);
                leanh::lean_ctor_set(v___x_8314_, 3, v_localInstances_8295_);
                leanh::lean_ctor_set(v___x_8314_, 4, v_defEqCtx_x3f_8296_);
                leanh::lean_ctor_set(v___x_8314_, 5, v_synthPendingDepth_8297_);
                leanh::lean_ctor_set(v___x_8314_, 6, v_canUnfold_x3f_8298_);
                leanh::lean_ctor_set_uint8(
                    v___x_8314_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_8292_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8314_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_8299_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8314_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_8300_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8314_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_8301_,
                );
                v___x_8315_ = l_Lean_Elab_Tactic_evalTactic(
                    v___x_8309_,
                    v_a_8261_,
                    v_a_8262_,
                    v_a_8263_,
                    v_a_8264_,
                    v___x_8314_,
                    v_a_8266_,
                    v_a_8267_,
                    v_a_8268_,
                );
                leanh::lean_dec_ref_known(v___x_8314_, 7);
                if leanh::lean_obj_tag(v___x_8315_) == 0 {
                    v_a_8316_ = leanh::lean_ctor_get(v___x_8315_, 0);
                    v_isSharedCheck_8323_ = (!leanh::lean_is_exclusive(v___x_8315_)) as u8;
                    if v_isSharedCheck_8323_ == 0 {
                        v___x_8318_ = v___x_8315_;
                        v_isShared_8319_ = v_isSharedCheck_8323_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8316_);
                        leanh::lean_dec(v___x_8315_);
                        v___x_8318_ = leanh::lean_box(0);
                        v_isShared_8319_ = v_isSharedCheck_8323_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_8315_;
                }
            }
            3 => {
                if v_isShared_8319_ == 0 {
                    v___x_8321_ = v___x_8318_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8322_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8322_, 0, v_a_8316_);
                    v___x_8321_ = v_reuseFailAlloc_8322_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed(
    mut v_stx_8326_: *mut leanh::LeanObject,
    mut v_a_8327_: *mut leanh::LeanObject,
    mut v_a_8328_: *mut leanh::LeanObject,
    mut v_a_8329_: *mut leanh::LeanObject,
    mut v_a_8330_: *mut leanh::LeanObject,
    mut v_a_8331_: *mut leanh::LeanObject,
    mut v_a_8332_: *mut leanh::LeanObject,
    mut v_a_8333_: *mut leanh::LeanObject,
    mut v_a_8334_: *mut leanh::LeanObject,
    mut v_a_8335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8336_ = l_Lean_Elab_Tactic_evalWithUnfoldingAll(
        v_stx_8326_,
        v_a_8327_,
        v_a_8328_,
        v_a_8329_,
        v_a_8330_,
        v_a_8331_,
        v_a_8332_,
        v_a_8333_,
        v_a_8334_,
    );
    leanh::lean_dec(v_a_8334_);
    leanh::lean_dec_ref(v_a_8333_);
    leanh::lean_dec(v_a_8332_);
    leanh::lean_dec_ref(v_a_8331_);
    leanh::lean_dec(v_a_8330_);
    leanh::lean_dec_ref(v_a_8329_);
    leanh::lean_dec(v_a_8328_);
    leanh::lean_dec_ref(v_a_8327_);
    leanh::lean_dec(v_stx_8326_);
    return v_res_8336_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1()
-> *mut leanh::LeanObject {
    let mut v___x_8350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8350_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_8351_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1;
    v___x_8352_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3;
    v___x_8353_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_8354_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_8350_,
        v___x_8351_,
        v___x_8352_,
        v___x_8353_,
    );
    return v___x_8354_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___boxed(
    mut v_a_8355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8356_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1();
    return v_res_8356_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_8383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8383_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3;
    v___x_8384_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6;
    v___x_8385_ = l_Lean_addBuiltinDeclarationRanges(v___x_8383_, v___x_8384_);
    return v___x_8385_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___boxed(
    mut v_a_8386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8387_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3();
    return v_res_8387_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0() -> u64 {
    let mut v___x_8388_: u8 = 0;
    let mut v___x_8389_: u64 = 0;
    v___x_8388_ = 4;
    v___x_8389_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_8388_);
    return v___x_8389_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalWithUnfoldingNone(
    mut v_stx_8390_: *mut leanh::LeanObject,
    mut v_a_8391_: *mut leanh::LeanObject,
    mut v_a_8392_: *mut leanh::LeanObject,
    mut v_a_8393_: *mut leanh::LeanObject,
    mut v_a_8394_: *mut leanh::LeanObject,
    mut v_a_8395_: *mut leanh::LeanObject,
    mut v_a_8396_: *mut leanh::LeanObject,
    mut v_a_8397_: *mut leanh::LeanObject,
    mut v_a_8398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_8401_: u8 = 0;
    let mut v_ctxApprox_8402_: u8 = 0;
    let mut v_quasiPatternApprox_8403_: u8 = 0;
    let mut v_constApprox_8404_: u8 = 0;
    let mut v_isDefEqStuckEx_8405_: u8 = 0;
    let mut v_unificationHints_8406_: u8 = 0;
    let mut v_proofIrrelevance_8407_: u8 = 0;
    let mut v_assignSyntheticOpaque_8408_: u8 = 0;
    let mut v_offsetCnstrs_8409_: u8 = 0;
    let mut v_etaStruct_8410_: u8 = 0;
    let mut v_univApprox_8411_: u8 = 0;
    let mut v_iota_8412_: u8 = 0;
    let mut v_beta_8413_: u8 = 0;
    let mut v_proj_8414_: u8 = 0;
    let mut v_zeta_8415_: u8 = 0;
    let mut v_zetaDelta_8416_: u8 = 0;
    let mut v_zetaUnused_8417_: u8 = 0;
    let mut v_zetaHave_8418_: u8 = 0;
    let mut v___x_8420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8421_: u8 = 0;
    let mut v_trackZetaDelta_8422_: u8 = 0;
    let mut v_zetaDeltaSet_8423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_8424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_8425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_8426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_8427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_8428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_8429_: u8 = 0;
    let mut v_inTypeClassResolution_8430_: u8 = 0;
    let mut v_cacheInferType_8431_: u8 = 0;
    let mut v___x_8432_: u8 = 0;
    let mut v_config_8434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8435_: u64 = 0;
    let mut v___x_8436_: u64 = 0;
    let mut v___x_8437_: u64 = 0;
    let mut v___x_8438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8440_: u64 = 0;
    let mut v___x_8441_: u64 = 0;
    let mut v_key_8442_: u64 = 0;
    let mut v___x_8443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8449_: u8 = 0;
    let mut v___x_8451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8453_: u8 = 0;
    let mut v_reuseFailAlloc_8454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8400_ = l_Lean_Meta_Context_config(v_a_8395_);
                v_foApprox_8401_ = leanh::lean_ctor_get_uint8(v___x_8400_, 0 as u32);
                v_ctxApprox_8402_ = leanh::lean_ctor_get_uint8(v___x_8400_, 1 as u32);
                v_quasiPatternApprox_8403_ =
                    leanh::lean_ctor_get_uint8(v___x_8400_, 2 as u32);
                v_constApprox_8404_ = leanh::lean_ctor_get_uint8(v___x_8400_, 3 as u32);
                v_isDefEqStuckEx_8405_ = leanh::lean_ctor_get_uint8(v___x_8400_, 4 as u32);
                v_unificationHints_8406_ = leanh::lean_ctor_get_uint8(v___x_8400_, 5 as u32);
                v_proofIrrelevance_8407_ = leanh::lean_ctor_get_uint8(v___x_8400_, 6 as u32);
                v_assignSyntheticOpaque_8408_ =
                    leanh::lean_ctor_get_uint8(v___x_8400_, 7 as u32);
                v_offsetCnstrs_8409_ = leanh::lean_ctor_get_uint8(v___x_8400_, 8 as u32);
                v_etaStruct_8410_ = leanh::lean_ctor_get_uint8(v___x_8400_, 10 as u32);
                v_univApprox_8411_ = leanh::lean_ctor_get_uint8(v___x_8400_, 11 as u32);
                v_iota_8412_ = leanh::lean_ctor_get_uint8(v___x_8400_, 12 as u32);
                v_beta_8413_ = leanh::lean_ctor_get_uint8(v___x_8400_, 13 as u32);
                v_proj_8414_ = leanh::lean_ctor_get_uint8(v___x_8400_, 14 as u32);
                v_zeta_8415_ = leanh::lean_ctor_get_uint8(v___x_8400_, 15 as u32);
                v_zetaDelta_8416_ = leanh::lean_ctor_get_uint8(v___x_8400_, 16 as u32);
                v_zetaUnused_8417_ = leanh::lean_ctor_get_uint8(v___x_8400_, 17 as u32);
                v_zetaHave_8418_ = leanh::lean_ctor_get_uint8(v___x_8400_, 18 as u32);
                v_isSharedCheck_8455_ = (!leanh::lean_is_exclusive(v___x_8400_)) as u8;
                if v_isSharedCheck_8455_ == 0 {
                    v___x_8420_ = v___x_8400_;
                    v_isShared_8421_ = v_isSharedCheck_8455_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_8400_);
                    v___x_8420_ = leanh::lean_box(0);
                    v_isShared_8421_ = v_isSharedCheck_8455_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_8422_ = leanh::lean_ctor_get_uint8(
                    v_a_8395_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_8423_ = leanh::lean_ctor_get(v_a_8395_, 1);
                v_lctx_8424_ = leanh::lean_ctor_get(v_a_8395_, 2);
                v_localInstances_8425_ = leanh::lean_ctor_get(v_a_8395_, 3);
                v_defEqCtx_x3f_8426_ = leanh::lean_ctor_get(v_a_8395_, 4);
                v_synthPendingDepth_8427_ = leanh::lean_ctor_get(v_a_8395_, 5);
                v_canUnfold_x3f_8428_ = leanh::lean_ctor_get(v_a_8395_, 6);
                v_univApprox_8429_ = leanh::lean_ctor_get_uint8(
                    v_a_8395_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_8430_ = leanh::lean_ctor_get_uint8(
                    v_a_8395_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_8431_ = leanh::lean_ctor_get_uint8(
                    v_a_8395_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_8432_ = 4;
                if v_isShared_8421_ == 0 {
                    v_config_8434_ = v___x_8420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8454_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        0 as u32,
                        v_foApprox_8401_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        1 as u32,
                        v_ctxApprox_8402_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        2 as u32,
                        v_quasiPatternApprox_8403_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        3 as u32,
                        v_constApprox_8404_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        4 as u32,
                        v_isDefEqStuckEx_8405_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        5 as u32,
                        v_unificationHints_8406_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        6 as u32,
                        v_proofIrrelevance_8407_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        7 as u32,
                        v_assignSyntheticOpaque_8408_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        8 as u32,
                        v_offsetCnstrs_8409_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        10 as u32,
                        v_etaStruct_8410_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        11 as u32,
                        v_univApprox_8411_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        12 as u32,
                        v_iota_8412_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        13 as u32,
                        v_beta_8413_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        14 as u32,
                        v_proj_8414_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        15 as u32,
                        v_zeta_8415_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        16 as u32,
                        v_zetaDelta_8416_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        17 as u32,
                        v_zetaUnused_8417_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8454_,
                        18 as u32,
                        v_zetaHave_8418_,
                    );
                    v_config_8434_ = v_reuseFailAlloc_8454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_8434_, 9 as u32, v___x_8432_);
                v___x_8435_ = l_Lean_Meta_Context_configKey(v_a_8395_);
                v___x_8436_ = 3u64;
                v___x_8437_ = lean_uint64_shift_right(v___x_8435_, v___x_8436_);
                v___x_8438_ = leanh::lean_unsigned_to_nat(1);
                v___x_8439_ = l_Lean_Syntax_getArg(v_stx_8390_, v___x_8438_);
                v___x_8440_ = lean_uint64_shift_left(v___x_8437_, v___x_8436_);
                v___x_8441_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0_once
                    ),
                    _init_l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0,
                );
                v_key_8442_ = lean_uint64_lor(v___x_8440_, v___x_8441_);
                v___x_8443_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_8443_, 0, v_config_8434_);
                leanh::lean_ctor_set_uint64(
                    v___x_8443_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_8442_,
                );
                leanh::lean_inc(v_canUnfold_x3f_8428_);
                leanh::lean_inc(v_synthPendingDepth_8427_);
                leanh::lean_inc(v_defEqCtx_x3f_8426_);
                leanh::lean_inc_ref(v_localInstances_8425_);
                leanh::lean_inc_ref(v_lctx_8424_);
                leanh::lean_inc(v_zetaDeltaSet_8423_);
                v___x_8444_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_8444_, 0, v___x_8443_);
                leanh::lean_ctor_set(v___x_8444_, 1, v_zetaDeltaSet_8423_);
                leanh::lean_ctor_set(v___x_8444_, 2, v_lctx_8424_);
                leanh::lean_ctor_set(v___x_8444_, 3, v_localInstances_8425_);
                leanh::lean_ctor_set(v___x_8444_, 4, v_defEqCtx_x3f_8426_);
                leanh::lean_ctor_set(v___x_8444_, 5, v_synthPendingDepth_8427_);
                leanh::lean_ctor_set(v___x_8444_, 6, v_canUnfold_x3f_8428_);
                leanh::lean_ctor_set_uint8(
                    v___x_8444_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_8422_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8444_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_8429_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8444_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_8430_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8444_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_8431_,
                );
                v___x_8445_ = l_Lean_Elab_Tactic_evalTactic(
                    v___x_8439_,
                    v_a_8391_,
                    v_a_8392_,
                    v_a_8393_,
                    v_a_8394_,
                    v___x_8444_,
                    v_a_8396_,
                    v_a_8397_,
                    v_a_8398_,
                );
                leanh::lean_dec_ref_known(v___x_8444_, 7);
                if leanh::lean_obj_tag(v___x_8445_) == 0 {
                    v_a_8446_ = leanh::lean_ctor_get(v___x_8445_, 0);
                    v_isSharedCheck_8453_ = (!leanh::lean_is_exclusive(v___x_8445_)) as u8;
                    if v_isSharedCheck_8453_ == 0 {
                        v___x_8448_ = v___x_8445_;
                        v_isShared_8449_ = v_isSharedCheck_8453_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8446_);
                        leanh::lean_dec(v___x_8445_);
                        v___x_8448_ = leanh::lean_box(0);
                        v_isShared_8449_ = v_isSharedCheck_8453_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_8445_;
                }
            }
            3 => {
                if v_isShared_8449_ == 0 {
                    v___x_8451_ = v___x_8448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8452_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8452_, 0, v_a_8446_);
                    v___x_8451_ = v_reuseFailAlloc_8452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed(
    mut v_stx_8456_: *mut leanh::LeanObject,
    mut v_a_8457_: *mut leanh::LeanObject,
    mut v_a_8458_: *mut leanh::LeanObject,
    mut v_a_8459_: *mut leanh::LeanObject,
    mut v_a_8460_: *mut leanh::LeanObject,
    mut v_a_8461_: *mut leanh::LeanObject,
    mut v_a_8462_: *mut leanh::LeanObject,
    mut v_a_8463_: *mut leanh::LeanObject,
    mut v_a_8464_: *mut leanh::LeanObject,
    mut v_a_8465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8466_ = l_Lean_Elab_Tactic_evalWithUnfoldingNone(
        v_stx_8456_,
        v_a_8457_,
        v_a_8458_,
        v_a_8459_,
        v_a_8460_,
        v_a_8461_,
        v_a_8462_,
        v_a_8463_,
        v_a_8464_,
    );
    leanh::lean_dec(v_a_8464_);
    leanh::lean_dec_ref(v_a_8463_);
    leanh::lean_dec(v_a_8462_);
    leanh::lean_dec_ref(v_a_8461_);
    leanh::lean_dec(v_a_8460_);
    leanh::lean_dec_ref(v_a_8459_);
    leanh::lean_dec(v_a_8458_);
    leanh::lean_dec_ref(v_a_8457_);
    leanh::lean_dec(v_stx_8456_);
    return v_res_8466_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1()
-> *mut leanh::LeanObject {
    let mut v___x_8480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8480_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_8481_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1;
    v___x_8482_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3;
    v___x_8483_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_8484_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_8480_,
        v___x_8481_,
        v___x_8482_,
        v___x_8483_,
    );
    return v___x_8484_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___boxed(
    mut v_a_8485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8486_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1();
    return v_res_8486_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabAsFVar___lam__0(
    mut v_stx_8490_: *mut leanh::LeanObject,
    mut v___x_8491_: *mut leanh::LeanObject,
    mut v___x_8492_: u8,
    mut v_userName_x3f_8493_: *mut leanh::LeanObject,
    mut v___y_8494_: *mut leanh::LeanObject,
    mut v___y_8495_: *mut leanh::LeanObject,
    mut v___y_8496_: *mut leanh::LeanObject,
    mut v___y_8497_: *mut leanh::LeanObject,
    mut v___y_8498_: *mut leanh::LeanObject,
    mut v___y_8499_: *mut leanh::LeanObject,
    mut v___y_8500_: *mut leanh::LeanObject,
    mut v___y_8501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8507_: u8 = 0;
    let mut v_fvarId_8508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_8515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_preserveBinderNames_8516_: u8 = 0;
    let mut v___y_8517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8532_: u8 = 0;
    let mut v___x_8533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8539_: u8 = 0;
    let mut v___x_8541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8543_: u8 = 0;
    let mut v_unused_8544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8548_: u8 = 0;
    let mut v___x_8550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8552_: u8 = 0;
    let mut v_reuseFailAlloc_8553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8554_: u8 = 0;
    let mut v_a_8555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8558_: u8 = 0;
    let mut v___x_8560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8562_: u8 = 0;
    let mut v_a_8563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8566_: u8 = 0;
    let mut v___x_8568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8570_: u8 = 0;
    let mut v_a_8571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8574_: u8 = 0;
    let mut v___x_8576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8578_: u8 = 0;
    let mut v___x_8579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8581_: u8 = 0;
    let mut v_a_8582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8585_: u8 = 0;
    let mut v___x_8587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8589_: u8 = 0;
    let mut v_isSharedCheck_8590_: u8 = 0;
    let mut v_a_8591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8594_: u8 = 0;
    let mut v___x_8596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8598_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8503_ = l_Lean_Elab_Tactic_elabTerm(
                    v_stx_8490_,
                    v___x_8491_,
                    v___x_8492_,
                    v___y_8494_,
                    v___y_8495_,
                    v___y_8496_,
                    v___y_8497_,
                    v___y_8498_,
                    v___y_8499_,
                    v___y_8500_,
                    v___y_8501_,
                );
                if leanh::lean_obj_tag(v___x_8503_) == 0 {
                    v_a_8504_ = leanh::lean_ctor_get(v___x_8503_, 0);
                    v_isSharedCheck_8590_ = (!leanh::lean_is_exclusive(v___x_8503_)) as u8;
                    if v_isSharedCheck_8590_ == 0 {
                        v___x_8506_ = v___x_8503_;
                        v_isShared_8507_ = v_isSharedCheck_8590_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8504_);
                        leanh::lean_dec(v___x_8503_);
                        v___x_8506_ = leanh::lean_box(0);
                        v_isShared_8507_ = v_isSharedCheck_8590_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_8501_);
                    leanh::lean_dec_ref(v___y_8500_);
                    leanh::lean_dec(v___y_8499_);
                    leanh::lean_dec_ref(v___y_8498_);
                    leanh::lean_dec(v_userName_x3f_8493_);
                    v_a_8591_ = leanh::lean_ctor_get(v___x_8503_, 0);
                    v_isSharedCheck_8598_ = (!leanh::lean_is_exclusive(v___x_8503_)) as u8;
                    if v_isSharedCheck_8598_ == 0 {
                        v___x_8593_ = v___x_8503_;
                        v_isShared_8594_ = v_isSharedCheck_8598_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8591_);
                        leanh::lean_dec(v___x_8503_);
                        v___x_8593_ = leanh::lean_box(0);
                        v_isShared_8594_ = v_isSharedCheck_8598_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_8504_) == 1 {
                    leanh::lean_dec(v___y_8501_);
                    leanh::lean_dec_ref(v___y_8500_);
                    leanh::lean_dec(v___y_8499_);
                    leanh::lean_dec_ref(v___y_8498_);
                    leanh::lean_dec(v_userName_x3f_8493_);
                    v_fvarId_8508_ = leanh::lean_ctor_get(v_a_8504_, 0);
                    leanh::lean_inc(v_fvarId_8508_);
                    leanh::lean_dec_ref_known(v_a_8504_, 1);
                    if v_isShared_8507_ == 0 {
                        leanh::lean_ctor_set(v___x_8506_, 0, v_fvarId_8508_);
                        v___x_8510_ = v___x_8506_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8511_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8511_, 0, v_fvarId_8508_);
                        v___x_8510_ = v_reuseFailAlloc_8511_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_8506_);
                    leanh::lean_inc(v___y_8501_);
                    leanh::lean_inc_ref(v___y_8500_);
                    leanh::lean_inc(v___y_8499_);
                    leanh::lean_inc_ref(v___y_8498_);
                    leanh::lean_inc(v_a_8504_);
                    v___x_8512_ = lean_infer_type(
                        v_a_8504_,
                        v___y_8498_,
                        v___y_8499_,
                        v___y_8500_,
                        v___y_8501_,
                    );
                    if leanh::lean_obj_tag(v___x_8512_) == 0 {
                        v_a_8513_ = leanh::lean_ctor_get(v___x_8512_, 0);
                        leanh::lean_inc(v_a_8513_);
                        leanh::lean_dec_ref_known(v___x_8512_, 1);
                        if leanh::lean_obj_tag(v_userName_x3f_8493_) == 0 {
                            v___x_8579_ = l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1;
                            v_userName_8515_ = v___x_8579_;
                            v_preserveBinderNames_8516_ = v___x_8492_;
                            v___y_8517_ = v___y_8495_;
                            v___y_8518_ = v___y_8498_;
                            v___y_8519_ = v___y_8499_;
                            v___y_8520_ = v___y_8500_;
                            v___y_8521_ = v___y_8501_;
                            state = 3;
                            continue;
                        } else {
                            v_val_8580_ = leanh::lean_ctor_get(v_userName_x3f_8493_, 0);
                            leanh::lean_inc(v_val_8580_);
                            leanh::lean_dec_ref_known(v_userName_x3f_8493_, 1);
                            v___x_8581_ = 1;
                            v_userName_8515_ = v_val_8580_;
                            v_preserveBinderNames_8516_ = v___x_8581_;
                            v___y_8517_ = v___y_8495_;
                            v___y_8518_ = v___y_8498_;
                            v___y_8519_ = v___y_8499_;
                            v___y_8520_ = v___y_8500_;
                            v___y_8521_ = v___y_8501_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_8504_);
                        leanh::lean_dec(v___y_8501_);
                        leanh::lean_dec_ref(v___y_8500_);
                        leanh::lean_dec(v___y_8499_);
                        leanh::lean_dec_ref(v___y_8498_);
                        leanh::lean_dec(v_userName_x3f_8493_);
                        v_a_8582_ = leanh::lean_ctor_get(v___x_8512_, 0);
                        v_isSharedCheck_8589_ =
                            (!leanh::lean_is_exclusive(v___x_8512_)) as u8;
                        if v_isSharedCheck_8589_ == 0 {
                            v___x_8584_ = v___x_8512_;
                            v_isShared_8585_ = v_isSharedCheck_8589_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8582_);
                            leanh::lean_dec(v___x_8512_);
                            v___x_8584_ = leanh::lean_box(0);
                            v_isShared_8585_ = v_isSharedCheck_8589_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_8510_;
            }
            3 => {
                v___x_8522_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_8517_,
                    v___y_8518_,
                    v___y_8519_,
                    v___y_8520_,
                    v___y_8521_,
                );
                if leanh::lean_obj_tag(v___x_8522_) == 0 {
                    v_a_8523_ = leanh::lean_ctor_get(v___x_8522_, 0);
                    leanh::lean_inc(v_a_8523_);
                    leanh::lean_dec_ref_known(v___x_8522_, 1);
                    v___x_8524_ = l_Lean_MVarId_assert(
                        v_a_8523_,
                        v_userName_8515_,
                        v_a_8513_,
                        v_a_8504_,
                        v___y_8518_,
                        v___y_8519_,
                        v___y_8520_,
                        v___y_8521_,
                    );
                    if leanh::lean_obj_tag(v___x_8524_) == 0 {
                        v_a_8525_ = leanh::lean_ctor_get(v___x_8524_, 0);
                        leanh::lean_inc(v_a_8525_);
                        leanh::lean_dec_ref_known(v___x_8524_, 1);
                        v___x_8526_ = l_Lean_Meta_intro1Core(
                            v_a_8525_,
                            v_preserveBinderNames_8516_,
                            v___y_8518_,
                            v___y_8519_,
                            v___y_8520_,
                            v___y_8521_,
                        );
                        if leanh::lean_obj_tag(v___x_8526_) == 0 {
                            v_a_8527_ = leanh::lean_ctor_get(v___x_8526_, 0);
                            leanh::lean_inc(v_a_8527_);
                            leanh::lean_dec_ref_known(v___x_8526_, 1);
                            v_fst_8528_ = leanh::lean_ctor_get(v_a_8527_, 0);
                            v_snd_8529_ = leanh::lean_ctor_get(v_a_8527_, 1);
                            v_isSharedCheck_8554_ =
                                (!leanh::lean_is_exclusive(v_a_8527_)) as u8;
                            if v_isSharedCheck_8554_ == 0 {
                                v___x_8531_ = v_a_8527_;
                                v_isShared_8532_ = v_isSharedCheck_8554_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_8529_);
                                leanh::lean_inc(v_fst_8528_);
                                leanh::lean_dec(v_a_8527_);
                                v___x_8531_ = leanh::lean_box(0);
                                v_isShared_8532_ = v_isSharedCheck_8554_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___y_8521_);
                            leanh::lean_dec_ref(v___y_8520_);
                            leanh::lean_dec(v___y_8519_);
                            leanh::lean_dec_ref(v___y_8518_);
                            v_a_8555_ = leanh::lean_ctor_get(v___x_8526_, 0);
                            v_isSharedCheck_8562_ =
                                (!leanh::lean_is_exclusive(v___x_8526_)) as u8;
                            if v_isSharedCheck_8562_ == 0 {
                                v___x_8557_ = v___x_8526_;
                                v_isShared_8558_ = v_isSharedCheck_8562_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8555_);
                                leanh::lean_dec(v___x_8526_);
                                v___x_8557_ = leanh::lean_box(0);
                                v_isShared_8558_ = v_isSharedCheck_8562_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___y_8521_);
                        leanh::lean_dec_ref(v___y_8520_);
                        leanh::lean_dec(v___y_8519_);
                        leanh::lean_dec_ref(v___y_8518_);
                        v_a_8563_ = leanh::lean_ctor_get(v___x_8524_, 0);
                        v_isSharedCheck_8570_ =
                            (!leanh::lean_is_exclusive(v___x_8524_)) as u8;
                        if v_isSharedCheck_8570_ == 0 {
                            v___x_8565_ = v___x_8524_;
                            v_isShared_8566_ = v_isSharedCheck_8570_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8563_);
                            leanh::lean_dec(v___x_8524_);
                            v___x_8565_ = leanh::lean_box(0);
                            v_isShared_8566_ = v_isSharedCheck_8570_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_8521_);
                    leanh::lean_dec_ref(v___y_8520_);
                    leanh::lean_dec(v___y_8519_);
                    leanh::lean_dec_ref(v___y_8518_);
                    leanh::lean_dec(v_userName_8515_);
                    leanh::lean_dec(v_a_8513_);
                    leanh::lean_dec(v_a_8504_);
                    v_a_8571_ = leanh::lean_ctor_get(v___x_8522_, 0);
                    v_isSharedCheck_8578_ = (!leanh::lean_is_exclusive(v___x_8522_)) as u8;
                    if v_isSharedCheck_8578_ == 0 {
                        v___x_8573_ = v___x_8522_;
                        v_isShared_8574_ = v_isSharedCheck_8578_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8571_);
                        leanh::lean_dec(v___x_8522_);
                        v___x_8573_ = leanh::lean_box(0);
                        v_isShared_8574_ = v_isSharedCheck_8578_;
                        state = 14;
                        continue;
                    }
                }
            }
            4 => {
                v___x_8533_ = leanh::lean_box(0);
                if v_isShared_8532_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_8531_, 1);
                    leanh::lean_ctor_set(v___x_8531_, 1, v___x_8533_);
                    leanh::lean_ctor_set(v___x_8531_, 0, v_snd_8529_);
                    v___x_8535_ = v___x_8531_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8553_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8553_, 0, v_snd_8529_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8553_, 1, v___x_8533_);
                    v___x_8535_ = v_reuseFailAlloc_8553_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_8536_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_8535_,
                    v___y_8517_,
                    v___y_8518_,
                    v___y_8519_,
                    v___y_8520_,
                    v___y_8521_,
                );
                leanh::lean_dec(v___y_8521_);
                leanh::lean_dec_ref(v___y_8520_);
                leanh::lean_dec(v___y_8519_);
                leanh::lean_dec_ref(v___y_8518_);
                if leanh::lean_obj_tag(v___x_8536_) == 0 {
                    v_isSharedCheck_8543_ = (!leanh::lean_is_exclusive(v___x_8536_)) as u8;
                    if v_isSharedCheck_8543_ == 0 {
                        v_unused_8544_ = leanh::lean_ctor_get(v___x_8536_, 0);
                        leanh::lean_dec(v_unused_8544_);
                        v___x_8538_ = v___x_8536_;
                        v_isShared_8539_ = v_isSharedCheck_8543_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_8536_);
                        v___x_8538_ = leanh::lean_box(0);
                        v_isShared_8539_ = v_isSharedCheck_8543_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_8528_);
                    v_a_8545_ = leanh::lean_ctor_get(v___x_8536_, 0);
                    v_isSharedCheck_8552_ = (!leanh::lean_is_exclusive(v___x_8536_)) as u8;
                    if v_isSharedCheck_8552_ == 0 {
                        v___x_8547_ = v___x_8536_;
                        v_isShared_8548_ = v_isSharedCheck_8552_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8545_);
                        leanh::lean_dec(v___x_8536_);
                        v___x_8547_ = leanh::lean_box(0);
                        v_isShared_8548_ = v_isSharedCheck_8552_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_8539_ == 0 {
                    leanh::lean_ctor_set(v___x_8538_, 0, v_fst_8528_);
                    v___x_8541_ = v___x_8538_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8542_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8542_, 0, v_fst_8528_);
                    v___x_8541_ = v_reuseFailAlloc_8542_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8541_;
            }
            8 => {
                if v_isShared_8548_ == 0 {
                    v___x_8550_ = v___x_8547_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8551_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8551_, 0, v_a_8545_);
                    v___x_8550_ = v_reuseFailAlloc_8551_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8550_;
            }
            10 => {
                if v_isShared_8558_ == 0 {
                    v___x_8560_ = v___x_8557_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8561_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8561_, 0, v_a_8555_);
                    v___x_8560_ = v_reuseFailAlloc_8561_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8560_;
            }
            12 => {
                if v_isShared_8566_ == 0 {
                    v___x_8568_ = v___x_8565_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8569_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8569_, 0, v_a_8563_);
                    v___x_8568_ = v_reuseFailAlloc_8569_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_8568_;
            }
            14 => {
                if v_isShared_8574_ == 0 {
                    v___x_8576_ = v___x_8573_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_8577_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8577_, 0, v_a_8571_);
                    v___x_8576_ = v_reuseFailAlloc_8577_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_8576_;
            }
            16 => {
                if v_isShared_8585_ == 0 {
                    v___x_8587_ = v___x_8584_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_8588_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8588_, 0, v_a_8582_);
                    v___x_8587_ = v_reuseFailAlloc_8588_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_8587_;
            }
            18 => {
                if v_isShared_8594_ == 0 {
                    v___x_8596_ = v___x_8593_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_8597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8597_, 0, v_a_8591_);
                    v___x_8596_ = v_reuseFailAlloc_8597_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_8596_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed(
    mut v_stx_8599_: *mut leanh::LeanObject,
    mut v___x_8600_: *mut leanh::LeanObject,
    mut v___x_8601_: *mut leanh::LeanObject,
    mut v_userName_x3f_8602_: *mut leanh::LeanObject,
    mut v___y_8603_: *mut leanh::LeanObject,
    mut v___y_8604_: *mut leanh::LeanObject,
    mut v___y_8605_: *mut leanh::LeanObject,
    mut v___y_8606_: *mut leanh::LeanObject,
    mut v___y_8607_: *mut leanh::LeanObject,
    mut v___y_8608_: *mut leanh::LeanObject,
    mut v___y_8609_: *mut leanh::LeanObject,
    mut v___y_8610_: *mut leanh::LeanObject,
    mut v___y_8611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1473__boxed_8612_: u8 = 0;
    let mut v_res_8613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1473__boxed_8612_ = (leanh::lean_unbox(v___x_8601_) as u8);
    v_res_8613_ = l_Lean_Elab_Tactic_elabAsFVar___lam__0(
        v_stx_8599_,
        v___x_8600_,
        v___x_1473__boxed_8612_,
        v_userName_x3f_8602_,
        v___y_8603_,
        v___y_8604_,
        v___y_8605_,
        v___y_8606_,
        v___y_8607_,
        v___y_8608_,
        v___y_8609_,
        v___y_8610_,
    );
    leanh::lean_dec(v___y_8606_);
    leanh::lean_dec_ref(v___y_8605_);
    leanh::lean_dec(v___y_8604_);
    leanh::lean_dec_ref(v___y_8603_);
    return v_res_8613_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabAsFVar(
    mut v_stx_8614_: *mut leanh::LeanObject,
    mut v_userName_x3f_8615_: *mut leanh::LeanObject,
    mut v_a_8616_: *mut leanh::LeanObject,
    mut v_a_8617_: *mut leanh::LeanObject,
    mut v_a_8618_: *mut leanh::LeanObject,
    mut v_a_8619_: *mut leanh::LeanObject,
    mut v_a_8620_: *mut leanh::LeanObject,
    mut v_a_8621_: *mut leanh::LeanObject,
    mut v_a_8622_: *mut leanh::LeanObject,
    mut v_a_8623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8626_: u8 = 0;
    let mut v___x_8627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8625_ = leanh::lean_box(0);
    v___x_8626_ = 0;
    v___x_8627_ = leanh::lean_box((v___x_8626_) as usize);
    v___f_8628_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed as *mut core::ffi::c_void,
        13,
        4,
    );
    leanh::lean_closure_set(v___f_8628_, 0, v_stx_8614_);
    leanh::lean_closure_set(v___f_8628_, 1, v___x_8625_);
    leanh::lean_closure_set(v___f_8628_, 2, v___x_8627_);
    leanh::lean_closure_set(v___f_8628_, 3, v_userName_x3f_8615_);
    v___x_8629_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_8628_,
        v_a_8616_,
        v_a_8617_,
        v_a_8618_,
        v_a_8619_,
        v_a_8620_,
        v_a_8621_,
        v_a_8622_,
        v_a_8623_,
    );
    return v___x_8629_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabAsFVar___boxed(
    mut v_stx_8630_: *mut leanh::LeanObject,
    mut v_userName_x3f_8631_: *mut leanh::LeanObject,
    mut v_a_8632_: *mut leanh::LeanObject,
    mut v_a_8633_: *mut leanh::LeanObject,
    mut v_a_8634_: *mut leanh::LeanObject,
    mut v_a_8635_: *mut leanh::LeanObject,
    mut v_a_8636_: *mut leanh::LeanObject,
    mut v_a_8637_: *mut leanh::LeanObject,
    mut v_a_8638_: *mut leanh::LeanObject,
    mut v_a_8639_: *mut leanh::LeanObject,
    mut v_a_8640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8641_ = l_Lean_Elab_Tactic_elabAsFVar(
        v_stx_8630_,
        v_userName_x3f_8631_,
        v_a_8632_,
        v_a_8633_,
        v_a_8634_,
        v_a_8635_,
        v_a_8636_,
        v_a_8637_,
        v_a_8638_,
        v_a_8639_,
    );
    leanh::lean_dec(v_a_8639_);
    leanh::lean_dec_ref(v_a_8638_);
    leanh::lean_dec(v_a_8637_);
    leanh::lean_dec_ref(v_a_8636_);
    leanh::lean_dec(v_a_8635_);
    leanh::lean_dec_ref(v_a_8634_);
    leanh::lean_dec(v_a_8633_);
    leanh::lean_dec_ref(v_a_8632_);
    return v_res_8641_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(
    mut v_k_8642_: *mut leanh::LeanObject,
    mut v___y_8643_: *mut leanh::LeanObject,
    mut v___y_8644_: *mut leanh::LeanObject,
    mut v___y_8645_: *mut leanh::LeanObject,
    mut v___y_8646_: *mut leanh::LeanObject,
    mut v___y_8647_: *mut leanh::LeanObject,
    mut v___y_8648_: *mut leanh::LeanObject,
    mut v___y_8649_: *mut leanh::LeanObject,
    mut v___y_8650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8652_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_8646_);
    leanh::lean_inc_ref(v___y_8645_);
    leanh::lean_inc(v___y_8644_);
    leanh::lean_inc_ref(v___y_8643_);
    v___x_8652_ = leanh::lean_apply_9(
        v_k_8642_,
        v___y_8643_,
        v___y_8644_,
        v___y_8645_,
        v___y_8646_,
        v___y_8647_,
        v___y_8648_,
        v___y_8649_,
        v___y_8650_,
        leanh::lean_box(0),
    );
    return v___x_8652_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed(
    mut v_k_8653_: *mut leanh::LeanObject,
    mut v___y_8654_: *mut leanh::LeanObject,
    mut v___y_8655_: *mut leanh::LeanObject,
    mut v___y_8656_: *mut leanh::LeanObject,
    mut v___y_8657_: *mut leanh::LeanObject,
    mut v___y_8658_: *mut leanh::LeanObject,
    mut v___y_8659_: *mut leanh::LeanObject,
    mut v___y_8660_: *mut leanh::LeanObject,
    mut v___y_8661_: *mut leanh::LeanObject,
    mut v___y_8662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8663_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(
            v_k_8653_,
            v___y_8654_,
            v___y_8655_,
            v___y_8656_,
            v___y_8657_,
            v___y_8658_,
            v___y_8659_,
            v___y_8660_,
            v___y_8661_,
        );
    leanh::lean_dec(v___y_8657_);
    leanh::lean_dec_ref(v___y_8656_);
    leanh::lean_dec(v___y_8655_);
    leanh::lean_dec_ref(v___y_8654_);
    return v_res_8663_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(
    mut v_k_8664_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_8665_: u8,
    mut v___y_8666_: *mut leanh::LeanObject,
    mut v___y_8667_: *mut leanh::LeanObject,
    mut v___y_8668_: *mut leanh::LeanObject,
    mut v___y_8669_: *mut leanh::LeanObject,
    mut v___y_8670_: *mut leanh::LeanObject,
    mut v___y_8671_: *mut leanh::LeanObject,
    mut v___y_8672_: *mut leanh::LeanObject,
    mut v___y_8673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8680_: u8 = 0;
    let mut v___x_8682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8684_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_8669_);
                leanh::lean_inc_ref(v___y_8668_);
                leanh::lean_inc(v___y_8667_);
                leanh::lean_inc_ref(v___y_8666_);
                v___f_8675_ = leanh::lean_alloc_closure(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                leanh::lean_closure_set(v___f_8675_, 0, v_k_8664_);
                leanh::lean_closure_set(v___f_8675_, 1, v___y_8666_);
                leanh::lean_closure_set(v___f_8675_, 2, v___y_8667_);
                leanh::lean_closure_set(v___f_8675_, 3, v___y_8668_);
                leanh::lean_closure_set(v___f_8675_, 4, v___y_8669_);
                v___x_8676_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    leanh::lean_box(0),
                    v_allowLevelAssignments_8665_,
                    v___f_8675_,
                    v___y_8670_,
                    v___y_8671_,
                    v___y_8672_,
                    v___y_8673_,
                );
                if leanh::lean_obj_tag(v___x_8676_) == 0 {
                    return v___x_8676_;
                } else {
                    v_a_8677_ = leanh::lean_ctor_get(v___x_8676_, 0);
                    v_isSharedCheck_8684_ = (!leanh::lean_is_exclusive(v___x_8676_)) as u8;
                    if v_isSharedCheck_8684_ == 0 {
                        v___x_8679_ = v___x_8676_;
                        v_isShared_8680_ = v_isSharedCheck_8684_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8677_);
                        leanh::lean_dec(v___x_8676_);
                        v___x_8679_ = leanh::lean_box(0);
                        v_isShared_8680_ = v_isSharedCheck_8684_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8680_ == 0 {
                    v___x_8682_ = v___x_8679_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8683_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8683_, 0, v_a_8677_);
                    v___x_8682_ = v_reuseFailAlloc_8683_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8682_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___boxed(
    mut v_k_8685_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_8686_: *mut leanh::LeanObject,
    mut v___y_8687_: *mut leanh::LeanObject,
    mut v___y_8688_: *mut leanh::LeanObject,
    mut v___y_8689_: *mut leanh::LeanObject,
    mut v___y_8690_: *mut leanh::LeanObject,
    mut v___y_8691_: *mut leanh::LeanObject,
    mut v___y_8692_: *mut leanh::LeanObject,
    mut v___y_8693_: *mut leanh::LeanObject,
    mut v___y_8694_: *mut leanh::LeanObject,
    mut v___y_8695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_8696_: u8 = 0;
    let mut v_res_8697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_8696_ =
        (leanh::lean_unbox(v_allowLevelAssignments_8686_) as u8);
    v_res_8697_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(
            v_k_8685_,
            v_allowLevelAssignments_boxed_8696_,
            v___y_8687_,
            v___y_8688_,
            v___y_8689_,
            v___y_8690_,
            v___y_8691_,
            v___y_8692_,
            v___y_8693_,
            v___y_8694_,
        );
    leanh::lean_dec(v___y_8694_);
    leanh::lean_dec_ref(v___y_8693_);
    leanh::lean_dec(v___y_8692_);
    leanh::lean_dec_ref(v___y_8691_);
    leanh::lean_dec(v___y_8690_);
    leanh::lean_dec_ref(v___y_8689_);
    leanh::lean_dec(v___y_8688_);
    leanh::lean_dec_ref(v___y_8687_);
    return v_res_8697_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(
    mut v_00_u03b1_8698_: *mut leanh::LeanObject,
    mut v_k_8699_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_8700_: u8,
    mut v___y_8701_: *mut leanh::LeanObject,
    mut v___y_8702_: *mut leanh::LeanObject,
    mut v___y_8703_: *mut leanh::LeanObject,
    mut v___y_8704_: *mut leanh::LeanObject,
    mut v___y_8705_: *mut leanh::LeanObject,
    mut v___y_8706_: *mut leanh::LeanObject,
    mut v___y_8707_: *mut leanh::LeanObject,
    mut v___y_8708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8710_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(
            v_k_8699_,
            v_allowLevelAssignments_8700_,
            v___y_8701_,
            v___y_8702_,
            v___y_8703_,
            v___y_8704_,
            v___y_8705_,
            v___y_8706_,
            v___y_8707_,
            v___y_8708_,
        );
    return v___x_8710_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed(
    mut v_00_u03b1_8711_: *mut leanh::LeanObject,
    mut v_k_8712_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_8713_: *mut leanh::LeanObject,
    mut v___y_8714_: *mut leanh::LeanObject,
    mut v___y_8715_: *mut leanh::LeanObject,
    mut v___y_8716_: *mut leanh::LeanObject,
    mut v___y_8717_: *mut leanh::LeanObject,
    mut v___y_8718_: *mut leanh::LeanObject,
    mut v___y_8719_: *mut leanh::LeanObject,
    mut v___y_8720_: *mut leanh::LeanObject,
    mut v___y_8721_: *mut leanh::LeanObject,
    mut v___y_8722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_8723_: u8 = 0;
    let mut v_res_8724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_8723_ =
        (leanh::lean_unbox(v_allowLevelAssignments_8713_) as u8);
    v_res_8724_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(
        v_00_u03b1_8711_,
        v_k_8712_,
        v_allowLevelAssignments_boxed_8723_,
        v___y_8714_,
        v___y_8715_,
        v___y_8716_,
        v___y_8717_,
        v___y_8718_,
        v___y_8719_,
        v___y_8720_,
        v___y_8721_,
    );
    leanh::lean_dec(v___y_8721_);
    leanh::lean_dec_ref(v___y_8720_);
    leanh::lean_dec(v___y_8719_);
    leanh::lean_dec_ref(v___y_8718_);
    leanh::lean_dec(v___y_8717_);
    leanh::lean_dec_ref(v___y_8716_);
    leanh::lean_dec(v___y_8715_);
    leanh::lean_dec_ref(v___y_8714_);
    return v_res_8724_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(
    mut v_a_8725_: *mut leanh::LeanObject,
    mut v___y_8726_: *mut leanh::LeanObject,
    mut v___y_8727_: *mut leanh::LeanObject,
    mut v___y_8728_: *mut leanh::LeanObject,
    mut v___y_8729_: *mut leanh::LeanObject,
    mut v___y_8730_: *mut leanh::LeanObject,
    mut v___y_8731_: *mut leanh::LeanObject,
    mut v___y_8732_: *mut leanh::LeanObject,
    mut v_a_x3f_8733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8735_: u8 = 0;
    let mut v___x_8736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8735_ = 0;
    v___x_8736_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
        v_a_8725_,
        v___x_8735_,
        v___y_8726_,
        v___y_8727_,
        v___y_8728_,
        v___y_8729_,
        v___y_8730_,
        v___y_8731_,
        v___y_8732_,
    );
    return v___x_8736_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0___boxed(
    mut v_a_8737_: *mut leanh::LeanObject,
    mut v___y_8738_: *mut leanh::LeanObject,
    mut v___y_8739_: *mut leanh::LeanObject,
    mut v___y_8740_: *mut leanh::LeanObject,
    mut v___y_8741_: *mut leanh::LeanObject,
    mut v___y_8742_: *mut leanh::LeanObject,
    mut v___y_8743_: *mut leanh::LeanObject,
    mut v___y_8744_: *mut leanh::LeanObject,
    mut v_a_x3f_8745_: *mut leanh::LeanObject,
    mut v___y_8746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8747_ =
        l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(
            v_a_8737_,
            v___y_8738_,
            v___y_8739_,
            v___y_8740_,
            v___y_8741_,
            v___y_8742_,
            v___y_8743_,
            v___y_8744_,
            v_a_x3f_8745_,
        );
    leanh::lean_dec(v_a_x3f_8745_);
    leanh::lean_dec(v___y_8744_);
    leanh::lean_dec_ref(v___y_8743_);
    leanh::lean_dec(v___y_8742_);
    leanh::lean_dec_ref(v___y_8741_);
    leanh::lean_dec(v___y_8740_);
    leanh::lean_dec_ref(v___y_8739_);
    leanh::lean_dec(v___y_8738_);
    return v_res_8747_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(
    mut v_x_8748_: *mut leanh::LeanObject,
    mut v___y_8749_: *mut leanh::LeanObject,
    mut v___y_8750_: *mut leanh::LeanObject,
    mut v___y_8751_: *mut leanh::LeanObject,
    mut v___y_8752_: *mut leanh::LeanObject,
    mut v___y_8753_: *mut leanh::LeanObject,
    mut v___y_8754_: *mut leanh::LeanObject,
    mut v___y_8755_: *mut leanh::LeanObject,
    mut v___y_8756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8764_: u8 = 0;
    let mut v___x_8766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8770_: u8 = 0;
    let mut v___x_8772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8774_: u8 = 0;
    let mut v_unused_8775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8779_: u8 = 0;
    let mut v___x_8781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8783_: u8 = 0;
    let mut v_reuseFailAlloc_8784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8785_: u8 = 0;
    let mut v_a_8786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8791_: u8 = 0;
    let mut v___x_8793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8795_: u8 = 0;
    let mut v_unused_8796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8800_: u8 = 0;
    let mut v___x_8802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8804_: u8 = 0;
    let mut v_a_8805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8808_: u8 = 0;
    let mut v___x_8810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8812_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8758_ = l_Lean_Elab_Tactic_saveState___redArg(
                    v___y_8750_,
                    v___y_8752_,
                    v___y_8754_,
                    v___y_8756_,
                );
                if leanh::lean_obj_tag(v___x_8758_) == 0 {
                    v_a_8759_ = leanh::lean_ctor_get(v___x_8758_, 0);
                    leanh::lean_inc(v_a_8759_);
                    leanh::lean_dec_ref_known(v___x_8758_, 1);
                    leanh::lean_inc(v___y_8756_);
                    leanh::lean_inc_ref(v___y_8755_);
                    leanh::lean_inc(v___y_8754_);
                    leanh::lean_inc_ref(v___y_8753_);
                    leanh::lean_inc(v___y_8752_);
                    leanh::lean_inc_ref(v___y_8751_);
                    leanh::lean_inc(v___y_8750_);
                    leanh::lean_inc_ref(v___y_8749_);
                    v_r_8760_ = leanh::lean_apply_9(
                        v_x_8748_,
                        v___y_8749_,
                        v___y_8750_,
                        v___y_8751_,
                        v___y_8752_,
                        v___y_8753_,
                        v___y_8754_,
                        v___y_8755_,
                        v___y_8756_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v_r_8760_) == 0 {
                        v_a_8761_ = leanh::lean_ctor_get(v_r_8760_, 0);
                        v_isSharedCheck_8785_ = (!leanh::lean_is_exclusive(v_r_8760_)) as u8;
                        if v_isSharedCheck_8785_ == 0 {
                            v___x_8763_ = v_r_8760_;
                            v_isShared_8764_ = v_isSharedCheck_8785_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8761_);
                            leanh::lean_dec(v_r_8760_);
                            v___x_8763_ = leanh::lean_box(0);
                            v_isShared_8764_ = v_isSharedCheck_8785_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_8786_ = leanh::lean_ctor_get(v_r_8760_, 0);
                        leanh::lean_inc(v_a_8786_);
                        leanh::lean_dec_ref_known(v_r_8760_, 1);
                        v___x_8787_ = leanh::lean_box(0);
                        v___x_8788_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_8759_, v___y_8750_, v___y_8751_, v___y_8752_, v___y_8753_, v___y_8754_, v___y_8755_, v___y_8756_, v___x_8787_);
                        if leanh::lean_obj_tag(v___x_8788_) == 0 {
                            v_isSharedCheck_8795_ =
                                (!leanh::lean_is_exclusive(v___x_8788_)) as u8;
                            if v_isSharedCheck_8795_ == 0 {
                                v_unused_8796_ = leanh::lean_ctor_get(v___x_8788_, 0);
                                leanh::lean_dec(v_unused_8796_);
                                v___x_8790_ = v___x_8788_;
                                v_isShared_8791_ = v_isSharedCheck_8795_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_8788_);
                                v___x_8790_ = leanh::lean_box(0);
                                v_isShared_8791_ = v_isSharedCheck_8795_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_8786_);
                            v_a_8797_ = leanh::lean_ctor_get(v___x_8788_, 0);
                            v_isSharedCheck_8804_ =
                                (!leanh::lean_is_exclusive(v___x_8788_)) as u8;
                            if v_isSharedCheck_8804_ == 0 {
                                v___x_8799_ = v___x_8788_;
                                v_isShared_8800_ = v_isSharedCheck_8804_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8797_);
                                leanh::lean_dec(v___x_8788_);
                                v___x_8799_ = leanh::lean_box(0);
                                v_isShared_8800_ = v_isSharedCheck_8804_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_8748_);
                    v_a_8805_ = leanh::lean_ctor_get(v___x_8758_, 0);
                    v_isSharedCheck_8812_ = (!leanh::lean_is_exclusive(v___x_8758_)) as u8;
                    if v_isSharedCheck_8812_ == 0 {
                        v___x_8807_ = v___x_8758_;
                        v_isShared_8808_ = v_isSharedCheck_8812_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8805_);
                        leanh::lean_dec(v___x_8758_);
                        v___x_8807_ = leanh::lean_box(0);
                        v_isShared_8808_ = v_isSharedCheck_8812_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_8761_);
                if v_isShared_8764_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_8763_, 1);
                    v___x_8766_ = v___x_8763_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8784_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8784_, 0, v_a_8761_);
                    v___x_8766_ = v_reuseFailAlloc_8784_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8767_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_8759_, v___y_8750_, v___y_8751_, v___y_8752_, v___y_8753_, v___y_8754_, v___y_8755_, v___y_8756_, v___x_8766_);
                leanh::lean_dec_ref(v___x_8766_);
                if leanh::lean_obj_tag(v___x_8767_) == 0 {
                    v_isSharedCheck_8774_ = (!leanh::lean_is_exclusive(v___x_8767_)) as u8;
                    if v_isSharedCheck_8774_ == 0 {
                        v_unused_8775_ = leanh::lean_ctor_get(v___x_8767_, 0);
                        leanh::lean_dec(v_unused_8775_);
                        v___x_8769_ = v___x_8767_;
                        v_isShared_8770_ = v_isSharedCheck_8774_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_8767_);
                        v___x_8769_ = leanh::lean_box(0);
                        v_isShared_8770_ = v_isSharedCheck_8774_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_8761_);
                    v_a_8776_ = leanh::lean_ctor_get(v___x_8767_, 0);
                    v_isSharedCheck_8783_ = (!leanh::lean_is_exclusive(v___x_8767_)) as u8;
                    if v_isSharedCheck_8783_ == 0 {
                        v___x_8778_ = v___x_8767_;
                        v_isShared_8779_ = v_isSharedCheck_8783_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8776_);
                        leanh::lean_dec(v___x_8767_);
                        v___x_8778_ = leanh::lean_box(0);
                        v_isShared_8779_ = v_isSharedCheck_8783_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_8770_ == 0 {
                    leanh::lean_ctor_set(v___x_8769_, 0, v_a_8761_);
                    v___x_8772_ = v___x_8769_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8773_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8773_, 0, v_a_8761_);
                    v___x_8772_ = v_reuseFailAlloc_8773_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8772_;
            }
            5 => {
                if v_isShared_8779_ == 0 {
                    v___x_8781_ = v___x_8778_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8782_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8782_, 0, v_a_8776_);
                    v___x_8781_ = v_reuseFailAlloc_8782_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8781_;
            }
            7 => {
                if v_isShared_8791_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_8790_, 1);
                    leanh::lean_ctor_set(v___x_8790_, 0, v_a_8786_);
                    v___x_8793_ = v___x_8790_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8794_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8794_, 0, v_a_8786_);
                    v___x_8793_ = v_reuseFailAlloc_8794_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8793_;
            }
            9 => {
                if v_isShared_8800_ == 0 {
                    v___x_8802_ = v___x_8799_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8803_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8803_, 0, v_a_8797_);
                    v___x_8802_ = v_reuseFailAlloc_8803_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8802_;
            }
            11 => {
                if v_isShared_8808_ == 0 {
                    v___x_8810_ = v___x_8807_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_8811_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8811_, 0, v_a_8805_);
                    v___x_8810_ = v_reuseFailAlloc_8811_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_8810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___boxed(
    mut v_x_8813_: *mut leanh::LeanObject,
    mut v___y_8814_: *mut leanh::LeanObject,
    mut v___y_8815_: *mut leanh::LeanObject,
    mut v___y_8816_: *mut leanh::LeanObject,
    mut v___y_8817_: *mut leanh::LeanObject,
    mut v___y_8818_: *mut leanh::LeanObject,
    mut v___y_8819_: *mut leanh::LeanObject,
    mut v___y_8820_: *mut leanh::LeanObject,
    mut v___y_8821_: *mut leanh::LeanObject,
    mut v___y_8822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8823_ =
        l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(
            v_x_8813_,
            v___y_8814_,
            v___y_8815_,
            v___y_8816_,
            v___y_8817_,
            v___y_8818_,
            v___y_8819_,
            v___y_8820_,
            v___y_8821_,
        );
    leanh::lean_dec(v___y_8821_);
    leanh::lean_dec_ref(v___y_8820_);
    leanh::lean_dec(v___y_8819_);
    leanh::lean_dec_ref(v___y_8818_);
    leanh::lean_dec(v___y_8817_);
    leanh::lean_dec_ref(v___y_8816_);
    leanh::lean_dec(v___y_8815_);
    leanh::lean_dec_ref(v___y_8814_);
    return v_res_8823_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(
    mut v_00_u03b1_8824_: *mut leanh::LeanObject,
    mut v_x_8825_: *mut leanh::LeanObject,
    mut v___y_8826_: *mut leanh::LeanObject,
    mut v___y_8827_: *mut leanh::LeanObject,
    mut v___y_8828_: *mut leanh::LeanObject,
    mut v___y_8829_: *mut leanh::LeanObject,
    mut v___y_8830_: *mut leanh::LeanObject,
    mut v___y_8831_: *mut leanh::LeanObject,
    mut v___y_8832_: *mut leanh::LeanObject,
    mut v___y_8833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8835_ =
        l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(
            v_x_8825_,
            v___y_8826_,
            v___y_8827_,
            v___y_8828_,
            v___y_8829_,
            v___y_8830_,
            v___y_8831_,
            v___y_8832_,
            v___y_8833_,
        );
    return v___x_8835_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___boxed(
    mut v_00_u03b1_8836_: *mut leanh::LeanObject,
    mut v_x_8837_: *mut leanh::LeanObject,
    mut v___y_8838_: *mut leanh::LeanObject,
    mut v___y_8839_: *mut leanh::LeanObject,
    mut v___y_8840_: *mut leanh::LeanObject,
    mut v___y_8841_: *mut leanh::LeanObject,
    mut v___y_8842_: *mut leanh::LeanObject,
    mut v___y_8843_: *mut leanh::LeanObject,
    mut v___y_8844_: *mut leanh::LeanObject,
    mut v___y_8845_: *mut leanh::LeanObject,
    mut v___y_8846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8847_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(
        v_00_u03b1_8836_,
        v_x_8837_,
        v___y_8838_,
        v___y_8839_,
        v___y_8840_,
        v___y_8841_,
        v___y_8842_,
        v___y_8843_,
        v___y_8844_,
        v___y_8845_,
    );
    leanh::lean_dec(v___y_8845_);
    leanh::lean_dec_ref(v___y_8844_);
    leanh::lean_dec(v___y_8843_);
    leanh::lean_dec_ref(v___y_8842_);
    leanh::lean_dec(v___y_8841_);
    leanh::lean_dec_ref(v___y_8840_);
    leanh::lean_dec(v___y_8839_);
    leanh::lean_dec_ref(v___y_8838_);
    return v_res_8847_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(
    mut v_a_8848_: *mut leanh::LeanObject,
    mut v___x_8849_: u8,
    mut v_as_8850_: *mut leanh::LeanObject,
    mut v_i_8851_: *mut leanh::LeanObject,
    mut v___y_8852_: *mut leanh::LeanObject,
    mut v___y_8853_: *mut leanh::LeanObject,
    mut v___y_8854_: *mut leanh::LeanObject,
    mut v___y_8855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_8857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_8858_: u8 = 0;
    let mut v___x_8859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_8861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_8862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8868_: u8 = 0;
    let mut v___x_8869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8874_: u8 = 0;
    let mut v___x_8875_: u8 = 0;
    let mut v___x_8877_: u8 = 0;
    let mut v___x_8879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8887_: u8 = 0;
    let mut v_a_8888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8891_: u8 = 0;
    let mut v___x_8893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8895_: u8 = 0;
    let mut v_isSharedCheck_8896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_8857_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_8858_ = lean_nat_dec_eq(v_i_8851_, v_zero_8857_);
                if v_isZero_8858_ == 1 {
                    leanh::lean_dec(v_i_8851_);
                    leanh::lean_dec_ref(v_a_8848_);
                    v___x_8859_ = leanh::lean_box(0);
                    v___x_8860_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8860_, 0, v___x_8859_);
                    return v___x_8860_;
                } else {
                    v_one_8861_ = leanh::lean_unsigned_to_nat(1);
                    v_n_8862_ = lean_nat_sub(v_i_8851_, v_one_8861_);
                    leanh::lean_dec(v_i_8851_);
                    v___x_8863_ = lean_array_fget(v_as_8850_, v_n_8862_);
                    if leanh::lean_obj_tag(v___x_8863_) == 0 {
                        v_i_8851_ = v_n_8862_;
                        state = 0;
                        continue;
                    } else {
                        v_val_8865_ = leanh::lean_ctor_get(v___x_8863_, 0);
                        v_isSharedCheck_8896_ =
                            (!leanh::lean_is_exclusive(v___x_8863_)) as u8;
                        if v_isSharedCheck_8896_ == 0 {
                            v___x_8867_ = v___x_8863_;
                            v_isShared_8868_ = v_isSharedCheck_8896_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_8865_);
                            leanh::lean_dec(v___x_8863_);
                            v___x_8867_ = leanh::lean_box(0);
                            v_isShared_8868_ = v_isSharedCheck_8896_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_8869_ = l_Lean_LocalDecl_type(v_val_8865_);
                leanh::lean_inc_ref(v_a_8848_);
                v___x_8870_ = l_Lean_Meta_isExprDefEq(
                    v_a_8848_,
                    v___x_8869_,
                    v___y_8852_,
                    v___y_8853_,
                    v___y_8854_,
                    v___y_8855_,
                );
                if leanh::lean_obj_tag(v___x_8870_) == 0 {
                    v_a_8871_ = leanh::lean_ctor_get(v___x_8870_, 0);
                    v_isSharedCheck_8887_ = (!leanh::lean_is_exclusive(v___x_8870_)) as u8;
                    if v_isSharedCheck_8887_ == 0 {
                        v___x_8873_ = v___x_8870_;
                        v_isShared_8874_ = v_isSharedCheck_8887_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8871_);
                        leanh::lean_dec(v___x_8870_);
                        v___x_8873_ = leanh::lean_box(0);
                        v_isShared_8874_ = v_isSharedCheck_8887_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_8867_);
                    leanh::lean_dec(v_val_8865_);
                    leanh::lean_dec(v_n_8862_);
                    leanh::lean_dec_ref(v_a_8848_);
                    v_a_8888_ = leanh::lean_ctor_get(v___x_8870_, 0);
                    v_isSharedCheck_8895_ = (!leanh::lean_is_exclusive(v___x_8870_)) as u8;
                    if v_isSharedCheck_8895_ == 0 {
                        v___x_8890_ = v___x_8870_;
                        v_isShared_8891_ = v_isSharedCheck_8895_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8888_);
                        leanh::lean_dec(v___x_8870_);
                        v___x_8890_ = leanh::lean_box(0);
                        v_isShared_8891_ = v_isSharedCheck_8895_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8875_ = l_Lean_LocalDecl_isImplementationDetail(v_val_8865_);
                if v___x_8875_ == 0 {
                    if v___x_8849_ == 0 {
                        leanh::lean_del_object(v___x_8873_);
                        leanh::lean_dec(v_a_8871_);
                        leanh::lean_del_object(v___x_8867_);
                        leanh::lean_dec(v_val_8865_);
                        v_i_8851_ = v_n_8862_;
                        state = 0;
                        continue;
                    } else {
                        v___x_8877_ = (leanh::lean_unbox(v_a_8871_) as u8);
                        leanh::lean_dec(v_a_8871_);
                        if v___x_8877_ == 0 {
                            leanh::lean_del_object(v___x_8873_);
                            leanh::lean_del_object(v___x_8867_);
                            leanh::lean_dec(v_val_8865_);
                            v_i_8851_ = v_n_8862_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_n_8862_);
                            leanh::lean_dec_ref(v_a_8848_);
                            v___x_8879_ = l_Lean_LocalDecl_fvarId(v_val_8865_);
                            leanh::lean_dec(v_val_8865_);
                            if v_isShared_8868_ == 0 {
                                leanh::lean_ctor_set(v___x_8867_, 0, v___x_8879_);
                                v___x_8881_ = v___x_8867_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_8885_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_8885_, 0, v___x_8879_);
                                v___x_8881_ = v_reuseFailAlloc_8885_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_8873_);
                    leanh::lean_dec(v_a_8871_);
                    leanh::lean_del_object(v___x_8867_);
                    leanh::lean_dec(v_val_8865_);
                    v_i_8851_ = v_n_8862_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                if v_isShared_8874_ == 0 {
                    leanh::lean_ctor_set(v___x_8873_, 0, v___x_8881_);
                    v___x_8883_ = v___x_8873_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8884_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8884_, 0, v___x_8881_);
                    v___x_8883_ = v_reuseFailAlloc_8884_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8883_;
            }
            5 => {
                if v_isShared_8891_ == 0 {
                    v___x_8893_ = v___x_8890_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8894_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8894_, 0, v_a_8888_);
                    v___x_8893_ = v_reuseFailAlloc_8894_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_a_8897_: *mut leanh::LeanObject,
    mut v___x_8898_: *mut leanh::LeanObject,
    mut v_as_8899_: *mut leanh::LeanObject,
    mut v_i_8900_: *mut leanh::LeanObject,
    mut v___y_8901_: *mut leanh::LeanObject,
    mut v___y_8902_: *mut leanh::LeanObject,
    mut v___y_8903_: *mut leanh::LeanObject,
    mut v___y_8904_: *mut leanh::LeanObject,
    mut v___y_8905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7239__boxed_8906_: u8 = 0;
    let mut v_res_8907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7239__boxed_8906_ = (leanh::lean_unbox(v___x_8898_) as u8);
    v_res_8907_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_8897_, v___x_7239__boxed_8906_, v_as_8899_, v_i_8900_, v___y_8901_, v___y_8902_, v___y_8903_, v___y_8904_);
    leanh::lean_dec(v___y_8904_);
    leanh::lean_dec_ref(v___y_8903_);
    leanh::lean_dec(v___y_8902_);
    leanh::lean_dec_ref(v___y_8901_);
    leanh::lean_dec_ref(v_as_8899_);
    return v_res_8907_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(
    mut v_a_8908_: *mut leanh::LeanObject,
    mut v___x_8909_: u8,
    mut v_as_8910_: *mut leanh::LeanObject,
    mut v_i_8911_: *mut leanh::LeanObject,
    mut v___y_8912_: *mut leanh::LeanObject,
    mut v___y_8913_: *mut leanh::LeanObject,
    mut v___y_8914_: *mut leanh::LeanObject,
    mut v___y_8915_: *mut leanh::LeanObject,
    mut v___y_8916_: *mut leanh::LeanObject,
    mut v___y_8917_: *mut leanh::LeanObject,
    mut v___y_8918_: *mut leanh::LeanObject,
    mut v___y_8919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_8921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_8922_: u8 = 0;
    let mut v___x_8923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_8925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_8926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_8921_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_8922_ = lean_nat_dec_eq(v_i_8911_, v_zero_8921_);
                if v_isZero_8922_ == 1 {
                    leanh::lean_dec(v_i_8911_);
                    leanh::lean_dec_ref(v_a_8908_);
                    v___x_8923_ = leanh::lean_box(0);
                    v___x_8924_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8924_, 0, v___x_8923_);
                    return v___x_8924_;
                } else {
                    v_one_8925_ = leanh::lean_unsigned_to_nat(1);
                    v_n_8926_ = lean_nat_sub(v_i_8911_, v_one_8925_);
                    leanh::lean_dec(v_i_8911_);
                    v___x_8927_ = lean_array_fget_borrowed(v_as_8910_, v_n_8926_);
                    leanh::lean_inc_ref(v_a_8908_);
                    v___x_8928_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_8908_, v___x_8909_, v___x_8927_, v___y_8912_, v___y_8913_, v___y_8914_, v___y_8915_, v___y_8916_, v___y_8917_, v___y_8918_, v___y_8919_);
                    if leanh::lean_obj_tag(v___x_8928_) == 0 {
                        v_a_8929_ = leanh::lean_ctor_get(v___x_8928_, 0);
                        leanh::lean_inc(v_a_8929_);
                        if leanh::lean_obj_tag(v_a_8929_) == 0 {
                            leanh::lean_dec_ref_known(v___x_8928_, 1);
                            v_i_8911_ = v_n_8926_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_a_8929_, 1);
                            leanh::lean_dec(v_n_8926_);
                            leanh::lean_dec_ref(v_a_8908_);
                            return v___x_8928_;
                        }
                    } else {
                        leanh::lean_dec(v_n_8926_);
                        leanh::lean_dec_ref(v_a_8908_);
                        return v___x_8928_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(
    mut v_a_8931_: *mut leanh::LeanObject,
    mut v___x_8932_: u8,
    mut v_x_8933_: *mut leanh::LeanObject,
    mut v___y_8934_: *mut leanh::LeanObject,
    mut v___y_8935_: *mut leanh::LeanObject,
    mut v___y_8936_: *mut leanh::LeanObject,
    mut v___y_8937_: *mut leanh::LeanObject,
    mut v___y_8938_: *mut leanh::LeanObject,
    mut v___y_8939_: *mut leanh::LeanObject,
    mut v___y_8940_: *mut leanh::LeanObject,
    mut v___y_8941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_8933_) == 0 {
        let mut v_cs_8943_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8944_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8945_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_cs_8943_ = leanh::lean_ctor_get(v_x_8933_, 0);
        v___x_8944_ = lean_array_get_size(v_cs_8943_);
        v___x_8945_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_8931_, v___x_8932_, v_cs_8943_, v___x_8944_, v___y_8934_, v___y_8935_, v___y_8936_, v___y_8937_, v___y_8938_, v___y_8939_, v___y_8940_, v___y_8941_);
        return v___x_8945_;
    } else {
        let mut v_vs_8946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8947_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8948_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_vs_8946_ = leanh::lean_ctor_get(v_x_8933_, 0);
        v___x_8947_ = lean_array_get_size(v_vs_8946_);
        v___x_8948_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_8931_, v___x_8932_, v_vs_8946_, v___x_8947_, v___y_8938_, v___y_8939_, v___y_8940_, v___y_8941_);
        return v___x_8948_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4___boxed(
    mut v_a_8949_: *mut leanh::LeanObject,
    mut v___x_8950_: *mut leanh::LeanObject,
    mut v_x_8951_: *mut leanh::LeanObject,
    mut v___y_8952_: *mut leanh::LeanObject,
    mut v___y_8953_: *mut leanh::LeanObject,
    mut v___y_8954_: *mut leanh::LeanObject,
    mut v___y_8955_: *mut leanh::LeanObject,
    mut v___y_8956_: *mut leanh::LeanObject,
    mut v___y_8957_: *mut leanh::LeanObject,
    mut v___y_8958_: *mut leanh::LeanObject,
    mut v___y_8959_: *mut leanh::LeanObject,
    mut v___y_8960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7334__boxed_8961_: u8 = 0;
    let mut v_res_8962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7334__boxed_8961_ = (leanh::lean_unbox(v___x_8950_) as u8);
    v_res_8962_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_8949_, v___x_7334__boxed_8961_, v_x_8951_, v___y_8952_, v___y_8953_, v___y_8954_, v___y_8955_, v___y_8956_, v___y_8957_, v___y_8958_, v___y_8959_);
    leanh::lean_dec(v___y_8959_);
    leanh::lean_dec_ref(v___y_8958_);
    leanh::lean_dec(v___y_8957_);
    leanh::lean_dec_ref(v___y_8956_);
    leanh::lean_dec(v___y_8955_);
    leanh::lean_dec_ref(v___y_8954_);
    leanh::lean_dec(v___y_8953_);
    leanh::lean_dec_ref(v___y_8952_);
    leanh::lean_dec_ref(v_x_8951_);
    return v_res_8962_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg___boxed(
    mut v_a_8963_: *mut leanh::LeanObject,
    mut v___x_8964_: *mut leanh::LeanObject,
    mut v_as_8965_: *mut leanh::LeanObject,
    mut v_i_8966_: *mut leanh::LeanObject,
    mut v___y_8967_: *mut leanh::LeanObject,
    mut v___y_8968_: *mut leanh::LeanObject,
    mut v___y_8969_: *mut leanh::LeanObject,
    mut v___y_8970_: *mut leanh::LeanObject,
    mut v___y_8971_: *mut leanh::LeanObject,
    mut v___y_8972_: *mut leanh::LeanObject,
    mut v___y_8973_: *mut leanh::LeanObject,
    mut v___y_8974_: *mut leanh::LeanObject,
    mut v___y_8975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7352__boxed_8976_: u8 = 0;
    let mut v_res_8977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7352__boxed_8976_ = (leanh::lean_unbox(v___x_8964_) as u8);
    v_res_8977_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_8963_, v___x_7352__boxed_8976_, v_as_8965_, v_i_8966_, v___y_8967_, v___y_8968_, v___y_8969_, v___y_8970_, v___y_8971_, v___y_8972_, v___y_8973_, v___y_8974_);
    leanh::lean_dec(v___y_8974_);
    leanh::lean_dec_ref(v___y_8973_);
    leanh::lean_dec(v___y_8972_);
    leanh::lean_dec_ref(v___y_8971_);
    leanh::lean_dec(v___y_8970_);
    leanh::lean_dec_ref(v___y_8969_);
    leanh::lean_dec(v___y_8968_);
    leanh::lean_dec_ref(v___y_8967_);
    leanh::lean_dec_ref(v_as_8965_);
    return v_res_8977_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(
    mut v_a_8978_: *mut leanh::LeanObject,
    mut v___x_8979_: u8,
    mut v_t_8980_: *mut leanh::LeanObject,
    mut v___y_8981_: *mut leanh::LeanObject,
    mut v___y_8982_: *mut leanh::LeanObject,
    mut v___y_8983_: *mut leanh::LeanObject,
    mut v___y_8984_: *mut leanh::LeanObject,
    mut v___y_8985_: *mut leanh::LeanObject,
    mut v___y_8986_: *mut leanh::LeanObject,
    mut v___y_8987_: *mut leanh::LeanObject,
    mut v___y_8988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_8990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_8990_ = leanh::lean_ctor_get(v_t_8980_, 0);
    v_tail_8991_ = leanh::lean_ctor_get(v_t_8980_, 1);
    v___x_8992_ = lean_array_get_size(v_tail_8991_);
    leanh::lean_inc_ref(v_a_8978_);
    v___x_8993_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_8978_, v___x_8979_, v_tail_8991_, v___x_8992_, v___y_8985_, v___y_8986_, v___y_8987_, v___y_8988_);
    if leanh::lean_obj_tag(v___x_8993_) == 0 {
        let mut v_a_8994_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_8994_ = leanh::lean_ctor_get(v___x_8993_, 0);
        leanh::lean_inc(v_a_8994_);
        if leanh::lean_obj_tag(v_a_8994_) == 0 {
            let mut v___x_8995_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_8993_, 1);
            v___x_8995_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_8978_, v___x_8979_, v_root_8990_, v___y_8981_, v___y_8982_, v___y_8983_, v___y_8984_, v___y_8985_, v___y_8986_, v___y_8987_, v___y_8988_);
            return v___x_8995_;
        } else {
            leanh::lean_dec_ref_known(v_a_8994_, 1);
            leanh::lean_dec_ref(v_a_8978_);
            return v___x_8993_;
        }
    } else {
        leanh::lean_dec_ref(v_a_8978_);
        return v___x_8993_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0___boxed(
    mut v_a_8996_: *mut leanh::LeanObject,
    mut v___x_8997_: *mut leanh::LeanObject,
    mut v_t_8998_: *mut leanh::LeanObject,
    mut v___y_8999_: *mut leanh::LeanObject,
    mut v___y_9000_: *mut leanh::LeanObject,
    mut v___y_9001_: *mut leanh::LeanObject,
    mut v___y_9002_: *mut leanh::LeanObject,
    mut v___y_9003_: *mut leanh::LeanObject,
    mut v___y_9004_: *mut leanh::LeanObject,
    mut v___y_9005_: *mut leanh::LeanObject,
    mut v___y_9006_: *mut leanh::LeanObject,
    mut v___y_9007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7431__boxed_9008_: u8 = 0;
    let mut v_res_9009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7431__boxed_9008_ = (leanh::lean_unbox(v___x_8997_) as u8);
    v_res_9009_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(v_a_8996_, v___x_7431__boxed_9008_, v_t_8998_, v___y_8999_, v___y_9000_, v___y_9001_, v___y_9002_, v___y_9003_, v___y_9004_, v___y_9005_, v___y_9006_);
    leanh::lean_dec(v___y_9006_);
    leanh::lean_dec_ref(v___y_9005_);
    leanh::lean_dec(v___y_9004_);
    leanh::lean_dec_ref(v___y_9003_);
    leanh::lean_dec(v___y_9002_);
    leanh::lean_dec_ref(v___y_9001_);
    leanh::lean_dec(v___y_9000_);
    leanh::lean_dec_ref(v___y_8999_);
    leanh::lean_dec_ref(v_t_8998_);
    return v_res_9009_;
}
pub unsafe fn l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(
    mut v_a_9010_: *mut leanh::LeanObject,
    mut v___x_9011_: u8,
    mut v_lctx_9012_: *mut leanh::LeanObject,
    mut v___y_9013_: *mut leanh::LeanObject,
    mut v___y_9014_: *mut leanh::LeanObject,
    mut v___y_9015_: *mut leanh::LeanObject,
    mut v___y_9016_: *mut leanh::LeanObject,
    mut v___y_9017_: *mut leanh::LeanObject,
    mut v___y_9018_: *mut leanh::LeanObject,
    mut v___y_9019_: *mut leanh::LeanObject,
    mut v___y_9020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decls_9022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_decls_9022_ = leanh::lean_ctor_get(v_lctx_9012_, 1);
    v___x_9023_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(v_a_9010_, v___x_9011_, v_decls_9022_, v___y_9013_, v___y_9014_, v___y_9015_, v___y_9016_, v___y_9017_, v___y_9018_, v___y_9019_, v___y_9020_);
    return v___x_9023_;
}
pub unsafe fn l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0___boxed(
    mut v_a_9024_: *mut leanh::LeanObject,
    mut v___x_9025_: *mut leanh::LeanObject,
    mut v_lctx_9026_: *mut leanh::LeanObject,
    mut v___y_9027_: *mut leanh::LeanObject,
    mut v___y_9028_: *mut leanh::LeanObject,
    mut v___y_9029_: *mut leanh::LeanObject,
    mut v___y_9030_: *mut leanh::LeanObject,
    mut v___y_9031_: *mut leanh::LeanObject,
    mut v___y_9032_: *mut leanh::LeanObject,
    mut v___y_9033_: *mut leanh::LeanObject,
    mut v___y_9034_: *mut leanh::LeanObject,
    mut v___y_9035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7474__boxed_9036_: u8 = 0;
    let mut v_res_9037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7474__boxed_9036_ = (leanh::lean_unbox(v___x_9025_) as u8);
    v_res_9037_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(
        v_a_9024_,
        v___x_7474__boxed_9036_,
        v_lctx_9026_,
        v___y_9027_,
        v___y_9028_,
        v___y_9029_,
        v___y_9030_,
        v___y_9031_,
        v___y_9032_,
        v___y_9033_,
        v___y_9034_,
    );
    leanh::lean_dec(v___y_9034_);
    leanh::lean_dec_ref(v___y_9033_);
    leanh::lean_dec(v___y_9032_);
    leanh::lean_dec_ref(v___y_9031_);
    leanh::lean_dec(v___y_9030_);
    leanh::lean_dec_ref(v___y_9029_);
    leanh::lean_dec(v___y_9028_);
    leanh::lean_dec_ref(v___y_9027_);
    leanh::lean_dec_ref(v_lctx_9026_);
    return v_res_9037_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_9039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9039_ = l_Lean_Elab_Tactic_evalRename___lam__0___closed__0;
    v___x_9040_ = l_Lean_stringToMessageData(v___x_9039_);
    return v___x_9040_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRename___lam__0(
    mut v___x_9041_: *mut leanh::LeanObject,
    mut v___x_9042_: *mut leanh::LeanObject,
    mut v___x_9043_: u8,
    mut v___y_9044_: *mut leanh::LeanObject,
    mut v___y_9045_: *mut leanh::LeanObject,
    mut v___y_9046_: *mut leanh::LeanObject,
    mut v___y_9047_: *mut leanh::LeanObject,
    mut v___y_9048_: *mut leanh::LeanObject,
    mut v___y_9049_: *mut leanh::LeanObject,
    mut v___y_9050_: *mut leanh::LeanObject,
    mut v___y_9051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_9055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9060_: u8 = 0;
    let mut v___x_9061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_9065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9069_: u8 = 0;
    let mut v_a_9070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9073_: u8 = 0;
    let mut v___x_9075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9077_: u8 = 0;
    let mut v_a_9078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9081_: u8 = 0;
    let mut v___x_9083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9053_ = l_Lean_Elab_Tactic_elabTerm(
                    v___x_9041_,
                    v___x_9042_,
                    v___x_9043_,
                    v___y_9044_,
                    v___y_9045_,
                    v___y_9046_,
                    v___y_9047_,
                    v___y_9048_,
                    v___y_9049_,
                    v___y_9050_,
                    v___y_9051_,
                );
                if leanh::lean_obj_tag(v___x_9053_) == 0 {
                    v_a_9054_ = leanh::lean_ctor_get(v___x_9053_, 0);
                    leanh::lean_inc_n(v_a_9054_, 2);
                    leanh::lean_dec_ref_known(v___x_9053_, 1);
                    v_lctx_9055_ = leanh::lean_ctor_get(v___y_9048_, 2);
                    v___x_9056_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(v_a_9054_, v___x_9043_, v_lctx_9055_, v___y_9044_, v___y_9045_, v___y_9046_, v___y_9047_, v___y_9048_, v___y_9049_, v___y_9050_, v___y_9051_);
                    if leanh::lean_obj_tag(v___x_9056_) == 0 {
                        v_a_9057_ = leanh::lean_ctor_get(v___x_9056_, 0);
                        v_isSharedCheck_9069_ =
                            (!leanh::lean_is_exclusive(v___x_9056_)) as u8;
                        if v_isSharedCheck_9069_ == 0 {
                            v___x_9059_ = v___x_9056_;
                            v_isShared_9060_ = v_isSharedCheck_9069_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9057_);
                            leanh::lean_dec(v___x_9056_);
                            v___x_9059_ = leanh::lean_box(0);
                            v_isShared_9060_ = v_isSharedCheck_9069_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_9054_);
                        v_a_9070_ = leanh::lean_ctor_get(v___x_9056_, 0);
                        v_isSharedCheck_9077_ =
                            (!leanh::lean_is_exclusive(v___x_9056_)) as u8;
                        if v_isSharedCheck_9077_ == 0 {
                            v___x_9072_ = v___x_9056_;
                            v_isShared_9073_ = v_isSharedCheck_9077_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9070_);
                            leanh::lean_dec(v___x_9056_);
                            v___x_9072_ = leanh::lean_box(0);
                            v_isShared_9073_ = v_isSharedCheck_9077_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_9078_ = leanh::lean_ctor_get(v___x_9053_, 0);
                    v_isSharedCheck_9085_ = (!leanh::lean_is_exclusive(v___x_9053_)) as u8;
                    if v_isSharedCheck_9085_ == 0 {
                        v___x_9080_ = v___x_9053_;
                        v_isShared_9081_ = v_isSharedCheck_9085_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9078_);
                        leanh::lean_dec(v___x_9053_);
                        v___x_9080_ = leanh::lean_box(0);
                        v_isShared_9081_ = v_isSharedCheck_9085_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_9057_) == 0 {
                    leanh::lean_del_object(v___x_9059_);
                    v___x_9061_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalRename___lam__0___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_evalRename___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1,
                    );
                    v___x_9062_ = l_Lean_indentExpr(v_a_9054_);
                    v___x_9063_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_9063_, 0, v___x_9061_);
                    leanh::lean_ctor_set(v___x_9063_, 1, v___x_9062_);
                    v___x_9064_ =
                        l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(
                            v___x_9063_,
                            v___y_9048_,
                            v___y_9049_,
                            v___y_9050_,
                            v___y_9051_,
                        );
                    return v___x_9064_;
                } else {
                    leanh::lean_dec(v_a_9054_);
                    v_val_9065_ = leanh::lean_ctor_get(v_a_9057_, 0);
                    leanh::lean_inc(v_val_9065_);
                    leanh::lean_dec_ref_known(v_a_9057_, 1);
                    if v_isShared_9060_ == 0 {
                        leanh::lean_ctor_set(v___x_9059_, 0, v_val_9065_);
                        v___x_9067_ = v___x_9059_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9068_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_9068_, 0, v_val_9065_);
                        v___x_9067_ = v_reuseFailAlloc_9068_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_9067_;
            }
            3 => {
                if v_isShared_9073_ == 0 {
                    v___x_9075_ = v___x_9072_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9076_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9076_, 0, v_a_9070_);
                    v___x_9075_ = v_reuseFailAlloc_9076_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9075_;
            }
            5 => {
                if v_isShared_9081_ == 0 {
                    v___x_9083_ = v___x_9080_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_9084_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9084_, 0, v_a_9078_);
                    v___x_9083_ = v_reuseFailAlloc_9084_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_9083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalRename___lam__0___boxed(
    mut v___x_9086_: *mut leanh::LeanObject,
    mut v___x_9087_: *mut leanh::LeanObject,
    mut v___x_9088_: *mut leanh::LeanObject,
    mut v___y_9089_: *mut leanh::LeanObject,
    mut v___y_9090_: *mut leanh::LeanObject,
    mut v___y_9091_: *mut leanh::LeanObject,
    mut v___y_9092_: *mut leanh::LeanObject,
    mut v___y_9093_: *mut leanh::LeanObject,
    mut v___y_9094_: *mut leanh::LeanObject,
    mut v___y_9095_: *mut leanh::LeanObject,
    mut v___y_9096_: *mut leanh::LeanObject,
    mut v___y_9097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7516__boxed_9098_: u8 = 0;
    let mut v_res_9099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7516__boxed_9098_ = (leanh::lean_unbox(v___x_9088_) as u8);
    v_res_9099_ = l_Lean_Elab_Tactic_evalRename___lam__0(
        v___x_9086_,
        v___x_9087_,
        v___x_7516__boxed_9098_,
        v___y_9089_,
        v___y_9090_,
        v___y_9091_,
        v___y_9092_,
        v___y_9093_,
        v___y_9094_,
        v___y_9095_,
        v___y_9096_,
    );
    leanh::lean_dec(v___y_9096_);
    leanh::lean_dec_ref(v___y_9095_);
    leanh::lean_dec(v___y_9094_);
    leanh::lean_dec_ref(v___y_9093_);
    leanh::lean_dec(v___y_9092_);
    leanh::lean_dec_ref(v___y_9091_);
    leanh::lean_dec(v___y_9090_);
    leanh::lean_dec_ref(v___y_9089_);
    return v_res_9099_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRename___lam__1(
    mut v___x_9100_: *mut leanh::LeanObject,
    mut v_h_9101_: *mut leanh::LeanObject,
    mut v___y_9102_: *mut leanh::LeanObject,
    mut v___y_9103_: *mut leanh::LeanObject,
    mut v___y_9104_: *mut leanh::LeanObject,
    mut v___y_9105_: *mut leanh::LeanObject,
    mut v___y_9106_: *mut leanh::LeanObject,
    mut v___y_9107_: *mut leanh::LeanObject,
    mut v___y_9108_: *mut leanh::LeanObject,
    mut v___y_9109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9124_: u8 = 0;
    let mut v___x_9126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9128_: u8 = 0;
    let mut v_a_9129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9132_: u8 = 0;
    let mut v___x_9134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9136_: u8 = 0;
    let mut v_a_9137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9140_: u8 = 0;
    let mut v___x_9142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9111_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v___x_9100_, v___y_9102_, v___y_9103_, v___y_9104_, v___y_9105_, v___y_9106_, v___y_9107_, v___y_9108_, v___y_9109_);
                if leanh::lean_obj_tag(v___x_9111_) == 0 {
                    v_a_9112_ = leanh::lean_ctor_get(v___x_9111_, 0);
                    leanh::lean_inc(v_a_9112_);
                    leanh::lean_dec_ref_known(v___x_9111_, 1);
                    v___x_9113_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v___y_9103_,
                        v___y_9106_,
                        v___y_9107_,
                        v___y_9108_,
                        v___y_9109_,
                    );
                    if leanh::lean_obj_tag(v___x_9113_) == 0 {
                        v_a_9114_ = leanh::lean_ctor_get(v___x_9113_, 0);
                        leanh::lean_inc(v_a_9114_);
                        leanh::lean_dec_ref_known(v___x_9113_, 1);
                        v___x_9115_ = l_Lean_TSyntax_getId(v_h_9101_);
                        v___x_9116_ = l_Lean_MVarId_rename(
                            v_a_9114_,
                            v_a_9112_,
                            v___x_9115_,
                            v___y_9106_,
                            v___y_9107_,
                            v___y_9108_,
                            v___y_9109_,
                        );
                        if leanh::lean_obj_tag(v___x_9116_) == 0 {
                            v_a_9117_ = leanh::lean_ctor_get(v___x_9116_, 0);
                            leanh::lean_inc(v_a_9117_);
                            leanh::lean_dec_ref_known(v___x_9116_, 1);
                            v___x_9118_ = leanh::lean_box(0);
                            v___x_9119_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_9119_, 0, v_a_9117_);
                            leanh::lean_ctor_set(v___x_9119_, 1, v___x_9118_);
                            v___x_9120_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v___x_9119_,
                                v___y_9103_,
                                v___y_9106_,
                                v___y_9107_,
                                v___y_9108_,
                                v___y_9109_,
                            );
                            return v___x_9120_;
                        } else {
                            v_a_9121_ = leanh::lean_ctor_get(v___x_9116_, 0);
                            v_isSharedCheck_9128_ =
                                (!leanh::lean_is_exclusive(v___x_9116_)) as u8;
                            if v_isSharedCheck_9128_ == 0 {
                                v___x_9123_ = v___x_9116_;
                                v_isShared_9124_ = v_isSharedCheck_9128_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_9121_);
                                leanh::lean_dec(v___x_9116_);
                                v___x_9123_ = leanh::lean_box(0);
                                v_isShared_9124_ = v_isSharedCheck_9128_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_9112_);
                        v_a_9129_ = leanh::lean_ctor_get(v___x_9113_, 0);
                        v_isSharedCheck_9136_ =
                            (!leanh::lean_is_exclusive(v___x_9113_)) as u8;
                        if v_isSharedCheck_9136_ == 0 {
                            v___x_9131_ = v___x_9113_;
                            v_isShared_9132_ = v_isSharedCheck_9136_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9129_);
                            leanh::lean_dec(v___x_9113_);
                            v___x_9131_ = leanh::lean_box(0);
                            v_isShared_9132_ = v_isSharedCheck_9136_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_9137_ = leanh::lean_ctor_get(v___x_9111_, 0);
                    v_isSharedCheck_9144_ = (!leanh::lean_is_exclusive(v___x_9111_)) as u8;
                    if v_isSharedCheck_9144_ == 0 {
                        v___x_9139_ = v___x_9111_;
                        v_isShared_9140_ = v_isSharedCheck_9144_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9137_);
                        leanh::lean_dec(v___x_9111_);
                        v___x_9139_ = leanh::lean_box(0);
                        v_isShared_9140_ = v_isSharedCheck_9144_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9124_ == 0 {
                    v___x_9126_ = v___x_9123_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9127_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9127_, 0, v_a_9121_);
                    v___x_9126_ = v_reuseFailAlloc_9127_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9126_;
            }
            3 => {
                if v_isShared_9132_ == 0 {
                    v___x_9134_ = v___x_9131_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9135_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9135_, 0, v_a_9129_);
                    v___x_9134_ = v_reuseFailAlloc_9135_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9134_;
            }
            5 => {
                if v_isShared_9140_ == 0 {
                    v___x_9142_ = v___x_9139_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_9143_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9143_, 0, v_a_9137_);
                    v___x_9142_ = v_reuseFailAlloc_9143_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_9142_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalRename___lam__1___boxed(
    mut v___x_9145_: *mut leanh::LeanObject,
    mut v_h_9146_: *mut leanh::LeanObject,
    mut v___y_9147_: *mut leanh::LeanObject,
    mut v___y_9148_: *mut leanh::LeanObject,
    mut v___y_9149_: *mut leanh::LeanObject,
    mut v___y_9150_: *mut leanh::LeanObject,
    mut v___y_9151_: *mut leanh::LeanObject,
    mut v___y_9152_: *mut leanh::LeanObject,
    mut v___y_9153_: *mut leanh::LeanObject,
    mut v___y_9154_: *mut leanh::LeanObject,
    mut v___y_9155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9156_ = l_Lean_Elab_Tactic_evalRename___lam__1(
        v___x_9145_,
        v_h_9146_,
        v___y_9147_,
        v___y_9148_,
        v___y_9149_,
        v___y_9150_,
        v___y_9151_,
        v___y_9152_,
        v___y_9153_,
        v___y_9154_,
    );
    leanh::lean_dec(v___y_9154_);
    leanh::lean_dec_ref(v___y_9153_);
    leanh::lean_dec(v___y_9152_);
    leanh::lean_dec_ref(v___y_9151_);
    leanh::lean_dec(v___y_9150_);
    leanh::lean_dec_ref(v___y_9149_);
    leanh::lean_dec(v___y_9148_);
    leanh::lean_dec_ref(v___y_9147_);
    leanh::lean_dec(v_h_9146_);
    return v_res_9156_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRename(
    mut v_stx_9166_: *mut leanh::LeanObject,
    mut v_a_9167_: *mut leanh::LeanObject,
    mut v_a_9168_: *mut leanh::LeanObject,
    mut v_a_9169_: *mut leanh::LeanObject,
    mut v_a_9170_: *mut leanh::LeanObject,
    mut v_a_9171_: *mut leanh::LeanObject,
    mut v_a_9172_: *mut leanh::LeanObject,
    mut v_a_9173_: *mut leanh::LeanObject,
    mut v_a_9174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9177_: u8 = 0;
    v___x_9176_ = l_Lean_Elab_Tactic_evalRename___closed__1;
    leanh::lean_inc(v_stx_9166_);
    v___x_9177_ = l_Lean_Syntax_isOfKind(v_stx_9166_, v___x_9176_);
    if v___x_9177_ == 0 {
        let mut v___x_9178_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_9166_);
        v___x_9178_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg(
            );
        return v___x_9178_;
    } else {
        let mut v___x_9179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_h_9180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_9181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_9182_: u8 = 0;
        v___x_9179_ = leanh::lean_unsigned_to_nat(3);
        v_h_9180_ = l_Lean_Syntax_getArg(v_stx_9166_, v___x_9179_);
        v___x_9181_ = l_Lean_Elab_Tactic_evalRename___closed__3;
        leanh::lean_inc(v_h_9180_);
        v___x_9182_ = l_Lean_Syntax_isOfKind(v_h_9180_, v___x_9181_);
        if v___x_9182_ == 0 {
            let mut v___x_9183_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h_9180_);
            leanh::lean_dec(v_stx_9166_);
            v___x_9183_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
            return v___x_9183_;
        } else {
            let mut v___x_9184_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9185_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9186_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9187_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_9188_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9189_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9190_: u8 = 0;
            let mut v___x_9191_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9192_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_9193_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_9194_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_9184_ = leanh::lean_unsigned_to_nat(1);
            v___x_9185_ = l_Lean_Syntax_getArg(v_stx_9166_, v___x_9184_);
            leanh::lean_dec(v_stx_9166_);
            v___x_9186_ = leanh::lean_box(0);
            v___x_9187_ = leanh::lean_box((v___x_9182_) as usize);
            v___f_9188_ = leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_evalRename___lam__0___boxed as *mut core::ffi::c_void,
                12,
                3,
            );
            leanh::lean_closure_set(v___f_9188_, 0, v___x_9185_);
            leanh::lean_closure_set(v___f_9188_, 1, v___x_9186_);
            leanh::lean_closure_set(v___f_9188_, 2, v___x_9187_);
            v___x_9189_ = leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_withoutRecover___boxed as *mut core::ffi::c_void,
                11,
                2,
            );
            leanh::lean_closure_set(v___x_9189_, 0, leanh::lean_box(0));
            leanh::lean_closure_set(v___x_9189_, 1, v___f_9188_);
            v___x_9190_ = 0;
            v___x_9191_ = leanh::lean_box((v___x_9190_) as usize);
            v___x_9192_ = leanh::lean_alloc_closure(
                l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed
                    as *mut core::ffi::c_void,
                12,
                3,
            );
            leanh::lean_closure_set(v___x_9192_, 0, leanh::lean_box(0));
            leanh::lean_closure_set(v___x_9192_, 1, v___x_9189_);
            leanh::lean_closure_set(v___x_9192_, 2, v___x_9191_);
            v___f_9193_ = leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_evalRename___lam__1___boxed as *mut core::ffi::c_void,
                11,
                2,
            );
            leanh::lean_closure_set(v___f_9193_, 0, v___x_9192_);
            leanh::lean_closure_set(v___f_9193_, 1, v_h_9180_);
            v___x_9194_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                v___f_9193_,
                v_a_9167_,
                v_a_9168_,
                v_a_9169_,
                v_a_9170_,
                v_a_9171_,
                v_a_9172_,
                v_a_9173_,
                v_a_9174_,
            );
            return v___x_9194_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalRename___boxed(
    mut v_stx_9195_: *mut leanh::LeanObject,
    mut v_a_9196_: *mut leanh::LeanObject,
    mut v_a_9197_: *mut leanh::LeanObject,
    mut v_a_9198_: *mut leanh::LeanObject,
    mut v_a_9199_: *mut leanh::LeanObject,
    mut v_a_9200_: *mut leanh::LeanObject,
    mut v_a_9201_: *mut leanh::LeanObject,
    mut v_a_9202_: *mut leanh::LeanObject,
    mut v_a_9203_: *mut leanh::LeanObject,
    mut v_a_9204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9205_ = l_Lean_Elab_Tactic_evalRename(
        v_stx_9195_,
        v_a_9196_,
        v_a_9197_,
        v_a_9198_,
        v_a_9199_,
        v_a_9200_,
        v_a_9201_,
        v_a_9202_,
        v_a_9203_,
    );
    leanh::lean_dec(v_a_9203_);
    leanh::lean_dec_ref(v_a_9202_);
    leanh::lean_dec(v_a_9201_);
    leanh::lean_dec_ref(v_a_9200_);
    leanh::lean_dec(v_a_9199_);
    leanh::lean_dec_ref(v_a_9198_);
    leanh::lean_dec(v_a_9197_);
    leanh::lean_dec_ref(v_a_9196_);
    return v_res_9205_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(
    mut v_a_9206_: *mut leanh::LeanObject,
    mut v___x_9207_: u8,
    mut v_as_9208_: *mut leanh::LeanObject,
    mut v_i_9209_: *mut leanh::LeanObject,
    mut v_a_9210_: *mut leanh::LeanObject,
    mut v___y_9211_: *mut leanh::LeanObject,
    mut v___y_9212_: *mut leanh::LeanObject,
    mut v___y_9213_: *mut leanh::LeanObject,
    mut v___y_9214_: *mut leanh::LeanObject,
    mut v___y_9215_: *mut leanh::LeanObject,
    mut v___y_9216_: *mut leanh::LeanObject,
    mut v___y_9217_: *mut leanh::LeanObject,
    mut v___y_9218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9220_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_9206_, v___x_9207_, v_as_9208_, v_i_9209_, v___y_9215_, v___y_9216_, v___y_9217_, v___y_9218_);
    return v___x_9220_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___boxed(
    mut v_a_9221_: *mut leanh::LeanObject,
    mut v___x_9222_: *mut leanh::LeanObject,
    mut v_as_9223_: *mut leanh::LeanObject,
    mut v_i_9224_: *mut leanh::LeanObject,
    mut v_a_9225_: *mut leanh::LeanObject,
    mut v___y_9226_: *mut leanh::LeanObject,
    mut v___y_9227_: *mut leanh::LeanObject,
    mut v___y_9228_: *mut leanh::LeanObject,
    mut v___y_9229_: *mut leanh::LeanObject,
    mut v___y_9230_: *mut leanh::LeanObject,
    mut v___y_9231_: *mut leanh::LeanObject,
    mut v___y_9232_: *mut leanh::LeanObject,
    mut v___y_9233_: *mut leanh::LeanObject,
    mut v___y_9234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7785__boxed_9235_: u8 = 0;
    let mut v_res_9236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7785__boxed_9235_ = (leanh::lean_unbox(v___x_9222_) as u8);
    v_res_9236_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(v_a_9221_, v___x_7785__boxed_9235_, v_as_9223_, v_i_9224_, v_a_9225_, v___y_9226_, v___y_9227_, v___y_9228_, v___y_9229_, v___y_9230_, v___y_9231_, v___y_9232_, v___y_9233_);
    leanh::lean_dec(v___y_9233_);
    leanh::lean_dec_ref(v___y_9232_);
    leanh::lean_dec(v___y_9231_);
    leanh::lean_dec_ref(v___y_9230_);
    leanh::lean_dec(v___y_9229_);
    leanh::lean_dec_ref(v___y_9228_);
    leanh::lean_dec(v___y_9227_);
    leanh::lean_dec_ref(v___y_9226_);
    leanh::lean_dec_ref(v_as_9223_);
    return v_res_9236_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(
    mut v_a_9237_: *mut leanh::LeanObject,
    mut v___x_9238_: u8,
    mut v_as_9239_: *mut leanh::LeanObject,
    mut v_i_9240_: *mut leanh::LeanObject,
    mut v_a_9241_: *mut leanh::LeanObject,
    mut v___y_9242_: *mut leanh::LeanObject,
    mut v___y_9243_: *mut leanh::LeanObject,
    mut v___y_9244_: *mut leanh::LeanObject,
    mut v___y_9245_: *mut leanh::LeanObject,
    mut v___y_9246_: *mut leanh::LeanObject,
    mut v___y_9247_: *mut leanh::LeanObject,
    mut v___y_9248_: *mut leanh::LeanObject,
    mut v___y_9249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9251_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_9237_, v___x_9238_, v_as_9239_, v_i_9240_, v___y_9242_, v___y_9243_, v___y_9244_, v___y_9245_, v___y_9246_, v___y_9247_, v___y_9248_, v___y_9249_);
    return v___x_9251_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___boxed(
    mut v_a_9252_: *mut leanh::LeanObject,
    mut v___x_9253_: *mut leanh::LeanObject,
    mut v_as_9254_: *mut leanh::LeanObject,
    mut v_i_9255_: *mut leanh::LeanObject,
    mut v_a_9256_: *mut leanh::LeanObject,
    mut v___y_9257_: *mut leanh::LeanObject,
    mut v___y_9258_: *mut leanh::LeanObject,
    mut v___y_9259_: *mut leanh::LeanObject,
    mut v___y_9260_: *mut leanh::LeanObject,
    mut v___y_9261_: *mut leanh::LeanObject,
    mut v___y_9262_: *mut leanh::LeanObject,
    mut v___y_9263_: *mut leanh::LeanObject,
    mut v___y_9264_: *mut leanh::LeanObject,
    mut v___y_9265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7823__boxed_9266_: u8 = 0;
    let mut v_res_9267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7823__boxed_9266_ = (leanh::lean_unbox(v___x_9253_) as u8);
    v_res_9267_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(v_a_9252_, v___x_7823__boxed_9266_, v_as_9254_, v_i_9255_, v_a_9256_, v___y_9257_, v___y_9258_, v___y_9259_, v___y_9260_, v___y_9261_, v___y_9262_, v___y_9263_, v___y_9264_);
    leanh::lean_dec(v___y_9264_);
    leanh::lean_dec_ref(v___y_9263_);
    leanh::lean_dec(v___y_9262_);
    leanh::lean_dec_ref(v___y_9261_);
    leanh::lean_dec(v___y_9260_);
    leanh::lean_dec_ref(v___y_9259_);
    leanh::lean_dec(v___y_9258_);
    leanh::lean_dec_ref(v___y_9257_);
    leanh::lean_dec_ref(v_as_9254_);
    return v_res_9267_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1()
-> *mut leanh::LeanObject {
    let mut v___x_9275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9275_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_9276_ = l_Lean_Elab_Tactic_evalRename___closed__1;
    v___x_9277_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1;
    v___x_9278_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalRename___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_9279_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_9275_,
        v___x_9276_,
        v___x_9277_,
        v___x_9278_,
    );
    return v___x_9279_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___boxed(
    mut v_a_9280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9281_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1();
    return v_res_9281_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_9308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9308_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1;
    v___x_9309_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6;
    v___x_9310_ = l_Lean_addBuiltinDeclarationRanges(v___x_9308_, v___x_9309_);
    return v___x_9310_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___boxed(
    mut v_a_9311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9312_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3();
    return v_res_9312_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_ElabTerm(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Constructor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rename(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_ElabTerm(
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
pub unsafe fn initialize_Lean_Elab_Tactic_ElabTerm(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Constructor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Replace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Rename(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_SyntheticMVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_ElabTerm(builtin);
}